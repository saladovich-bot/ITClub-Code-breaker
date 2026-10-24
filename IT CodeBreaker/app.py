"""
IT CodeBreaker — Kahoot-style quiz game for IT Club AAUP.

The server is the single source of truth: it runs every timer and decides
what each screen (host projector + player phones) shows. Clients only render
the "state" they receive, so a refreshed phone or a reconnect always lands
back in the right place.
"""
import json
import os
import random
import secrets
import socket
import threading
import time

from flask import Flask, render_template, request, session, redirect, url_for
from flask_socketio import SocketIO, emit
from werkzeug.middleware.proxy_fix import ProxyFix

# ── Game rules (tweak freely) ─────────────────────────────────
START_SCORE = 100        # everyone starts with this many points
WRONG_PENALTY = 20       # lost for a wrong answer OR no answer
POINTS_PER_SECOND = 2    # correct answer = seconds left × this
STREAK_BONUS = 0         # extra points per streak step: with 5 → 2nd correct in a row +5, 3rd +10 ... (0 = off)
DEFAULT_TIME = 30        # seconds per question when the quiz doesn't say otherwise
READ_TIME = 5            # seconds the question is shown alone before answers open
COUNTDOWN = 3            # "3-2-1" before the first question
MAX_NAME_LEN = 16
GAME_TTL = 6 * 3600      # abandoned games are forgotten after this many seconds
DEFAULT_QUIZ = 'it_basics'  # quizzes/<name>.json selected when a new game opens

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
QUIZ_DIR = os.path.join(BASE_DIR, 'quizzes')

app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'codebreaker-dev-key-change-me')
app.wsgi_app = ProxyFix(app.wsgi_app, x_proto=1, x_host=1)
socketio = SocketIO(app)

lock = threading.RLock()
games = {}     # pin -> Game
sid_map = {}   # socket id -> (pin, 'host' | 'player', player_id)


# ── Quizzes ───────────────────────────────────────────────────
def normalize_quiz(data, quiz_id):
    default_time = int(data.get('time', DEFAULT_TIME))
    questions = []
    for i, q in enumerate(data.get('questions', []), 1):
        qtype = q.get('type', 'choice')
        text = str(q.get('question', '')).strip()
        if not text:
            raise ValueError(f'question {i}: text is empty')
        if qtype == 'truefalse':
            if not isinstance(q.get('correct'), bool):
                raise ValueError(f'question {i}: "correct" must be true or false')
            options = ['True', 'False']
            correct = 0 if q['correct'] else 1
        elif qtype == 'choice':
            options = [str(o) for o in q.get('options', [])]
            if not 2 <= len(options) <= 4:
                raise ValueError(f'question {i}: needs 2 to 4 options')
            correct = q.get('correct')
            if isinstance(correct, bool) or not isinstance(correct, int) or not 0 <= correct < len(options):
                raise ValueError(f'question {i}: "correct" must be an option number from 0 to {len(options) - 1}')
        else:
            raise ValueError(f'question {i}: unknown type "{qtype}"')
        questions.append({
            'type': qtype,
            'question': text,
            'options': options,
            'correct': correct,
            'time': int(q.get('time', default_time)),
            'image': q.get('image'),
        })
    if not questions:
        raise ValueError('no questions')
    return {'id': quiz_id, 'title': data.get('title', quiz_id), 'questions': questions}


def load_quizzes():
    """Read every quizzes/*.json file. Re-read each time, so edits apply without a restart."""
    quizzes, errors = {}, []
    if not os.path.isdir(QUIZ_DIR):
        return quizzes, ['The quizzes/ folder is missing.']
    for filename in sorted(os.listdir(QUIZ_DIR)):
        if not filename.endswith('.json'):
            continue
        quiz_id = filename[:-5]
        try:
            with open(os.path.join(QUIZ_DIR, filename), encoding='utf-8') as f:
                quizzes[quiz_id] = normalize_quiz(json.load(f), quiz_id)
        except Exception as e:  # show broken files on the host screen instead of crashing
            errors.append(f'{filename}: {e}')
    return quizzes, errors


SOUND_NAMES = ['lobby', 'question', 'heartbeat', 'podium_suspense', 'winner']
SOUND_EXTS = ('.mp3', '.wav', '.ogg', '.m4a')


def find_sounds():
    """Find each music file anywhere inside static/ (any subfolder, any letter case)."""
    static_dir = os.path.join(BASE_DIR, 'static')
    found = {}
    for root, _, files in os.walk(static_dir):
        for filename in sorted(files):
            stem, ext = os.path.splitext(filename)
            key = stem.lower().replace(' ', '_').replace('-', '_')
            if ext.lower() in SOUND_EXTS and key in SOUND_NAMES and key not in found:
                rel = os.path.relpath(os.path.join(root, filename), static_dir).replace(os.sep, '/')
                found[key] = url_for('static', filename=rel)
    return found


def image_url(path):
    if not path:
        return None
    if path.startswith(('http://', 'https://', '/')):
        return path
    return '/static/' + path


# ── Game objects ──────────────────────────────────────────────
class Player:
    def __init__(self, pid, name, order):
        self.pid = pid
        self.name = name
        self.order = order      # join order, used for avatar + tie-breaks
        self.sid = None         # current socket, None while disconnected
        self.reset()

    def reset(self):
        self.score = START_SCORE
        self.eliminated = False
        self.streak = 0
        self.answer = None          # option picked for the current question
        self.pending_points = 0     # points if that answer turns out correct
        self.last = None            # result of the last finished question


class Game:
    def __init__(self, pin):
        self.pin = pin
        self.host_token = secrets.token_urlsafe(16)
        self.host_sid = None
        self.players = {}
        self.join_counter = 0
        quizzes, _ = load_quizzes()
        self.quiz_id = DEFAULT_QUIZ if DEFAULT_QUIZ in quizzes else next(iter(quizzes), None)
        self.quiz = None
        self.phase = 'lobby'
        self.q_index = -1
        self.gen = 0                # bumps on every phase change; cancels stale timers
        self.phase_ends = None
        self.phase_len = None
        self.prev_ranks = {}
        self.distribution = []
        self.ended_early = False
        self.touched = time.time()

    @property
    def question(self):
        if self.quiz and 0 <= self.q_index < len(self.quiz['questions']):
            return self.quiz['questions'][self.q_index]
        return None

    @property
    def is_last(self):
        return self.quiz is not None and self.q_index >= len(self.quiz['questions']) - 1

    def ranking(self):
        return sorted(self.players.values(), key=lambda p: (-p.score, p.order))

    def active_connected(self):
        return [p for p in self.players.values() if not p.eliminated and p.sid]


# ── Phase machine ─────────────────────────────────────────────
# lobby → countdown → intro → answering → results → leaderboard → intro → ...
#                                               └→ (last question) final → podium
def set_phase(g, phase, duration=None):
    g.gen += 1
    g.phase = phase
    g.phase_len = duration
    g.phase_ends = time.time() + duration if duration else None
    g.touched = time.time()


def after(g, delay, fn):
    """Run fn(g) after delay seconds, unless the phase changed in the meantime."""
    gen = g.gen

    def run():
        socketio.sleep(delay)
        with lock:
            if games.get(g.pin) is g and g.gen == gen:
                fn(g)

    socketio.start_background_task(run)


def start_countdown(g):
    quizzes, _ = load_quizzes()
    g.quiz = quizzes.get(g.quiz_id) or next(iter(quizzes.values()), None)
    if not g.quiz:
        return
    for p in g.players.values():
        p.reset()
    g.q_index = -1
    g.prev_ranks = {}
    set_phase(g, 'countdown', COUNTDOWN)
    broadcast(g)
    after(g, COUNTDOWN, start_intro)


def start_intro(g):
    g.q_index += 1
    g.ended_early = False
    for p in g.players.values():
        p.answer = None
        p.pending_points = 0
        p.last = None
    set_phase(g, 'intro', READ_TIME)
    broadcast(g)
    after(g, READ_TIME, start_answering)


def start_answering(g):
    duration = g.question['time']
    set_phase(g, 'answering', duration)
    broadcast(g)
    after(g, duration, end_answering)


def end_answering(g):
    q = g.question
    g.prev_ranks = {p.pid: i + 1 for i, p in enumerate(g.ranking())}
    dist = [0] * len(q['options'])
    for p in g.players.values():
        if p.eliminated:
            continue
        if p.answer is not None:
            dist[p.answer] += 1
        if p.answer == q['correct']:
            p.streak += 1
            points = p.pending_points + STREAK_BONUS * (p.streak - 1)
            outcome = 'correct'
        else:
            p.streak = 0
            points = -WRONG_PENALTY
            outcome = 'timeout' if p.answer is None else 'wrong'
        p.score += points
        if p.score < 0:
            p.eliminated = True
        p.last = {'outcome': outcome, 'points': points, 'eliminated_now': p.eliminated}
    g.distribution = dist
    set_phase(g, 'results')
    broadcast(g)


def maybe_all_answered(g):
    if g.phase != 'answering':
        return
    active = g.active_connected()
    if active and all(p.answer is not None for p in active):
        g.ended_early = True
        end_answering(g)


def host_next(g):
    if g.phase == 'results':
        set_phase(g, 'final' if g.is_last else 'leaderboard')
        broadcast(g)
    elif g.phase == 'leaderboard':
        start_intro(g)
    elif g.phase == 'final':
        set_phase(g, 'podium')
        broadcast(g)


def host_skip(g):
    if g.phase == 'intro':
        start_answering(g)
    elif g.phase == 'answering':
        end_answering(g)


def back_to_lobby(g):
    for p in g.players.values():
        p.reset()
    g.q_index = -1
    g.quiz = None
    g.prev_ranks = {}
    set_phase(g, 'lobby')
    broadcast(g)


# ── What each screen gets ─────────────────────────────────────
def quiz_summary(q):
    return {'id': q['id'], 'title': q['title'], 'count': len(q['questions'])}


def base_view(g):
    return {
        'phase': g.phase,
        'server_now': time.time(),
        'ends_at': g.phase_ends,
        'duration': g.phase_len,
        'q_number': g.q_index + 1,
        'q_total': len(g.quiz['questions']) if g.quiz else 0,
    }


def host_view(g):
    v = base_view(g)
    v['pin'] = g.pin
    v['players'] = [
        {'pid': p.pid, 'name': p.name, 'order': p.order, 'connected': bool(p.sid),
         'score': p.score, 'eliminated': p.eliminated}
        for p in sorted(g.players.values(), key=lambda p: p.order)
    ]
    if g.phase == 'lobby':
        quizzes, errors = load_quizzes()
        v['quizzes'] = [quiz_summary(q) for q in quizzes.values()]
        v['quiz_id'] = g.quiz_id
        v['quiz_errors'] = errors
    q = g.question
    if q and g.phase in ('intro', 'answering', 'results'):
        v['question'] = {'text': q['question'], 'options': q['options'],
                         'type': q['type'], 'image': image_url(q['image'])}
    if g.phase == 'answering':
        active = [p for p in g.players.values() if not p.eliminated]
        v['answered'] = sum(1 for p in active if p.answer is not None)
        v['active'] = len(active)
    if g.phase == 'results':
        v['correct'] = q['correct']   # the answer reaches the projector only after time is up
        v['distribution'] = g.distribution
        v['ended_early'] = g.ended_early
        v['is_last'] = g.is_last
    if g.phase in ('leaderboard', 'final', 'podium'):
        v['leaderboard'] = [
            {'pid': p.pid, 'name': p.name, 'score': p.score, 'eliminated': p.eliminated,
             'rank': i + 1, 'prev_rank': g.prev_ranks.get(p.pid)}
            for i, p in enumerate(g.ranking())
        ]
    return v


def standing(g, p):
    ranking = g.ranking()
    idx = ranking.index(p)
    info = {'rank': idx + 1, 'total': len(ranking)}
    if idx > 0:
        above = ranking[idx - 1]
        info['ahead'] = {'name': above.name, 'gap': above.score - p.score}
    return info


def player_view(g, p):
    v = base_view(g)
    v.update(name=p.name, order=p.order, score=p.score, streak=p.streak,
             eliminated=p.eliminated, players_count=len(g.players))
    q = g.question
    if g.phase == 'answering' and q:
        v['options_count'] = len(q['options'])
        v['answered'] = p.answer is not None
        v['labels'] = q['options']
    if g.phase == 'results':
        v['result'] = p.last
        v['correct_index'] = q['correct']
        v['correct_text'] = q['options'][q['correct']]
    if g.phase in ('results', 'leaderboard', 'final', 'podium'):
        v['standing'] = standing(g, p)
    return v


def broadcast(g, host=True, players=True):
    if host and g.host_sid:
        socketio.emit('state', host_view(g), to=g.host_sid)
    if players:
        for p in g.players.values():
            if p.sid:
                socketio.emit('state', player_view(g, p), to=p.sid)


# ── Game lifecycle helpers ────────────────────────────────────
def create_game():
    while True:
        pin = str(random.randint(100000, 999999))
        if pin not in games:
            break
    g = Game(pin)
    games[pin] = g
    return g


def end_game(g, reason='The host ended this game.'):
    g.gen += 1
    for p in g.players.values():
        if p.sid:
            sid_map.pop(p.sid, None)
            socketio.emit('kicked', {'reason': reason}, to=p.sid)
    if g.host_sid:
        sid_map.pop(g.host_sid, None)
    games.pop(g.pin, None)


def cleanup_games():
    now = time.time()
    for g in list(games.values()):
        if not g.host_sid and now - g.touched > GAME_TTL:
            end_game(g, 'This game has expired.')


def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(('8.8.8.8', 80))   # no packets are sent; this just picks the Wi-Fi address
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return None


def public_base_url():
    """The address phones should open. On a laptop, swap localhost for the Wi-Fi IP."""
    if os.environ.get('PUBLIC_URL'):
        return os.environ['PUBLIC_URL'].rstrip('/')
    host = request.host
    hostname, _, port = host.partition(':')
    if hostname in ('localhost', '127.0.0.1', '0.0.0.0'):
        ip = lan_ip()
        if ip:
            host = ip + (':' + port if port else '')
    return f'{request.scheme}://{host}'


def current_player():
    with lock:
        g = games.get(session.get('pin', ''))
        p = g.players.get(session.get('pid')) if g else None
        return g, p


# ── Pages ─────────────────────────────────────────────────────
@app.route('/')
def home():
    _, p = current_player()
    return render_template('index.html', pin=request.args.get('pin', ''), name='',
                           error=request.args.get('error', ''), rejoin=p.name if p else None)


@app.route('/join', methods=['POST'])
def join():
    pin = request.form.get('pin', '').strip()
    name = ' '.join(request.form.get('username', '').split())[:MAX_NAME_LEN]
    with lock:
        g = games.get(pin)
        error = None
        if not g:
            error = 'Game not found — check the PIN.'
        elif not name:
            error = 'Enter your name.'
        elif g.phase != 'lobby':
            error = 'This game has already started.'
        elif any(p.name.lower() == name.lower() for p in g.players.values()):
            error = 'That name is taken — pick another one.'
        if error:
            return render_template('index.html', pin=pin, name=name, error=error, rejoin=None)
        g.join_counter += 1
        pid = secrets.token_urlsafe(9)
        g.players[pid] = Player(pid, name, g.join_counter)
        g.touched = time.time()
    session['pin'] = pin
    session['pid'] = pid
    return redirect(url_for('play'))


@app.route('/play')
def play():
    g, p = current_player()
    if not p:
        return redirect(url_for('home'))
    return render_template('play.html', cfg={'pin': g.pin, 'pid': p.pid})


@app.route('/host')
def host():
    with lock:
        cleanup_games()
        g = games.get(session.get('host_pin', ''))
        if g and g.host_token != session.get('host_token'):
            g = None
        if request.args.get('new'):
            if g:
                end_game(g)
            g = None
        if not g:
            g = create_game()
            session['host_pin'] = g.pin
            session['host_token'] = g.host_token
        if request.args.get('new'):
            return redirect(url_for('host'))
        sounds = find_sounds()
        cfg = {'pin': g.pin, 'token': g.host_token, 'join_base': public_base_url(),
               'sounds': sounds, 'missing_sounds': [s for s in SOUND_NAMES if s not in sounds]}
    return render_template('host.html', cfg=cfg)


# ── Socket events ─────────────────────────────────────────────
def from_host():
    entry = sid_map.get(request.sid)
    if not entry or entry[1] != 'host':
        return None
    return games.get(entry[0])


def from_player():
    entry = sid_map.get(request.sid)
    if not entry or entry[1] != 'player':
        return None, None
    g = games.get(entry[0])
    return (g, g.players.get(entry[2])) if g else (None, None)


@socketio.on('host_hello')
def on_host_hello(data):
    data = data or {}
    with lock:
        g = games.get(str(data.get('pin')))
        if not g or data.get('token') != g.host_token:
            emit('host_invalid')
            return
        if g.host_sid and g.host_sid != request.sid:
            sid_map.pop(g.host_sid, None)
        g.host_sid = request.sid
        g.touched = time.time()
        sid_map[request.sid] = (g.pin, 'host', None)
        emit('state', host_view(g))


@socketio.on('player_hello')
def on_player_hello(data):
    data = data or {}
    with lock:
        g = games.get(str(data.get('pin')))
        p = g.players.get(data.get('pid')) if g else None
        if not p:
            emit('kicked', {'reason': 'This game is no longer available.'})
            return
        if p.sid and p.sid != request.sid:
            sid_map.pop(p.sid, None)
            socketio.emit('kicked', {'reason': 'You opened the game in another tab.'}, to=p.sid)
        p.sid = request.sid
        sid_map[request.sid] = (g.pin, 'player', p.pid)
        emit('state', player_view(g, p))
        broadcast(g, players=(g.phase == 'lobby'))


@socketio.on('disconnect')
def on_disconnect(*_):
    with lock:
        entry = sid_map.pop(request.sid, None)
        if not entry:
            return
        g = games.get(entry[0])
        if not g:
            return
        if entry[1] == 'host':
            if g.host_sid == request.sid:
                g.host_sid = None
            return
        p = g.players.get(entry[2])
        if p and p.sid == request.sid:
            p.sid = None
            broadcast(g, players=False)
            maybe_all_answered(g)


@socketio.on('select_quiz')
def on_select_quiz(data):
    with lock:
        g = from_host()
        if not g or g.phase != 'lobby':
            return
        quizzes, _ = load_quizzes()
        if (data or {}).get('quiz_id') in quizzes:
            g.quiz_id = data['quiz_id']
            broadcast(g, players=False)


@socketio.on('start_game')
def on_start_game():
    with lock:
        g = from_host()
        if g and g.phase == 'lobby' and g.players:
            start_countdown(g)


@socketio.on('kick')
def on_kick(data):
    with lock:
        g = from_host()
        if not g or g.phase != 'lobby':
            return
        p = g.players.pop((data or {}).get('pid'), None)
        if p and p.sid:
            sid_map.pop(p.sid, None)
            socketio.emit('kicked', {'reason': 'The host removed you from the game.'}, to=p.sid)
        broadcast(g)


@socketio.on('host_next')
def on_host_next():
    with lock:
        g = from_host()
        if g:
            host_next(g)


@socketio.on('host_skip')
def on_host_skip():
    with lock:
        g = from_host()
        if g:
            host_skip(g)


@socketio.on('back_to_lobby')
def on_back_to_lobby():
    with lock:
        g = from_host()
        if g:
            back_to_lobby(g)


@socketio.on('answer')
def on_answer(data):
    with lock:
        g, p = from_player()
        if not g or not p or g.phase != 'answering' or p.eliminated or p.answer is not None:
            return
        choice = (data or {}).get('choice')
        if isinstance(choice, bool) or not isinstance(choice, int) \
                or not 0 <= choice < len(g.question['options']):
            return
        p.answer = choice
        remaining = max(0.0, g.phase_ends - time.time())
        p.pending_points = round(remaining * POINTS_PER_SECOND)
        emit('state', player_view(g, p))
        broadcast(g, players=False)
        maybe_all_answered(g)


if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5000))
    ip = lan_ip()
    print(f'\n  Host screen:  http://localhost:{port}/host')
    if ip:
        print(f'  Players join: http://{ip}:{port}  (same Wi-Fi)\n')
    socketio.run(app, host='0.0.0.0', port=port, allow_unsafe_werkzeug=True)
