# Driver of an evaluation in pieces (the piece files are written by runs/gen_shared.py).  It builds
# the pieces one after the other with `lake build`, keeps a record of each, and can be stopped and
# started again at any time: a piece that was not finished is evaluated again from its start.
#
# usage (from the folder of the Lean project, with `lake` on the PATH):
#
#   python runs/run_pieces.py TAG
#
#   for example, in the background:   nohup python runs/run_pieces.py k9s >> runs/k9s_run.out 2>&1 &
#
# Files, all in runs/ (TAG = k5s, k9s, ...):
#   TAG_pieces.txt    the module name, then the names of the pieces in order (from gen_shared.py)
#   TAG_threads.txt   one line, the number of threads; read before every piece.  It becomes the
#                     line  weakLeanArgs = ["-jN"]  of lakefile.toml, that is the size of the pool
#                     of threads of the `lean` process that evaluates the piece.
#   TAG_STOP          if this file exists, the driver stops before the next piece (the piece in
#                     progress is finished first).
#   TAG_done.txt      one line for every finished piece: name, threads, seconds, SHA-256 of the
#                     source, SHA-256 of the .olean, date.
#   TAG_pieces/NAME.out   the output of `lake build` for the piece
#   TAG_stale/        leftovers of pieces that were not finished, or whose record does not fit
#   TAG_lean.pid      the process ids of the `lean` processes of the piece in progress
#   TAG_driver.pid    the process id of this driver
#   TAG_top.out       the output of the build of the top module (with the axioms)
#
# A piece counts as built only if (1) it has a line in TAG_done.txt, (2) the hashes of its source
# and its .olean are the ones of that line, and (3) `lake build --no-build` finds it up to date.
# Otherwise its build files are moved to TAG_stale/ and it is evaluated again.
# The driver refuses to start while another driver of the same TAG runs, or while a `lean` process
# that an earlier driver started, or one that works on a file of this folder, is still alive.
# It ends with the line "== all done" (exit 0), "== stopped" (exit 0) or "== FAILED" (exit 1).
#
# Do not run another `lake` in this folder while the driver runs.
# The list of processes is taken from PowerShell under Windows and from `ps` elsewhere; the driver
# was used under Windows only.
import datetime, hashlib, io, os, re, shutil, subprocess, sys, time

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
RUNS = os.path.join(ROOT, "runs")
ENV = dict(os.environ)
ELAN = os.path.join(os.path.expanduser("~"), ".elan", "bin")
if os.path.isdir(ELAN):
    ENV["PATH"] = ELAN + os.pathsep + ENV.get("PATH", "")
ENV["LEAN_NUM_THREADS"] = "1"       # lake itself: one job at a time
LAKE = shutil.which("lake", path=ENV.get("PATH"))
MAX_THREADS = 32
SCRIPT = os.path.basename(__file__)


def now():
    return datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def say(text):
    print("%s  %s" % (now(), text), flush=True)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def processes():
    """All processes: list of (pid, parent pid, name, command line)."""
    if os.name == "nt":
        cmd = ("Get-CimInstance Win32_Process | ForEach-Object { "
               "'{0}|{1}|{2}|{3}' -f $_.ProcessId, $_.ParentProcessId, $_.Name, $_.CommandLine }")
        out = subprocess.run(["powershell", "-NoProfile", "-Command", cmd], capture_output=True,
                             text=True, errors="replace").stdout
        rows = [line.split("|", 3) for line in out.splitlines()]
    else:
        out = subprocess.run(["ps", "-eo", "pid=,ppid=,comm=,args="], capture_output=True,
                             text=True, errors="replace").stdout
        rows = [line.split(None, 3) for line in out.splitlines()]
    res = []
    for f in rows:
        if len(f) == 4 and f[0].strip().isdigit() and f[1].strip().isdigit():
            res.append((int(f[0]), int(f[1]), os.path.basename(f[2].strip()), f[3]))
    return res


def is_lean(name):
    return name.lower() in ("lean", "lean.exe")


def descendants(procs, root):
    kids = {}
    for pid, ppid, name, cl in procs:
        kids.setdefault(ppid, []).append((pid, name))
    res, todo, seen = [], [root], set()
    while todo:
        x = todo.pop()
        for pid, name in kids.get(x, []):
            if pid not in seen:
                seen.add(pid)
                res.append((pid, name))
                todo.append(pid)
    return res


def norm(text):
    return text.replace("\\", "/").lower()


def lean_alive(tag):
    """Process ids of `lean` processes that belong to this folder (see the head of this file)."""
    procs = processes()
    recorded = set()
    path = os.path.join(RUNS, tag + "_lean.pid")
    if os.path.exists(path):
        recorded = set(int(x) for x in io.open(path, encoding="ascii").read().split() if x.isdigit())
    here = norm(ROOT)
    found = []
    for pid, ppid, name, cl in procs:
        if not is_lean(name):
            continue
        if pid in recorded or here + "/" in norm(cl) + "/":
            found.append(pid)
    return found


def driver_alive(tag):
    path = os.path.join(RUNS, tag + "_driver.pid")
    if not os.path.exists(path):
        return None
    text = io.open(path, encoding="ascii").read().strip()
    if not text.isdigit():
        return None
    old = int(text)
    for pid, ppid, name, cl in processes():
        if pid == old and name.lower().startswith("python") and SCRIPT in cl:
            return old
    return None


def set_threads(tag):
    """Reads TAG_threads.txt and writes the number into lakefile.toml if it is not there yet."""
    if not os.path.exists(os.path.join(RUNS, tag + "_threads.txt")):
        raise SystemExit("== FAILED: write the number of threads into runs/%s_threads.txt first" % tag)
    text = io.open(os.path.join(RUNS, tag + "_threads.txt"), encoding="ascii").read().strip()
    if not text.isdigit() or not (1 <= int(text) <= MAX_THREADS):
        raise SystemExit("== FAILED: %s_threads.txt must hold one number from 1 to %d" % (tag, MAX_THREADS))
    n = int(text)
    path = os.path.join(ROOT, "lakefile.toml")
    s = io.open(path, encoding="utf-8").read()
    lines = re.findall(r'(?m)^weakLeanArgs = \["-j\d+"\]$', s)
    if len(lines) != 1:
        raise SystemExit('== FAILED: lakefile.toml must have exactly one line  weakLeanArgs = ["-jN"]')
    new = 'weakLeanArgs = ["-j%d"]' % n
    if lines[0] != new:
        io.open(path, "w", encoding="utf-8", newline="\n").write(s.replace(lines[0], new))
    return n


def files_of(mod, name):
    lib = os.path.join(ROOT, ".lake", "build", "lib", "lean", "Results", mod)
    ir = os.path.join(ROOT, ".lake", "build", "ir", "Results", mod)
    return ([os.path.join(lib, name + ext) for ext in
             (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace", ".olean.server",
              ".olean.private", ".olean.server.hash", ".olean.private.hash")]
            + [os.path.join(ir, name + ext) for ext in (".c", ".c.hash", ".setup.json")])


def source_of(mod, name):
    return os.path.join(ROOT, "Results", mod, name + ".lean")


def olean_of(mod, name):
    return os.path.join(ROOT, ".lake", "build", "lib", "lean", "Results", mod, name + ".olean")


def record_of(tag, name):
    path = os.path.join(RUNS, tag + "_done.txt")
    rec = None
    if os.path.exists(path):
        for line in io.open(path, encoding="ascii"):
            f = line.split()
            if len(f) >= 5 and f[0] == name:
                rec = f
    return rec


def is_built(tag, mod, name):
    rec = record_of(tag, name)
    if rec is None:
        return False, "no record"
    src, ole = source_of(mod, name), olean_of(mod, name)
    if not os.path.exists(ole):
        return False, "record, but no .olean"
    if sha256(src) != rec[3]:
        return False, "the source is not the one of the record"
    if sha256(ole) != rec[4]:
        return False, "the .olean is not the one of the record"
    r = subprocess.run([LAKE, "build", "--no-build", "Results.%s.%s" % (mod, name)], cwd=ROOT, env=ENV,
                       capture_output=True, text=True, errors="replace")
    if r.returncode != 0:
        return False, "lake does not find it up to date"
    return True, "built"


def move_stale(tag, mod, name):
    present = [p for p in files_of(mod, name) if os.path.exists(p)]
    if not present:
        return 0
    dest = os.path.join(RUNS, tag + "_stale", datetime.datetime.now().strftime("%Y%m%d_%H%M%S_") + name)
    os.makedirs(dest, exist_ok=True)
    for p in present:
        shutil.move(p, os.path.join(dest, os.path.basename(p)))
    return len(present)


def build(tag, target, out_path):
    """`lake build target`; the process ids of its `lean` processes are kept in TAG_lean.pid."""
    start = time.time()
    pid_path = os.path.join(RUNS, tag + "_lean.pid")
    with open(out_path, "wb") as out:
        proc = subprocess.Popen([LAKE, "build", target], cwd=ROOT, env=ENV, stdout=out,
                                stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        known = set()
        wait = 0.5
        while True:
            try:
                proc.wait(timeout=wait)
                break
            except subprocess.TimeoutExpired:
                pass
            leans = set(pid for pid, name in descendants(processes(), proc.pid) if is_lean(name))
            if leans - known:
                known |= leans
                io.open(pid_path, "w", encoding="ascii", newline="\n").write(
                    "".join("%d\n" % x for x in sorted(known)))
            wait = min(20.0, wait * 2)
    return proc.returncode, time.time() - start


def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    if len(sys.argv) != 2:
        raise SystemExit("usage: python runs/run_pieces.py TAG     (see the head of the script)")
    if LAKE is None:
        raise SystemExit("== FAILED: `lake` is not on the PATH")
    tag = sys.argv[1]
    lines = io.open(os.path.join(RUNS, tag + "_pieces.txt"), encoding="ascii").read().split()
    mod, names = lines[0], lines[1:]
    say("== driver for %s (module Results.%s, %d pieces), process id %d"
        % (tag, mod, len(names), os.getpid()))
    other = driver_alive(tag)
    if other is not None:
        say("== FAILED: another driver for %s is running (process id %d)" % (tag, other))
        return 1
    alive = lean_alive(tag)
    if alive:
        say("== FAILED: a lean process of this folder is still running (process ids %s); "
            "wait for it or stop it by its process id, then start again" % alive)
        return 1
    io.open(os.path.join(RUNS, tag + "_driver.pid"), "w", encoding="ascii", newline="\n").write("%d\n" % os.getpid())
    os.makedirs(os.path.join(RUNS, tag + "_pieces"), exist_ok=True)
    stop = os.path.join(RUNS, tag + "_STOP")
    done = 0
    for name in names:
        if os.path.exists(stop):
            say("== stopped: the file %s_STOP exists (%d of %d pieces built)" % (tag, done, len(names)))
            return 0
        ok, why = is_built(tag, mod, name)
        if ok:
            done += 1
            continue
        moved = move_stale(tag, mod, name)
        threads = set_threads(tag)
        say("piece %s: start, %d threads (%s%s)" % (name, threads, why,
                                                    ", %d old build files moved to %s_stale" % (moved, tag) if moved else ""))
        code, seconds = build(tag, "Results.%s.%s" % (mod, name), os.path.join(RUNS, tag + "_pieces", name + ".out"))
        if code != 0 or not os.path.exists(olean_of(mod, name)):
            say("== FAILED: piece %s, exit code %s after %.0f s; see runs/%s_pieces/%s.out"
                % (name, code, seconds, tag, name))
            return 1
        io.open(os.path.join(RUNS, tag + "_done.txt"), "a", encoding="ascii", newline="\n").write(
            "%s %d %.1f %s %s %s\n" % (name, threads, seconds, sha256(source_of(mod, name)),
                                       sha256(olean_of(mod, name)), now().replace(" ", "T")))
        done += 1
        say("piece %s: built in %.0f s (%d of %d)" % (name, seconds, done, len(names)))
    if os.path.exists(stop):
        say("== stopped: the file %s_STOP exists (all %d pieces built, top module not built)" % (tag, done))
        return 0
    threads = set_threads(tag)
    say("top module Results.%s: start, %d threads" % (mod, threads))
    top_out = os.path.join(RUNS, tag + "_top.out")
    code, seconds = build(tag, "Results.%s" % mod, top_out)
    text = io.open(top_out, encoding="utf-8", errors="replace").read()
    print(text, flush=True)
    if code != 0:
        say("== FAILED: top module Results.%s, exit code %s after %.0f s" % (mod, code, seconds))
        return 1
    say("top module built in %.0f s" % seconds)
    say("== all done")
    return 0


if __name__ == "__main__":
    sys.exit(main())
