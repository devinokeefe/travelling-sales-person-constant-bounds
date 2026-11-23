"""Portable build and verification driver for BHHBounds Lean 4 modules.

Supports building individual modules or parallel batches against either the local
`.lake/packages` directory (populated by `lake exe cache get`) or an existing
Mathlib checkout matching `lean-toolchain` via `--cache` or `BHH_MATHLIB_CACHE`.
"""
import argparse
import concurrent.futures
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def find_mathlib_cache(override: Path | None) -> Path:
    """Locate a directory containing `.lake/packages` for the pinned Mathlib."""
    if override is not None:
        return override
    env_path = os.environ.get("BHH_MATHLIB_CACHE")
    if env_path:
        return Path(env_path)
    if (ROOT / ".lake" / "packages").exists():
        return ROOT
    raise FileNotFoundError(
        "No `.lake/packages` directory found. Run `lake exe cache get && lake build`, "
        "or pass `--cache /path/to/mathlib-checkout` (or set `BHH_MATHLIB_CACHE`)."
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build and verify BHHBounds Lean 4 modules."
    )
    parser.add_argument("modules", nargs="+", help="Dotted Lean module names to build.")
    parser.add_argument(
        "--cache",
        type=Path,
        default=None,
        help="Path to a Lake workspace containing a prebuilt `.lake/packages` cache.",
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="Parallel worker count for independent modules.",
    )
    parser.add_argument(
        "--threads",
        type=int,
        default=2,
        help="Threads per `lean` invocation (`-j`).",
    )
    args = parser.parse_args()

    cache = find_mathlib_cache(args.cache)
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    bin_dir = (
        Path.home()
        / ".elan"
        / "toolchains"
        / toolchain.replace("/", "--").replace(":", "---")
        / "bin"
    )
    ext = ".exe" if os.name == "nt" else ""
    lean_exe = bin_dir / ("lean" + ext)

    packages = cache / ".lake" / "packages"
    out = ROOT / ".lake" / "build" / "lib" / "lean"
    out.mkdir(parents=True, exist_ok=True)
    paths = [out] + [d / ".lake" / "build" / "lib" / "lean" for d in packages.iterdir() if d.is_dir()]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(p) for p in paths))

    def build_one(mod: str) -> tuple[str, float]:
        t0 = time.time()
        rel = Path(*mod.split("."))
        artifact = (out / rel).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        src = rel.with_suffix(".lean")
        res = subprocess.run(
            [str(lean_exe), f"-j{args.threads}", "-o", str(artifact), str(src)],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
        )
        dt = time.time() - t0
        if res.stdout:
            print(res.stdout, end="")
        if res.stderr:
            print(res.stderr, end="", file=sys.stderr)
        if res.returncode != 0:
            raise RuntimeError(f"Failed to build {mod} (exit {res.returncode})")
        return mod, dt

    t_start = time.time()
    if args.jobs <= 1 or len(args.modules) <= 1:
        for mod in args.modules:
            print(f"Building {mod} ...", flush=True)
            _, dt = build_one(mod)
            print(f"  OK {mod} ({dt:.2f}s)", flush=True)
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = {ex.submit(build_one, m): m for m in args.modules}
            for fut in concurrent.futures.as_completed(futs):
                mod, dt = fut.result()
                print(f"  OK {mod} ({dt:.2f}s)", flush=True)
    print(f"Done ({len(args.modules)} module(s), {time.time() - t_start:.2f}s total).")


if __name__ == "__main__":
    main()
