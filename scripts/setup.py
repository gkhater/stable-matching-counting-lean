#!/usr/bin/env python3
"""Fetch pinned sources and apply the MathEconLib extension patch safely."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
EXTERNAL = ROOT / "external"
PATCH = ROOT / "patches" / "matheconlib.patch"
VENDORS = (
    ("matheconlib", "https://github.com/matheconlib/matheconlib.git", "58f602847d7f131994d32ca7a8cc1af35b7e2dbe"),
    ("formal-math", "https://github.com/anthropics/formal-math.git", "16a5ce41304fcdaea4e0be7c132e1c361dc26da5"),
)


def git(*args, cwd=None, check=True, capture=False):
    return subprocess.run(["git", "-c", "core.autocrlf=false", *map(str, args)],
                          cwd=cwd, check=check, text=True, encoding="utf-8",
                          stdout=subprocess.PIPE if capture else None,
                          stderr=subprocess.PIPE if capture else None)


def prepare(name, url, revision):
    dest = EXTERNAL / name
    if dest.is_symlink():
        raise RuntimeError(f"Refusing symlink: {dest}")
    if not dest.exists():
        git("clone", "--no-checkout", "--", url, dest)
        git("checkout", "--detach", revision, cwd=dest)
    if not dest.is_dir() or not (dest / ".git").is_dir():
        raise RuntimeError(f"Not a standalone Git checkout: {dest}")
    actual_root = Path(git("rev-parse", "--show-toplevel", cwd=dest, capture=True).stdout.strip()).resolve()
    if actual_root != dest.resolve():
        raise RuntimeError(f"Unexpected Git root: {actual_root}")
    origin = git("remote", "get-url", "origin", cwd=dest, capture=True).stdout.strip()
    if origin != url:
        raise RuntimeError(f"Unexpected origin for {dest}: {origin}")
    head = git("rev-parse", "HEAD", cwd=dest, capture=True).stdout.strip()
    if head != revision:
        raise RuntimeError(f"Wrong HEAD for {dest}: {head}; expected {revision}")
    print(f"Verified {name} at {head}", flush=True)
    return dest


def main():
    if EXTERNAL.is_symlink():
        raise RuntimeError(f"Refusing symlink: {EXTERNAL}")
    EXTERNAL.mkdir(exist_ok=True)
    # Verify both checkouts before modifying either vendor tree.
    paths = [prepare(*vendor) for vendor in VENDORS]
    repo = paths[0]
    if git("apply", "--reverse", "--check", PATCH, cwd=repo, check=False, capture=True).returncode == 0:
        print("MathEconLib patch already applied.")
    else:
        git("apply", "--check", PATCH, cwd=repo)
        git("apply", PATCH, cwd=repo)
        print("Applied MathEconLib patch.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as exc:
        print(f"Setup failed: {exc}", file=sys.stderr)
        sys.exit(1)
