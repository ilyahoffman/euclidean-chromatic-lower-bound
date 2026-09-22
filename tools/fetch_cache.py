"""Fetch the pinned mathlib cache only for this project's dependency closure."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    modules = set()
    for source in (root / "HoffmanChromatic").rglob("*.lean"):
        modules.update(re.findall(r"^import (Mathlib\.[A-Za-z0-9_.]+)$",
                                  source.read_text(), re.MULTILINE))
    if not modules:
        raise SystemExit("No mathlib imports found")
    subprocess.run([args.lake, "exe", "cache", "get", *sorted(modules)],
                   cwd=root, check=True)


if __name__ == "__main__":
    main()
