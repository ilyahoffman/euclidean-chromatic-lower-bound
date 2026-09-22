"""Build and audit all project mathematics with the locked Lean toolchain.

A fresh run checks dependency revisions, regenerates every witness file in a
temporary directory, replays the article's arithmetic independently, builds Lean,
audits all declarations and their transitive axioms, and checks closed endpoints.
Python checks are supplementary: only Lean proof terms certify the mathematics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def run_logged(root, out, name, command):
    print("Running:", " ".join(map(str, command)), flush=True)
    path = out / name
    with path.open("w") as log:
        result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print("\n".join(path.read_text().splitlines()[-30:]), file=sys.stderr)
        raise SystemExit(f"FAILED: inspect {path}")
    return path.read_text()


def check_dependencies(root, log):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    if (root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
        raise SystemExit("The Lean toolchain differs from this release's pin")
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != "c44e0c8ee63ca166450922a373c7409c5d26b00b":
        raise SystemExit("The mathlib revision differs from this release's pin")
    for package in manifest["packages"]:
        path = root / ".lake" / "packages" / package["name"]
        head = subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        status = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"],
            text=True).strip()
        if head != package["rev"] or status:
            raise SystemExit(f"Dependency is not a clean pinned checkout: {package['name']}\n{status}")
        print(f"PASS: {package['name']} at {head}; clean checkout.", file=log)


def check_regeneration(root, log):
    names = ("NewtonData.lean", "SharpCertificates.lean", "InteriorCertificates.lean")
    with tempfile.TemporaryDirectory(prefix="hoffman-witnesses-") as tmp:
        temp = Path(tmp)
        (temp / "tools").mkdir()
        (temp / "HoffmanChromatic").mkdir()
        for script in ("generate_newton.py", "generate_sharp_certificates.py"):
            shutil.copy2(root / "tools" / script, temp / "tools" / script)
            subprocess.run([sys.executable, str(temp / "tools" / script)], cwd=temp,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        for name in names:
            original = (root / "HoffmanChromatic" / name).read_bytes()
            generated = (temp / "HoffmanChromatic" / name).read_bytes()
            if original != generated:
                raise SystemExit(f"Generated witness source differs: {name}")
            print(f"PASS: byte-identical {name}; SHA-256 {hashlib.sha256(original).hexdigest()}.",
                  file=log)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument("--logs", default="verification/reproduced")
    parser.add_argument("--clean", action="store_true",
                        help="Remove only this project's build directory before verification")
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run verification without Python's -O option")
    root = Path(__file__).resolve().parents[1]
    out = root / args.logs
    out.mkdir(parents=True, exist_ok=True)
    sources = sorted((root / "HoffmanChromatic").rglob("*.lean"))
    forbidden = re.compile(
        r"\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\s",
        re.MULTILINE,
    )
    for path in sources + [root / "HoffmanChromatic.lean"]:
        if forbidden.search(path.read_text()):
            raise SystemExit(f"Disallowed proof construct in {path.relative_to(root)}")
    with (out / "dependencies.log").open("w") as log:
        check_dependencies(root, log)
    with (out / "regeneration.log").open("w") as log:
        check_regeneration(root, log)
    version = run_logged(root, out, "toolchain.log", [args.lake, "env", "lean", "--version"])
    if "version 4.19.0," not in version or "6caaee842e94" not in version:
        raise SystemExit("Unexpected Lean executable: " + version)
    if args.clean:
        build = root / ".lake" / "build"
        if build.is_symlink() or (build.exists() and build.resolve() != build.absolute()):
            raise SystemExit("Refusing to remove a redirected build directory")
        if build.exists():
            shutil.rmtree(build)
    build_log = run_logged(root, out, "build.log", [args.lake, "build"])
    if re.search(r"\bwarning:", build_log, re.IGNORECASE):
        raise SystemExit("Build produced warnings; inspect build.log")
    audit = run_logged(root, out, "axioms.log",
                       [args.lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"])
    imported = set(re.findall(r"^IMPORTED_MODULE (\S+)$", audit, re.MULTILINE))
    expected = {"HoffmanChromatic"} | {
        ".".join(p.relative_to(root).with_suffix("").parts) for p in sources
    }
    if not expected.issubset(imported):
        raise SystemExit("Unaudited project modules: " + ", ".join(sorted(expected - imported)))
    checked_modules = set(re.findall(r"^CHECKED_DECLARATION (\S+) ", audit, re.MULTILINE))
    if not (expected - {"HoffmanChromatic"}).issubset(checked_modules):
        raise SystemExit("An imported source module has no audited declarations")
    match = re.search(r"PASS: dynamically checked (\d+) mathematical declarations; (\d+) theorems", audit)
    if not match:
        raise SystemExit("Dynamic dependency audit did not report success")
    run_logged(root, out, "statements.log",
               [args.lake, "env", "lean", "-DwarningAsError=true", "Statements.lean"])
    run_logged(root, out, "full-completion.log",
               [sys.executable, "tools/check_full.py", "--lake", args.lake])
    run_logged(root, out, "arithmetic.log",
               [sys.executable, "tools/check_arithmetic.py"])
    with (out / "dependencies-after.log").open("w") as log:
        check_dependencies(root, log)
    summary = (
        f"PASS: warning-free project build; {len(expected)} project modules imported and audited.\n"
        f"PASS: {match[1]} mathematical declarations and all transitive axiom dependencies.\n"
        "ALLOWED AXIOMS: propext, Classical.choice, Quot.sound.\n"
        "PROVED: RoundedTarget, SubsequenceTarget, UniformTarget, and direct colouring statements.\n"
        "PROVED: exact minimal detector index for every positive P, in both binomial bases.\n"
        "PASS: clean pinned dependencies, byte-identical witness regeneration, independent article arithmetic.\n"
        f"Project build cache removed for this run: {args.clean}.\n"
    )
    (out / "RESULT.txt").write_text(summary)
    print(summary, end="")


if __name__ == "__main__":
    main()
