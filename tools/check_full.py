"""Check the three closed endpoints and the detector-index theorem in both bases."""
import argparse
import shutil
import subprocess
import tempfile
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument("--lake", default=shutil.which("lake") or "lake")
a = p.parse_args()
root = Path(__file__).resolve().parents[1]
source = """import HoffmanChromatic
open scoped Classical
example : HoffmanChromatic.RoundedTarget := HoffmanChromatic.rounded_chromatic
example : HoffmanChromatic.SubsequenceTarget := HoffmanChromatic.subsequence_chromatic
example : HoffmanChromatic.UniformTarget := HoffmanChromatic.uniform_chromatic
example (P D : ℕ) (hP : 0<P) :
    HoffmanChromatic.HasBinomialDetector P D ↔
      (if ∃ ell : ℕ, P=2^ell then P-1 else 2*P-1) ≤ D := by
  classical
  exact HoffmanChromatic.minimum_detector_index_iff P D hP
example (P D : ℕ) (hP : 0<P) :
    HoffmanChromatic.HasShiftedBinomialDetector P D ↔
      (if ∃ ell : ℕ, P=2^ell then P-1 else 2*P-1) ≤ D := by
  classical
  exact HoffmanChromatic.minimum_shifted_detector_index_iff P D hP
"""
with tempfile.TemporaryDirectory(prefix="hoffman-completion-") as tmp:
    f = Path(tmp) / "Complete.lean"
    f.write_text(source)
    result = subprocess.run([a.lake, "env", "lean", "-DwarningAsError=true", str(f)], cwd=root)
if result.returncode:
    raise SystemExit("FULL FORMALIZATION NOT VERIFIED: at least one endpoint proof is missing.")
print("All three endpoint proofs and both detector-index equivalences are checked.")
