# Release verification — 1.1.0

**Result: PASS, 2026-09-21.** The isolated build checked all 58 project
modules without warnings. The dependency audit covered 871 mathematical
declarations, including 730 theorems and generated equations, and 138
definitions. All closed endpoint and detector-index checks passed.

The verification record for this release is in `verification/`. Its scope
is all three extended-abstract endpoints and the exact minimal-detector-index
theorem in both bases. `PROOF_STATUS.md` maps the mathematics to the source.

## Reproduction procedure

The release was prepared in a separate project directory. The nine dependency
repositories were fetched afresh from their upstream URLs at the revisions
locked in `lake-manifest.json`. No prior project build files were copied into
this reproduction directory. The required official mathlib cache was fetched
into a separate, initially empty download directory.

The toolchain is Lean 4.19.0, commit `6caaee842e94`, with Lake
5.0.0-6caaee8 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
Lean itself is the pinned release binary. Mathlib's precompiled dependency
cache is used; this is a fresh build of every project module, not a bootstrap
of Lean and all of mathlib from source.

The standard reproduction commands are:

```sh
python3 tools/fetch_cache.py
python3 tools/verify.py --clean
```

The recorded local run passes an explicit path to the same pinned Lake
executable and writes to `verification/` using `--logs verification`.
In this container, archive extraction also required
`TAR_OPTIONS=--no-same-owner`; this changes file ownership handling, not the
archive contents or any Lean source. Shallow dependency fetching required
fetching ProofWidgets' `v0.0.57` tag in addition to its pinned commit.
The usual Lake dependency checkout performs that setup automatically.

## What the checks establish

- `build.log`: every project module compiles, with warnings treated as errors.
- `dependencies.log` and `dependencies-after.log`: all dependency revisions
  match the lockfile, with no tracked or untracked source changes.
- `regeneration.log`: all three generated Lean witness files reproduce
  byte for byte from the included Python scripts.
- `axioms.log`: automatic discovery by source module includes private proofs,
  definitions and generated equations. Only `propext`, `Classical.choice`
  and `Quot.sound` occur as axioms in the transitive mathematical closure.
  Unsafe compiler runtime declarations are listed separately and must be
  absent from that closure.
- `statements.log` and `full-completion.log`: the three endpoints are inhabited
  by closed proof terms; the direct colouring formulations compile; the exact
  detector-index formula holds for every positive P in both bases.
- `arithmetic.log`: the printed M=200 rows, subsequence comparison, crossing
  rows, constant enclosure and six interior bounds also pass an independent
  exact rational replay using the article's own logarithm remainder.

The Python checks supplement the Lean proofs. They are not trusted proof
oracles. Counts of generated declarations do not count independent research
results. `verification/RESULT.txt` records the totals and final outcome.

## Scope and distribution

The exact constant is defined by the unique crossing in the stated bracket;
the certified enclosure is **1.309251 < C_* < 1.309252**. The constant
prefactor and eventual dimension threshold are existential. No explicit
numerical c or d0, eleven-decimal enclosure, or arbitrary-Q valuation theorem
is claimed. The required Q=6,7 factorizations are proved directly.

The original English paper, extended abstract and figures are unchanged.
Their hashes remain in `PROVENANCE.json`. `SHA256SUMS.txt` covers the release
files; on a freshly extracted archive it can be checked with
`sha256sum -c SHA256SUMS.txt` before generating new logs.

The GitHub Actions workflow is included, with actions pinned by commit and
the GitHub build cache disabled. Its verification commands are those above.
No remote GitHub CI run is claimed: no external repository was supplied.
