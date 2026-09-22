# Release 1.1.0 — 2026-09-21

- Proved the exact minimal detector index for every positive period, in both
  the ordinary and shifted binomial bases. This closes the separate remark
  in the article without enumerating periods.
- Included direct statements of all three chromatic bounds in terms of
  arbitrary finite colouring functions on Euclidean space.
- Replaced the handwritten public-theorem audit with automatic discovery by
  source module. Private proofs, definitions, generated equations, and their
  transitive axiom dependencies are audited as well.
- Removed all 12 previous Lean warnings and made warnings fail the build.
  Two unused assumptions and four unnecessary typeclass parameters were
  removed from intermediate lemmas; no linter was disabled.
- Added exact witness regeneration, independent replay of the printed
  arithmetic, clean dependency checks, a clean-build option, and a GitHub
  Actions workflow pinned by commit.

The three principal bounds are unchanged. The exact crossing defines C_*;
the certified numerical enclosure remains 1.309251 < C_* < 1.309252.
Constants and dimension thresholds remain existential. The reference paper
and extended abstract are unchanged.

The recorded verification describes the local reproduction actually run.
The GitHub workflow is supplied for future repository use; no remote CI run
is claimed by this release.
