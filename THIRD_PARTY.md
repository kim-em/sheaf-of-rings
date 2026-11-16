# Third-party sources

All new material is licensed under [Apache-2.0](LICENCE). See [the licensing overview](licenses/README.md).

No third-party source files are vendored. The developments are checked against stock releases, which are fetched or installed separately.

## Archive of Formal Proofs

The Isabelle development builds on the AFP entries [Grothendieck's Schemes in Algebraic Geometry](https://isa-afp.org/entries/Grothendieck_Schemes.html), by Anthony Bordg, Lawrence C. Paulson, and Wenda Li, and [Jacobson Basic Algebra](https://isa-afp.org/entries/Jacobson_Basic_Algebra.html), by Clemens Ballarin. Both are BSD licensed. They are used unmodified, from the AFP release for Isabelle2026.

[`repair/repair.patch`](repair/repair.patch) is a patch against `Topological_Space.thy` and `Comm_Ring.thy` of the first entry. Its context and removed lines are excerpts of those files and remain under the AFP BSD license, reproduced in [`licenses/AFP-LICENSE`](licenses/AFP-LICENSE). The note also quotes a few lines of `Topological_Space.thy`.

## Isabelle

Isabelle2026 and its `HOL-Library` session are used as distributed.

## Lean and Mathlib

Lean and Mathlib are dependencies fetched by Lake; their sources are not vendored here. Mathlib is Apache-2.0 licensed, and Lean uses Apache-2.0 with its stated exceptions. Dependency commits are pinned in `lean/lake-manifest.json` and `lean/lean-toolchain`.
