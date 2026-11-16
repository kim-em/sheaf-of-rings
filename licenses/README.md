# Licensing

Copyright 2026 Kim Morrison and the sheaf-of-rings contributors.

All new material in this repository is licensed under the **Apache License, Version 2.0**. See the full text in [`../LICENCE`](../LICENCE). This includes the Isabelle and Lean developments, the article's LaTeX source and compiled PDF, documentation, scripts, configuration, and metadata, including `formalization.yaml`.

No third-party source files are vendored. One file contains excerpts of third-party material:

| Material | Upstream license and notices |
| --- | --- |
| Context and removed lines in [`../repair/repair.patch`](../repair/repair.patch), taken from `Topological_Space.thy` and `Comm_Ring.thy` of the AFP entry `Grothendieck_Schemes` | AFP BSD license; authors Anthony Bordg, Lawrence C. Paulson, and Wenda Li. See [`AFP-LICENSE`](AFP-LICENSE). |

The upstream license file in this directory is retained verbatim. The added lines of the patch are Apache-2.0 licensed; the upstream portions remain subject to their existing BSD terms. The repository's Apache license does not replace that license or remove its attribution and redistribution requirements.

See [`../THIRD_PARTY.md`](../THIRD_PARTY.md) for the dependencies. Isabelle, the AFP, Lean and Mathlib are installed or fetched separately; their upstream licenses continue to apply.
