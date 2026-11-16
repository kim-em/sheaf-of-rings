# The Isabelle/HOL formalization of sheaves has been incorrect for 5 years

[Read the note](article/note.pdf) ([Verso source](article/verso/Note.lean)).

The AFP entry [*Grothendieck's Schemes in Algebraic Geometry*](https://isa-afp.org/entries/Grothendieck_Schemes.html) states the sheaf axioms only for covers indexed by sets of real numbers. This repository records four consequences, each checked in Isabelle/HOL against the unmodified entry, and the corresponding statements in Lean with Mathlib.

1. The entry's predicate `sheaf_of_rings` accepts a presheaf that fails gluing.
2. Hartshorne's Proposition II.1.1 is false for these sheaves: there is a morphism that is an isomorphism on every stalk and is not an isomorphism.
3. The entry's predicate `scheme` accepts an object whose structure presheaf fails gluing.
4. The entry's predicate `scheme` accepts an object whose ring of global sections is not commutative.

Nothing false is proved in the entry, and its construction of the structure sheaf of a spectrum is the standard one. What its theorems assert is weaker than their names suggest.

New material is licensed under [Apache-2.0](LICENCE); see [the licensing overview](licenses/README.md). [`formalization.yaml`](formalization.yaml) records the Lean development's sources, results, automation, and review status in the [Mathlib Initiative format](https://github.com/mathlib-initiative/formalization.yaml). Validate it with:

```sh
uvx check-jsonschema --no-cache --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json formalization.yaml
```

## Files and results

| File | What it establishes |
| --- | --- |
| [`counterexample/Counterexample.thy`](counterexample/Counterexample.thy) | `counterexample_to_arbitrary_gluing`: the bounded-range presheaf on `ℝ → ℤ` satisfies `sheaf_of_rings`, and an explicit compatible family over the cover by points has no gluing. `sections_comm_ring` checks commutativity. |
| [`counterexample/Stalk_Counterexample.thy`](counterexample/Stalk_Counterexample.thy) | `exists_stalkwise_iso_not_iso` existentially quantifies the presheaf and morphism data, with the construction confined to the proof; its stalk maps use the AFP definition. `stalkwise_iso_not_iso`: the inclusion of the bounded-range presheaf into the presheaf of all functions is a `morphism_sheaves_of_rings` inducing a ring isomorphism on every stalk, and is not an `iso_sheaves_of_rings`. `stalkwise_iso_not_iso_ringed_spaces` states the same with the entry's `morphism_ringed_spaces`, `homeomorphism` and `induced_morphism`. |
| [`counterexample/Point_Schemes.thy`](counterexample/Point_Schemes.thy) | `open_points_scheme_field`: any `sheaf_of_rings` on a space with open points whose rings over the points are fields satisfies `scheme`. `open_points_scheme` is the version for local rings with one prime ideal. |
| [`counterexample/Scheme_Counterexample.thy`](counterexample/Scheme_Counterexample.thy) | `afp_scheme_without_gluing`: the bounded-range presheaf with values in the local ring of [`BigRing.thy`](counterexample/BigRing.thy) satisfies `scheme`, and the same compatible family has no gluing. |
| [`counterexample/NC_Scheme.thy`](counterexample/NC_Scheme.thy) | `exists_scheme_with_noncommutative_global_sections` existentially quantifies all scheme data, with fixed ambient carrier types. `afp_scheme_with_noncommutative_global_sections`: an object satisfying `scheme` with global sections `u`, `v` such that `u·v ≠ v·u`. The construction is in [`NC_Core.thy`](counterexample/NC_Core.thy) and [`NC_Counterexample.thy`](counterexample/NC_Counterexample.thy). |
| [`counterexample/Small_Range.thy`](counterexample/Small_Range.thy) | Cardinality bounds and the bounded-range sections, operations and restrictions. |
| [`counterexample/Audit.thy`](counterexample/Audit.thy) | Fails the build if any of the results above depends on an oracle or a skipped proof. |
| [`lean/Counterexample.lean`](lean/Counterexample.lean) | `boundedRing_gluing_of_small_index` and `largeRing_not_isSheaf_commRing`: the presheaf of result 1, as a presheaf of commutative rings, glues over every cover with at most continuum many members and is not a sheaf in Mathlib's sense. `isIso_of_stalkwise_iso` records Mathlib's proof of Proposition II.1.1. |
| [`repair/`](repair) | A patch to the entry that indexes covers by sets of open sets, and a check that the patched entry builds and its sheaf predicate gives gluing over families indexed by an arbitrary type. |

## Check Isabelle/HOL

Requirements: the stock [Isabelle2026](https://isabelle.in.tum.de/) release and the stock [AFP release for Isabelle2026](https://www.isa-afp.org/download/). No AFP source is vendored or modified.

If the AFP is registered as an Isabelle component:

```sh
./counterexample/check.sh
```

Otherwise pass its `thys` directory, and optionally the Isabelle executable:

```sh
AFP=/path/to/afp/thys ./counterexample/check.sh
ISABELLE=/path/to/Isabelle2026/bin/isabelle AFP=/path/to/afp/thys ./counterexample/check.sh
```

The script builds the AFP session `Grothendieck_Schemes` and then the session in [`counterexample/`](counterexample), and prints the checked statements of the headline results. It took about one minute on our machine once the `HOL` heap existed.

To check the repair:

```sh
AFP=/path/to/afp/thys ./repair/check.sh
```

This copies the entry to a temporary directory, applies [`repair/repair.patch`](repair/repair.patch) (76 lines added, 23 removed, in `Topological_Space.thy` and `Comm_Ring.thy`), and rebuilds the whole entry.

Note for NixOS users: the Z3 binary bundled in the nixpkgs package of Isabelle2025-2 crashed on our machine, which breaks the unmodified AFP entry. The official release tarball does not have this problem.

## Check Lean

With [elan](https://github.com/leanprover/elan) installed:

```sh
cd lean
lake exe cache get
lake build
```

The toolchain is stock **Lean v4.35.0**, with Mathlib pinned to the release tag [`v4.35.0`](https://github.com/leanprover-community/mathlib4/tree/v4.35.0) (commit [`56a005855ea17e0b0958f73ec801ae140b0a1679`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)). Both the toolchain and dependency manifest are committed.

Alternatively, reuse a Mathlib checkout at **that exact revision** with its cache installed:

```sh
./lean/check.sh /path/to/mathlib4
```

The `#print axioms` commands report only `propext`, `Classical.choice`, and `Quot.sound`. The negative result uses the cover of the discrete space `ℝ → ℤ` by its points, indexed by `ℝ → ℤ` itself. Index type and sections lie in `Type 0`; no universe issue is involved.

## Build the article

```sh
make -C article
```

Edit [`article/verso/Note.lean`](article/verso/Note.lean), the authoritative source. The build generates both the PDF and a native Verso blog page, runs `pdflatex` twice, and checks the output. `article/note.tex` and `article/note.pdf` are committed generated artifacts. Requirements and preview instructions are in [`article/verso/README.md`](article/verso/README.md).

Isabelle theorem links are resolved by declaration name during the build. `python3 article/check_links.py` checks that the committed links still point to those declarations; CI runs this check on pushes and pull requests. Run `make -C article` to refresh links after moving declarations.

`make -C article submission` also prepares a TeX-only source ZIP with immutable theorem links, without submitting it anywhere.

## Sources

The note cites Hartshorne, *Algebraic Geometry*, Section II.1; the [AFP entry](https://isa-afp.org/entries/Grothendieck_Schemes.html); [the associated paper](https://arxiv.org/abs/2104.09366); and Lawrence Paulson's blog post [*The concept of definition: in mathematics, and in computational logic*](https://lawrencecpaulson.github.io/2025/06/04/Definitions.html) of 4 June 2025.

The restriction is in `Topological_Space.thy`, lines 77 to 82 (the locale `cover_of_subset`), and `Comm_Ring.thy`, lines 660 to 666 (the locale `sheaf_of_rings`). Both locales are unchanged from the first AFP revision of the entry (9 April 2021) to [`mirror-afp-devel` at `bda1576f4422c042210bb7cc8406ef1335dcdfb5`](https://github.com/isabelle-prover/mirror-afp-devel/tree/bda1576f4422c042210bb7cc8406ef1335dcdfb5/thys/Grothendieck_Schemes) (14 November 2026).

## Verification

Checked on 16 November 2026:

- `counterexample/check.sh` and `repair/check.sh` succeed with the official Isabelle2026 Linux release (`Isabelle2026_linux.tar.gz`, SHA-256 `858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`) and the AFP release `afp-2026-11-15` (`afp-current.tar.gz`, SHA-256 `5fc231f2cda5a39f6115d2fd72e5c1cba023d31ad46c6ef5334bf7383c3d9135`). The entry in that release is identical to [`mirror-afp-2026` at `aaa511aa20958abfed536c271dfd2fe115515d6c`](https://github.com/isabelle-prover/mirror-afp-2026/tree/aaa511aa20958abfed536c271dfd2fe115515d6c/thys/Grothendieck_Schemes).
- `lake build` succeeds from a fresh copy of [`lean/`](lean).
- The article compiles without overfull boxes.
