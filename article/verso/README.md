# Article source and rendering

`Note.lean` is the authoritative document. It contains the prose, mathematics, abstract, epigraph, theorems, citations, and bibliography. It contains no layout commands or raw HTML/TeX blocks. The same elaborated document generates the PDF and a native Verso blog post.

Run `make -C article` from the repository root. This builds the pinned Verso project, renders both formats, runs pdflatex twice, validates the output, and updates the committed `article/note.tex` and `article/note.pdf`. Those two files are generated: edit `Note.lean` instead. Requirements are elan, pdflatex, Python 3, and Poppler (`pdftotext`, `pdftohtml`).

Run `make -C article submission` to additionally produce `_out/submission/source.zip`, a self-contained TeX upload with theorem links pinned to a Git commit. This does not submit or publish anything.

## Files

- `Article.lean`: semantic directives and roles.
- `Render.lean`: TeX rendering and conversion to `Verso.Genre.Blog.Post`. No Markdown or HTML round-trip is involved.
- `article-style.tex`: PDF presentation settings.
- `Main.lean`: source-link resolution and output generation.
- `BlogTheme.lean`, `theme.css`: unmodified snapshots of the existing blog's theme at `kim-em/kim-em.github.io@064cb75774373fa070f05bf946b3b3cf6ee020fc`.
- `check.py`: output checks. `../check_links.py` also checks the committed TeX links without needing Lean or TeX, for CI.

Theorems are identified by declaration name. The build resolves their current Isabelle file and line number automatically and fails if a reference is missing. CI detects stale committed links and requests a rebuild.

## Blog

The generated site is in `_out/html`. Serve it with `python3 -m http.server --directory article/verso/_out/html`; root-relative assets require an HTTP server rather than `file://`.

The native blog projection uses the existing theme, but the deployed blog remains on its older toolchain. Integration requires aligning versions or backporting the adapter; this repository does not deploy the blog. Publishing remains a separate action.

## Dependencies and validation

The document uses stock Lean `v4.36.0-rc2` and Verso at `a40afc8c44badcc1e58f060ec70a2aa5cb6243c6`, pinned in Lake. These are independent of the Lean `v4.35.0` mathematical proofs under `lean/`. No upstream patches are required. The copied blog theme produces deprecation warnings on the newer Verso but compiles and renders successfully.

During migration, the PDF was checked against the approved LaTeX version: the text and page contents matched across all four pages, with minor identifier wrapping differences and about 5pt more space before the author. The subsequently requested final credit reads “Document prepared in Verso.” Both PDF and HTML were visually checked.

The renderer supports the elements used in this article and fails on unsupported elements. Its semantic layer can be adapted to upstream Article/STEM interfaces when those become available; document wording and layout remain separate.
