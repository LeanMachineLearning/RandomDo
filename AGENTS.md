# Refactor instructions

- The refactor targets polymorphic `rdo` programs. The `computable` meta approach is being
  deprecated; preserving compatibility with it must not constrain the new API or implementation.
  Any future wrapper providing similar functionality should work by polymorphizing programs.
- Include `Gaëtan Serré` in a file's `Authors:` header when it copies or adapts substantive
  implementation work he authored, such as definitions, functions, algorithms, or proofs.
  Minor docstring, formatting, naming, or lint changes alone do not warrant adding an author.
  Check the implementation actually transferred, rather than attributing every extracted section
  to everyone who touched the source file. Merely importing or calling his code is not authorship.
- Consult [REFACTOR_REVIEW.md](REFACTOR_REVIEW.md) for the files David has fully reviewed
  and approved. Keep it current with explicit approvals and mark approved files as needing
  re-review after substantive changes; do not infer approval from tests, audits, or merges.
- Keep new tests in the scaffold branch during the refactor; do not include them in PRs to main.
  The test suite will be curated after the full refactor is complete.
- Clearly mark placeholder code with `**PLACEHOLDER: …**` in its docstring or an adjacent
  comment, stating exactly what remains unimplemented. Distinguish missing implementations,
  provisional integration, and unfinished documentation from complete generic interfaces or
  code that is merely awaiting review.
