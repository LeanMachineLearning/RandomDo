# Lean core tracking

This directory contains maintainer tooling run by GitHub Actions. The library provides only the
`analogue` attribute and its annotations; checking, baseline updates, and issue reporting live here.
All commands below run from the repository root.

Use `@[analogue Core.declaration]` to link an adaptation to its Lean core counterpart:

```lean
@[analogue Bind]
class MeasurableSpaceBind ...

@[analogue Lean.Elab.Do.DoOps.default]
def randOps ...
```

Multiple names use spaces: `@[analogue Pure Bind]`. Qualify names when necessary;
`_root_.bind_congr`, for example, avoids resolving to the declaration being annotated.
The attribute resolves and records names. It is defined in `RandomDo/Util/Analogue.lean` and has
no dependency on this tooling. The exporter restricts this workflow's tracked origins to Lean core.

## Checking for changes

The initial scope is `RandomDo/Monad/MeasurableSpace.lean` and `RandomDo/Monad/Notation.lean`.
To check the current toolchain against the recorded baselines:

```sh
lake build --wfail RandomDo.Monad.MeasurableSpace RandomDo.Monad.Notation
lake env lean .github/upstream/Export.lean > .lake/upstream-current.json
python3 .github/upstream/check.py check --metadata .lake/upstream-current.json
```

The build workflow runs this check on PRs. The exporter gets declaration locations from Lean;
`.github/upstream/baseline.json` stores the source path, line range, and exact Lean commit for each
mapping.
The Python script uses Git to compare those upstream regions with the target revision. It
requires Python 3.10+ and Git, with no Python packages. Later line insertions do not shift the
baseline because its range always refers to its recorded commit.

The weekly workflow compares against Lean's default development branch every Monday at 08:23 UTC.
It maintains one issue listing affected declarations and linking to the full diff report.
Unchanged relevant edits do not cause repeated updates. It closes the issue when differences
are resolved; a failed check fails the workflow and leaves the issue alone. The schedule starts
after merge to the default branch and can also be run manually.

To run the same comparison locally:

```sh
python3 .github/upstream/check.py check --target HEAD --report .lake/upstream-report.md
```

Sources are fetched into `.lake/upstream-lean.git`; no future Lean code is built or executed.
Use `--repo /path/to/lean4` before the subcommand to use a local Git repository without fetching.
Exit codes are 0 for unchanged, 1 for changes, and 2 for errors. `--advisory` allows changes while
still failing on errors; it is used by the weekly workflow.

## Updating a baseline

Review the upstream diff, adapt the local code as needed, and explain intentional differences
in the PR. Then record just the declarations you reviewed:

```sh
python3 .github/upstream/check.py record --metadata .lake/upstream-current.json --only RDo.randOps
```

Commit the generated baseline change with the adaptation. Other declarations retain their
baselines. For a rename, pass both old and new names to `--only`; for a removed annotation,
pass its old name. `--all` explicitly records every mapping. Checks never advance baselines.
To track another module, import it in `.github/upstream/Export.lean`, export, and record its mappings.

## Scope

The initial Lean v4.35.0 baseline starts monitoring the existing adaptations; it is not a
correctness audit. Known differences include the omitted dead-syntax guard in the
`mkPureApp` override in `RDo.randOps`, the loop adapters' missing `invariant` / `decreasing` syntax and
verification hooks, and the measurable hierarchy's intentional omission of applicative classes.

The checker reports edits within a declaration, including its body, and conservatively includes
insertions and replacements at either boundary. Renames and file moves are reported at the old
location. Changes to untracked helpers or surrounding sections can also affect behavior, so normal
elaboration and behavior tests remain necessary.

The checker, attribute, and issue tests run offline:

```sh
python3 -m unittest discover -s .github/upstream/tests -p 'test_check.py'
lake env lean .github/upstream/tests/Analogue.lean
node --test .github/upstream/tests/test_notify.cjs
```
