# Tracking adaptations of Lean core

The initial scope is `RandomDo/Monad/MeasurableSpace.lean` and
`RandomDo/Monad/Notation.lean`. The annotations identify adaptations, not literal copies or
claims of semantic equivalence. They do not change the definitions or their docstrings.

```lean
@[upstream Bind]
class MeasurableSpaceBind ...

@[upstream Lean.Elab.Do.DoOps.default]
def randOps ...
```

Multiple origins use spaces: `@[upstream Pure Bind]`. Use fully qualified names when needed;
for example, `_root_.bind_congr` avoids resolving to the declaration being annotated.
The attribute rejects unknown names, duplicate origins, and declarations outside Lean core.
It is implemented in `RandomDo/Util/Upstream.lean`. To extend tracking to another module,
import that module in `scripts/ExportUpstream.lean` and record its annotated declarations.

## Checking an upgrade

Build the tracked modules, export their annotations, and compare against the running toolchain:

```sh
lake build --wfail RandomDo.Monad.MeasurableSpace RandomDo.Monad.Notation
lake env lean scripts/ExportUpstream.lean > .lake/upstream-current.json
python3 scripts/upstream.py check --metadata .lake/upstream-current.json
```

The build workflow runs this check on PRs, along with the attribute and checker tests.
New or removed annotations require an explicit baseline update. An upstream name that disappears
will also fail to resolve when building against the new toolchain.

`upstream.json` records, for each local/upstream pair, an immutable Lean commit, the upstream source
path and range, a hash of that source, and a review note. The exporter obtains ranges from Lean's
declaration metadata, including class fields, documentation, and definition bodies. A range is
used only with the exact commit at which it was recorded: later line insertions do not invalidate
it. The checker compares old upstream source with new upstream source, not with the intentionally
different RandomDo implementation. It needs Git and Python 3.10 or later, with no Python packages.

## Reviewing and recording a change

Read the report's upstream diff alongside the corresponding RandomDo declaration. Port relevant
changes or explain why they do not apply. Then record only the declarations reviewed in this PR:

```sh
python3 scripts/upstream.py record --metadata .lake/upstream-current.json \
  --only RDo.randOps --note 'Ported the core change; measurable-space arguments remain explicit.'
```

Each selected declaration's origins receive the current toolchain commit and source range.
Other declarations keep their existing baselines. Commit the baseline update with the adaptation
or explanation, so reviewers can see both. `--all` explicitly records every exported annotation
and removes obsolete mappings; use it only when all affected entries have been reviewed.
For a local rename, `--all` also reconciles the old and new identities; unchanged upstream entries
still need accurate review notes. The checker never advances baselines automatically.

The initial baseline is Lean v4.35.0. It records the existing adaptations as the starting point for
monitoring, not a completed correctness audit. In particular:

- `RDo.randOps` supplies measurable-space arguments and currently omits core's dead-syntax guard
  in `mkPureApp`. This is a known difference to investigate separately.
- The loop parsers, expander and elaborator retain the existing `rdo` adaptations; they do not
  implement core's `invariant` / `decreasing` annotations or its verification-condition hooks.
- The class hierarchy and laws have measurable-space parameters and measurability hypotheses,
  and omit the applicative layer. These differences are intentional.

## Watching future core changes

The `Watch Lean core adaptations` workflow checks upstream's default development branch each
Monday at 08:23 UTC and can also be run manually. Scheduled workflows become active once merged
to the repository's default branch. It reads upstream source only; it does not build or execute
future core code or change the project's toolchain.

When a tracked region changes, the workflow opens or updates one GitHub issue with the affected
local declarations, review notes, source links, and upstream diffs. Unchanged relevant edits do
not cause repeated updates when unrelated commits land in core. The issue is closed when no
tracked differences remain. Fetch, metadata, and other check failures fail the workflow and do
not close an existing issue. The watcher has read-only contents access and permission to maintain its issue.
The PR checks add no token permissions to the existing build workflow. No baseline updates or code changes are made by the watcher.

Run the same comparison locally:

```sh
python3 scripts/upstream.py check --target HEAD --report .lake/upstream-report.md
```

Without `--repo`, the checker fetches from `leanprover/lean4` into `.lake/upstream-lean.git`.
Use `--repo /path/to/lean4` before `check` or `record` to use an existing Git repository without
fetching. Exit statuses are 0 for unchanged, 1 for changes needing review, and 2 for an incomplete
or invalid check. `--advisory` changes status 1 to 0; errors still fail.

## Coverage and tests

Moved or deleted files and renamed declarations are reported through changes at their recorded
locations. Insertions immediately at either boundary are conservatively flagged because they
can extend a declaration. Unrelated changes elsewhere in the same file are ignored.
This is source-change detection: changes to untracked helpers or surrounding module/section
context can also affect behavior. It does not prove that an adaptation remains correct. Keep the project's behavior and elaboration tests.

```sh
python3 -m unittest discover -s scripts/tests -p 'test_upstream.py'
lake env lean scripts/tests/Upstream.lean
```

The Python tests construct local Git histories and require no network. They cover source/body
changes, boundary insertions, unrelated edits, moves/deletions, malformed or missing data,
partial review, exit statuses, baseline preservation, and notification deduplication.
