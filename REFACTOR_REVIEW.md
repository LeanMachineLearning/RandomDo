# Refactor review tracker

<!-- Authors: David Ledvinka, Gaëtan Serré -->

This records David's explicit review approvals, including partial file reviews.
Files and portions of files not listed below are still pending review and approval.

Review preference: finish the generic APIs and WP support, then complete and review
`RDo/Core.lean` and `RDo/Loop.lean` before reviewing monad-specific
implementations. Include concrete prerequisites where required, such as the list traversal
API used by the generic collection-loop specifications. This order does not imply approval
of any file.

| File | Status | Approval date |
| --- | --- | --- |
| [MeasurableSpaceMonad/Defs.lean](RandomDo/MeasurableSpaceMonad/Defs.lean) | Approved | 2026-11-17 |
| [MeasurableSpaceMonad/ForIn.lean](RandomDo/MeasurableSpaceMonad/ForIn.lean) | Approved | 2026-11-17 |
| [MeasurableSpaceMonad/ForInInstances/Iterators/Loop.lean](RandomDo/MeasurableSpaceMonad/ForInInstances/Iterators/Loop.lean) | Needs re-review through `LawfulMeasurableSpaceIteratorLoop`: producer generalized to a measurable monad, state/output spaces moved to class parameters, and termination relations adapted. Pure/core compatibility moved to `CoreLoop.lean`. Loop operations and associated lemmas renamed to `mForIn`/`mForIn'`. Later declarations and new `Basic.lean`/`Core.lean` remain pending. | 2026-11-15 |
| [WP/MeasurableSpaceMonad.lean](RandomDo/WP/MeasurableSpaceMonad.lean) | Needs re-review: moved the class and its associated laws to `MeasureTheory`, and the generic specification rules to `MeasureTheory.WP.Spec`; the triple lemmas remain in `Std.WP.Triple`. | 2026-11-17 |
| [WP/ForIn.lean](RandomDo/WP/ForIn.lean) | Approved outside `section Loop`; the loop implementation and specifications now await review. Header/imports updated; collection definitions and proofs unchanged. | 2026-11-17 |
| [RDo/Loop.lean](RandomDo/RDo/Loop.lean) | Needs re-review: updated the optional WP class lookup to `MeasureTheory.WPMeasurableSpaceMonad`; the elaboration logic is unchanged. | 2026-11-17 |

Only explicit approval updates a file to this status. Passing builds or tests,
assistant audits, and merged PRs do not establish approval.

Approval applies to the reviewed version. After substantive changes to an approved
file, mark it as **Needs re-review** until those changes are explicitly approved.
