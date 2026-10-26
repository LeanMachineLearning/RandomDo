/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import RandomDo.Monad.Notation
import Lean.DeclarationRange
import Lean.Data.Json

/-!
Run `lake env lean .github/upstream/Export.lean > .lake/upstream-current.json` after building the
tracked modules. Source ranges come from the running toolchain's declaration metadata, including
class fields and definition bodies. They are meaningful only at the accompanying Lean commit.
-/

open Lean RandomDo.Analogue

run_cmd do
  let env ← getEnv
  let mut entries : Array Json := #[]
  for (decl, _) in env.constants do
    if let some sources := analogueAttr.getParam? env decl then
      let some localIdx := env.getModuleIdxFor? decl
        | throwError "No module for tracked declaration `{decl}`"
      let localModule := env.header.moduleNames[localIdx.toNat]!
      for source in sources do
        let some idx := env.getModuleIdxFor? source
          | throwError "No module for upstream declaration `{source}`"
        let mod := env.header.moduleNames[idx.toNat]!
        unless [`Init, `Lean, `Std].any (·.isPrefixOf mod) do
          throwError "Analogue declaration `{source}` belongs to `{mod}`, not Lean core"
        let some ranges ← findDeclarationRanges? source
          | throwError "No source range for upstream declaration `{source}`"
        let first := ranges.range.pos.line
        let last := ranges.range.endPos.line - if ranges.range.endPos.column == 0 then 1 else 0
        entries := entries.push <| Json.mkObj [
          ("local", toJson decl.toString),
          ("local_file", toJson (localModule.toString.replace "." "/" ++ ".lean")),
          ("upstream", toJson source.toString),
          ("path", toJson ("src/" ++ mod.toString.replace "." "/" ++ ".lean")),
          ("start", toJson first), ("end", toJson last)]
  let result := Json.mkObj [
    ("schema", toJson (1 : Nat)), ("commit", toJson Lean.githash), ("entries", toJson entries)]
  IO.println result.compress
