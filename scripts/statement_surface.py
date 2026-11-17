#!/usr/bin/env python3
"""Inventory the custom statement vocabulary; this is not Comparator evidence.

Adapted from the MIT-licensed Special transformations submission workflow.
Run with the pinned Lake environment after building FubiniTheorems.
"""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.scratch/palomar'
OUT.mkdir(parents=True, exist_ok=True)
SOURCE = r'''
import FubiniTheorems.Fubini.Section5DischargedInputs
import Lean
import Lean.Util.FoldConsts
open Lean
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  let root := `DiamondIntegral.Section5.bounded_fubini_discharged
  let mut todo := #[root]
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!.toString
    let allowed := ["Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop",
      "Qq", "LeanSearchClient", "ImportGraph", "Plausible", "ProofWidgets"]
    if allowed.any (fun p => modName == p || modName.startsWith (p ++ ".")) then continue
    for dependency in info.type.getUsedConstants do
      todo := todo.push dependency
    let (kind, value) := match info with
      | .defnInfo val => ("definition", some val.value)
      | .thmInfo _ => ("theorem", none)
      | .inductInfo _ => ("inductive", none)
      | .ctorInfo _ => ("constructor", none)
      | .recInfo _ => ("recursor", none)
      | _ => ("other", none)
    if let some value := value then
      for dependency in value.getUsedConstants do
        todo := todo.push dependency
    if let .inductInfo val := info then
      for constructor in val.ctors do
        todo := todo.push constructor
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson modName),
      ("kind", toJson kind), ("headline", toJson (name == root))]
  liftM <| IO.FS.writeFile ".scratch/palomar/statement-surface.json"
    (Json.pretty <| Json.mkObj [("declarations", Json.arr rows),
      ("count", toJson rows.size),
      ("scope", toJson "Custom type/definition closure only; not extraction or verification")])
'''
(OUT / 'StatementSurface.lean').write_text(SOURCE)
result = subprocess.run(['lake', 'env', 'lean', str(OUT / 'StatementSurface.lean')],
                        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(OUT / 'statement-surface.log').write_text(result.stdout)
print(result.stdout, end='')
sys.exit(result.returncode)
