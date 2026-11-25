import AbhiLib
import Lean
open Lean Elab Command

elab "#auditLibrary" : command => do
  for (n, info) in (← getEnv).constants.toList do
    if !(`AbhiLib).isPrefixOf n then continue
    if !(info matches .thmInfo _) then continue
    for ax in ← collectAxioms n do
      unless #[`propext, `Quot.sound, `Classical.choice].contains ax do
        throwError "{n} depends on {ax}"

elab "#entry " id:ident : command => do
  let n ← resolveGlobalConstNoOverload id
  let info ← getConstInfo n
  let names (e : Expr) := (e.getUsedConstants.filter (fun k => (`AbhiLib).isPrefixOf k)).map toString
  let axioms ← collectAxioms n
  for ax in axioms do
    unless #[`propext, `Quot.sound, `Classical.choice].contains ax do
      throwError "{n} depends on {ax}"
  let some mod ← findModuleOf? n | throwError "Missing module for {n}"
  let some loc ← findDeclarationRanges? n | throwError "Missing source range for {n}"
  liftIO <| IO.println <| Json.compress <| Json.mkObj [
    ("module", toJson mod.toString), ("start", toJson loc.selectionRange.pos.line),
    ("end", toJson loc.range.endPos.line), ("name", toJson n.toString), ("body", toJson (info.value?.map names |>.getD #[])),
    ("type", toJson (names info.type)), ("axioms", toJson (axioms.map toString))]
