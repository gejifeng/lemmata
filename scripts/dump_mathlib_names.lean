import Mathlib

/-! Writes every declaration name in the Mathlib environment with its pretty-printed type to
`.work/mathlib_names.tsv` (one `name<TAB>type` line each). The prover uses this index to suggest real
names when Lean reports an unknown identifier, and to check that search results exist in this Mathlib version.
Run from the project root: `lake env lean scripts/dump_mathlib_names.lean` (takes 10-20 minutes). -/

open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  IO.FS.createDirAll ".work"
  let h ← IO.FS.Handle.mk ".work/mathlib_names.tsv" IO.FS.Mode.write
  let mut n := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    match ci with
    | .thmInfo _ | .defnInfo _ | .axiomInfo _ | .inductInfo _ | .ctorInfo _ | .opaqueInfo _ =>
      let ty ← (do let f ← ppExpr ci.type; pure (toString f)) <|> pure ""
      let ty := ty.replace "\n" " "
      h.putStrLn s!"{name}\t{if ty.length > 400 then ty.take 400 else ty}"
      n := n + 1
    | _ => pure ()
  IO.println s!"wrote {n} declarations to .work/mathlib_names.tsv"
