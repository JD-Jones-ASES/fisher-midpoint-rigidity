module
import Lean
import Lake.Check.Compare
meta import Lake.Check.Compare

/-! Run the toolchain's declaration comparison directly on the two independently
elaborated modules. The Linux workflow also checks the sandboxed exports. -/

open Lean

private def readModule (name : Name) : IO LeanExport.ExportedEnv := do
  let env ← importModules #[{ module := name }] {}
  let constants := env.constants.fold (init := ({} : Std.HashMap Name ConstantInfo))
    fun result key info => result.insert key info
  return { constMap := constants, constOrder := #[] }

public def main (names : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← readModule `Challenge
  let solution ← readModule `Solution
  IO.ofExcept <| Lake.Check.compareAt challenge solution (names.toArray.map String.toName) #[] #[]
