import CoefficientwiseRigidity
import Lean.Util.CollectAxioms

/-!
Fail the default build if ANY kernel-safe declaration in this project's namespace depends
on a nonstandard axiom. This checks definitions as well as named theorems,
including the mathematical statements themselves. Compiler-generated unsafe
implementations are not proof terms. In particular sorryAx and
native evaluation axioms are forbidden. It does not turn a Prop target into a proof.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if (`CoefficientwiseRigidity).isPrefixOf name && !info.isUnsafe then
      checked := checked + 1
      if info.isTheorem then
        theorems := theorems + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
  if checked == 0 then
    throwError "Audit found no project declarations"
  logInfo m!"Axiom audit PASS: {checked} project declarations, {theorems} theorem declarations; only propext, Classical.choice, Quot.sound allowed."

#print axioms CoefficientwiseRigidity.coefficient_eq_projected_lift
#print axioms CoefficientwiseRigidity.ordinary_eq_polynomial_coefficient
#print axioms CoefficientwiseRigidity.paperReserve_eq_polynomial_coefficient
#print axioms CoefficientwiseRigidity.coefficient_kappa_paperReserve
#print axioms CoefficientwiseRigidity.paperMainBSharpness
#print axioms CoefficientwiseRigidity.paperMainCRelative
#print axioms CoefficientwiseRigidity.paperMainCQuantitativeReal
#print axioms CoefficientwiseRigidity.manuscriptMainTheorems
#check CoefficientwiseRigidity.manuscriptMainTheorems
