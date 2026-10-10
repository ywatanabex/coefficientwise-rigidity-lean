import CoefficientwiseRigidity.NewtonSplit
import CoefficientwiseRigidity.Slices

/-!
Kernel-checked finite boundary examples (VERIFIED only in their stated scope).
These prevent stronger, false interpretations of K1/K3; they are not premises
of the all-size proofs.
-/
namespace CoefficientwiseRigidity.Kernel

def badExtension (n : ℕ) : ℚ := if n ≤ 1 then (n : ℚ) else -100

theorem badExtension_in_cone : NewtonCone 1 badExtension := by
  apply (newtonCone_congr (f := badExtension) (g := fun n => (n.choose 1 : ℚ))
    (fun n hn => by simp [badExtension, hn])).mpr
  exact newtonCone_choose 1 1

theorem badExtension_not_in_larger_cone : ¬ NewtonCone 2 badExtension := by
  intro h
  have hp := newtonCone_nonneg h (le_refl 2)
  norm_num [badExtension] at hp

/-- Nonconstancy does not make every adjacent difference positive. -/
theorem lower_step_can_be_flat :
    NewtonCone 2 (fun n => (n.choose 2 : ℚ)) ∧
      ((0 : ℕ).choose 2 : ℚ) = (1 : ℕ).choose 2 ∧
      ((1 : ℕ).choose 2 : ℚ) < (2 : ℕ).choose 2 := by
  refine ⟨newtonCone_choose 2 2, ?_⟩
  norm_num

/-- Even with both inputs nonconstant, only the prioritized F branch must be strict. -/
theorem splitG_can_be_constant :
    splitG (fun n => (n : ℚ)) (fun n => (n : ℚ)) 0 =
      splitG (fun n => (n : ℚ)) (fun n => (n : ℚ)) 1 ∧
    splitF (fun n => (n : ℚ)) (fun n => (n : ℚ)) 0 <
      splitF (fun n => (n : ℚ)) (fun n => (n : ℚ)) 1 := by
  norm_num [splitF, splitG]

theorem dense_slice_has_shift : overlapShift 5 3 3 = 1 ∧ overlapRank 5 3 3 = 2 := by
  decide

end CoefficientwiseRigidity.Kernel
