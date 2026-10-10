import CoefficientwiseRigidity.GainKernels

/-!
Kernel-checked counterexample to replacing gain-list data by its evaluated
matrix: identical gained matrices can have different ordinary companions.
-/
namespace CoefficientwiseRigidity.Kernel.Boundary

def identityEntry : GainEntry 2 1 1 :=
  ⟨fun z => (z.choose 1 : ℚ), newtonCone_choose _ _, Equiv.refl _⟩

def swapEntry : GainEntry 2 1 1 :=
  ⟨fun z => (z.choose 1 : ℚ), newtonCone_choose _ _, Equiv.swap 0 1⟩

def unitEntry : GainEntry 2 1 1 :=
  ⟨fun _ => 1, newtonCone_const _ _ zero_le_one, Equiv.refl _⟩

def zeroSingleton : Slice 2 1 := ⟨{0}, by decide⟩

theorem same_gained_matrix : ∀ A B : Slice 2 1,
    listValue [identityEntry, swapEntry] A B = listValue [unitEntry] A B := by
  intro A B
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp A.property
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp B.property
  fin_cases i <;> fin_cases j <;>
    norm_num [listValue, GainEntry.value, identityEntry, swapEntry, unitEntry,
      overlap, overlapShift, permuteSlice, hi, hj, Equiv.swap_apply_def]

theorem different_companions :
    listOrdinary [identityEntry, swapEntry] zeroSingleton zeroSingleton = 2 ∧
    listOrdinary [unitEntry] zeroSingleton zeroSingleton = 1 := by
  norm_num [listOrdinary, GainEntry.ordinary, identityEntry, swapEntry, unitEntry,
    zeroSingleton, overlap, overlapShift]

/-- The companion must remain attached to its chosen list, not only its matrix. -/
theorem gained_matrix_does_not_determine_companion :
    ∃ L K : GainList 2 1 1, (∀ A B, listValue L A B = listValue K A B) ∧
      ∃ A B, listOrdinary L A B ≠ listOrdinary K A B := by
  refine ⟨[identityEntry, swapEntry], [unitEntry], same_gained_matrix,
    zeroSingleton, zeroSingleton, ?_⟩
  rw [different_companions.1, different_companions.2]
  norm_num

end CoefficientwiseRigidity.Kernel.Boundary
