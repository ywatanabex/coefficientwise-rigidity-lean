import CoefficientwiseRigidity.ColumnAssignments

/-! Linearity and on-slice congruence for the exact column sums. -/
namespace CoefficientwiseRigidity.Intersections
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] {M : ℕ}

theorem sumSet_congr_valid (q : V → ℕ) (U : Finset V)
    {F G : (V → Finset (Fin M)) → ℚ} (Q : V → Finset (Fin M))
    (h : ∀ S, ValidOn q U Q S → F S = G S) : sumSet q U F Q = sumSet q U G Q := by
  simp only [sumSet_eq_assignment_sum]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs with hs
  · exact h S hs
  · rfl

theorem sumSet_congr_ranks (q r : V → ℕ) (U : Finset V)
    (h : ∀ v ∈ U, q v = r v) (F : (V → Finset (Fin M)) → ℚ)
    (Q : V → Finset (Fin M)) : sumSet q U F Q = sumSet r U F Q := by
  simp only [sumSet_eq_assignment_sum]
  have he (S : V → Finset (Fin M)) : ValidOn q U Q S ↔ ValidOn r U Q S := by
    unfold ValidOn
    constructor <;> intro hs
    · exact ⟨fun v hv => by rw [← h v hv]; exact hs.1 v hv,hs.2⟩
    · exact ⟨fun v hv => by rw [h v hv]; exact hs.1 v hv,hs.2⟩
  simp_rw [he]

theorem sumSet_add (q : V → ℕ) (U : Finset V)
    (F G : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumSet q U (fun S => F S + G S) Q = sumSet q U F Q + sumSet q U G Q := by
  simp only [sumSet_eq_assignment_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem sumSet_sub (q : V → ℕ) (U : Finset V)
    (F G : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumSet q U (fun S => F S - G S) Q = sumSet q U F Q - sumSet q U G Q := by
  simp only [sumSet_eq_assignment_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem sumSet_mul (q : V → ℕ) (U : Finset V) (c : ℚ)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumSet q U (fun S => c * F S) Q = c * sumSet q U F Q := by
  simp only [sumSet_eq_assignment_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

omit [Fintype V] in
theorem sumSet_sum {T : Type*} (s : Finset T) (q : V → ℕ) (U : Finset V)
    (F : T → (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumSet q U (fun S => ∑ t ∈ s, F t S) Q = ∑ t ∈ s, sumSet q U (F t) Q :=
  sumColumns_sum s q U.toList F Q

end
end CoefficientwiseRigidity.Intersections
