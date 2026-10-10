import CoefficientwiseRigidity.CommonScalars

/-! The actual overlap matrix is the product of the two incidence matrices. -/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

theorem onLevel_incidenceLift {k : ℕ} {f : Space M} (hf : OnLevel k f) (j : ℕ) :
    OnLevel (k + j) (incidenceLift j f) := by
  exact (levelSpace M (k + j)).smul_mem _ (onLevel_raise hf j)

theorem onLevel_lower {k : ℕ} {f : Space M} (j : ℕ) (hf : OnLevel (k + j) f) :
    OnLevel k (lower j f) := by
  induction j generalizing f with
  | zero => simpa using hf
  | succ j ih =>
    rw [lower_succ]
    apply ih
    exact onLevel_down (by simpa only [Nat.add_assoc] using hf)

theorem onLevel_coIncidenceLift {k : ℕ} {f : Space M} (j : ℕ) (hf : OnLevel (k + j) f) :
    OnLevel k (coIncidenceLift j f) :=
  (levelSpace M k).smul_mem _ (onLevel_lower j hf)

def delta (A : Finset (Fin M)) : Space M := fun B => if B = A then 1 else 0

@[simp] theorem counting_delta (A : Finset (Fin M)) (f : Space M) :
    counting (delta A) f = f A := by simp [counting, delta]

theorem counting_restrict {q : ℕ} (g : Space M) {f : Space M} (hf : OnLevel q f) :
    counting g f = ∑ B : Kernel.Slice M q, g B.val * f B.val := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun A : Finset (Fin M) => A.card = q))
    (by simp) (fun A => g A * f A)]
  unfold counting
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro A _ hA
  have hne : A.card ≠ q := by simpa using hA
  rw [hf A hne, mul_zero]

theorem incidenceLift_delta {d q : ℕ} (hd : d ≤ q)
    (C : Finset (Fin M)) (hC : C.card = d) (B : Kernel.Slice M q) :
    incidenceLift (q - d) (delta C) B.val = if C ⊆ B.val then 1 else 0 := by
  rw [incidenceLift_apply (i := d) _ _ _ (by rw [B.property]; omega)]
  simp [delta, Finset.mem_powersetCard, hC]

/-- The transpose incidence sum is derived from counting adjointness. -/
theorem coIncidenceLift_apply {d q : ℕ} (hd : d ≤ q) {f : Space M}
    (hf : OnLevel q f) (C : Finset (Fin M)) (hC : C.card = d) :
    coIncidenceLift (q - d) f C =
      ∑ B : Kernel.Slice M q, if C ⊆ B.val then f B.val else 0 := by
  rw [← counting_delta C (coIncidenceLift (q - d) f),
    ← counting_incidence_adjoint, counting_restrict _ hf]
  apply Finset.sum_congr rfl
  intro B _
  rw [incidenceLift_delta hd C hC B]
  split_ifs <;> simp

theorem sum_incident_subsets (A B : Finset (Fin M)) (d : ℕ) (x : ℝ) :
    (∑ C ∈ A.powersetCard d, if C ⊆ B then x else 0) =
      ((A ∩ B).card.choose d : ℝ) * x := by
  rw [← Finset.sum_filter]
  have he : (A.powersetCard d).filter (fun C => C ⊆ B) = (A ∩ B).powersetCard d := by
    ext C
    simp [Finset.mem_powersetCard, Finset.subset_inter_iff, and_assoc, and_comm, and_left_comm]
  rw [he, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- An actual matrix, extended by zero off its output slice. -/
def overlapMatrix (p q d : ℕ) : Space M →ₗ[ℝ] Space M where
  toFun f A := if A.card = p then
    ∑ B : Kernel.Slice M q, ((A ∩ B.val).card.choose d : ℝ) * f B.val else 0
  map_add' f g := by ext A; by_cases hA : A.card = p <;> simp [hA, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext A; simp [Finset.mul_sum, mul_left_comm, mul_assoc]

theorem overlapMatrix_onLevel (p q d : ℕ) (f : Space M) :
    OnLevel p (overlapMatrix p q d f) := by
  intro A hA
  simp [overlapMatrix, hA]

/-- B_d = W_(p,d) W_(q,d)^*, proved for every vector on the input slice. -/
theorem overlapMatrix_factorization {p q d : ℕ} (hdp : d ≤ p) (hdq : d ≤ q)
    {f : Space M} (hf : OnLevel q f) :
    overlapMatrix p q d f = incidenceLift (p - d) (coIncidenceLift (q - d) f) := by
  have hl : OnLevel d (coIncidenceLift (q - d) f) :=
    onLevel_coIncidenceLift _ (by simpa only [Nat.add_sub_of_le hdq] using hf)
  have hu : OnLevel p (incidenceLift (p - d) (coIncidenceLift (q - d) f)) := by
    simpa only [Nat.add_sub_of_le hdp] using onLevel_incidenceLift hl (p - d)
  ext A
  by_cases hA : A.card = p
  · change (if A.card = p then _ else 0) = _
    rw [if_pos hA, incidenceLift_apply (i := d) _ _ A (by omega)]
    have he : (∑ C ∈ A.powersetCard d, coIncidenceLift (q - d) f C) =
        ∑ C ∈ A.powersetCard d,
          ∑ B : Kernel.Slice M q, if C ⊆ B.val then f B.val else 0 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact coIncidenceLift_apply hdq hf C (Finset.mem_powersetCard.mp hC).2
    rw [he, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B _
    exact (sum_incident_subsets A B.val d (f B.val)).symm
  · rw [overlapMatrix_onLevel p q d f A hA, hu A hA]

end
end CoefficientwiseRigidity.Spectral
