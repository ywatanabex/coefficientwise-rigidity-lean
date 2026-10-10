import CoefficientwiseRigidity.NormalizedBlocks

/-! Identify the factorial-scaled raising maps with actual subset-incidence sums. -/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

def subsetSum (i : ℕ) (f : Space M) (A : Finset (Fin M)) : ℝ :=
  ∑ B ∈ A.powersetCard i, f B

theorem up_apply_mem (f : Space M) (A : Finset (Fin M)) :
    up f A = ∑ x ∈ A, f (A.erase x) := by
  simp [up_apply]

theorem powersetCard_erase_filter (i : ℕ) (A : Finset (Fin M)) (x : Fin M) :
    (A.erase x).powersetCard i = (A.powersetCard i).filter (fun B => x ∉ B) := by
  ext B
  simp [Finset.mem_powersetCard, Finset.subset_erase, and_assoc, and_left_comm, and_comm]

/-- Each i-subset B is counted once for every removed label in A minus B. -/
theorem up_subsetSum (i : ℕ) (f : Space M) (A : Finset (Fin M)) :
    up (subsetSum i f) A = ((A.card - i : ℕ) : ℝ) * subsetSum i f A := by
  rw [up_apply_mem]
  simp_rw [subsetSum, powersetCard_erase_filter, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hB
  rw [← Finset.sum_filter]
  have he : A.filter (fun x => x ∉ B) = A \ B := by ext x; simp
  rw [he, Finset.sum_const, Finset.card_sdiff hsub, hcard, nsmul_eq_mul]

theorem raise_apply_card {i : ℕ} (f : Space M)
    (j : ℕ) (A : Finset (Fin M)) (hA : A.card = i + j) :
    raise j f A = (j.factorial : ℝ) * subsetSum i f A := by
  induction j generalizing A with
  | zero =>
    have hc : A.card = i := by simpa using hA
    simp [subsetSum, ← hc]
  | succ j ih =>
    rw [raise_succ, up_apply_mem]
    have hsum : (∑ x ∈ A, raise j f (A.erase x)) =
        (j.factorial : ℝ) * up (subsetSum i f) A := by
      rw [up_apply_mem, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      exact ih (A.erase x) (by rw [Finset.card_erase_of_mem hx, hA]; omega)
    rw [hsum, up_subsetSum, hA]
    have he : i + (j + 1) - i = j + 1 := by omega
    rw [he, Nat.factorial_succ]
    push_cast
    ring

/-- The actual incidence sum, not just a formally normalized abstract operator. -/
theorem incidenceLift_apply {i : ℕ} (f : Space M)
    (j : ℕ) (A : Finset (Fin M)) (hA : A.card = i + j) :
    incidenceLift j f A = ∑ B ∈ A.powersetCard i, f B := by
  change (j.factorial : ℝ)⁻¹ * raise j f A = _
  rw [raise_apply_card f j A hA, ← mul_assoc, inv_mul_cancel₀, one_mul]
  · rfl
  · exact_mod_cast j.factorial_ne_zero

/-- The powerset counting form restricts to exactly the paper's slice sum. -/
theorem counting_level {k : ℕ} (f g : levelSpace M k) :
    counting f.val g.val = ∑ A : Kernel.Slice M k, f.val A.val * g.val A.val := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun A : Finset (Fin M) => A.card = k))
    (by simp) (fun A => f.val A * g.val A)]
  unfold counting
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro A _ hA
  have hne : A.card ≠ k := by simpa using hA
  rw [f.property A hne, zero_mul]

end
end CoefficientwiseRigidity.Spectral
