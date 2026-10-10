import CoefficientwiseRigidity.KernelInsertion

/-!
W1/W3 invariants for the actual serial and parallel entries: exact reduced
serial sums, nonconstancy after serial composition, and the split reserve.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset
noncomputable section
variable {M p m q : ℕ}

def prefixSlice (M p : ℕ) (hp : p ≤ M) : Slice M p :=
  ⟨initialSegment M p, card_prefix M p hp⟩

theorem overlap_prefixSlice (hp : p ≤ M) (hq : q ≤ M) :
    overlap (prefixSlice M p hp) (prefixSlice M q hq) = overlapRank M p q := by
  have hi : initialSegment M p ∩ initialSegment M q = initialSegment M (min p q) := by
    ext i
    simp [lt_min_iff]
  simp only [overlap, prefixSlice, hi, card_prefix M (min p q) ((min_le_left _ _).trans hp)]
  rfl

def GainEntry.Nonconstant (e : GainEntry M p q) : Prop :=
  ∃ n, n ≤ overlapRank M p q ∧ e.profile n ≠ e.profile 0

theorem GainEntry.endpoint_pos (e : GainEntry M p q) (he : e.Nonconstant) :
    0 < e.profile (overlapRank M p q) := newtonCone_endpoint_pos e.cone he

theorem GainEntry.reduce_endpoint_pos (e : GainEntry (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) (he : e.Nonconstant) :
    0 < (e.reduce hp hq).profile (overlapRank M p q) := by
  have hc := e.cone
  unfold GainEntry.Nonconstant at he
  rw [overlapRank_reduce hp hq] at hc he
  exact sub_pos.mpr ((newtonCone_last_strict_iff hc).mpr he)

/-- W1 applied to the particular profile selected by `GainEntry.compose`. -/
theorem GainEntry.compose_reduce_ordinary
    (e : GainEntry (M + 2) (p + 1) (m + 1))
    (f : GainEntry (M + 2) (m + 1) (q + 1))
    (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M) (A : Slice M p) (B : Slice M q) :
    ((e.compose (by omega) (by omega) (by omega) f).reduce hp hq).ordinary A B =
      ∑ C : Slice M m, (e.reduce hp hm).ordinary A C * (f.reduce hm hq).ordinary C B := by
  apply serial_profile_difference
  intro C D
  exact (e.compose_ordinary (by omega) (by omega) (by omega) f C D).symm

/-- Serial elimination of two nonconstant interior entries preserves nonconstancy. -/
theorem GainEntry.compose_nonconstant
    (e : GainEntry (M + 2) (p + 1) (m + 1))
    (f : GainEntry (M + 2) (m + 1) (q + 1))
    (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (he : e.Nonconstant) (hf : f.Nonconstant) :
    (e.compose (by omega) (by omega) (by omega) f).Nonconstant := by
  classical
  let h := e.compose (by omega) (by omega) (by omega) f
  have hc := h.cone
  rw [overlapRank_reduce hp hq] at hc
  change ∃ n, n ≤ overlapRank (M + 2) (p + 1) (q + 1) ∧ h.profile n ≠ h.profile 0
  rw [overlapRank_reduce hp hq, ← newtonCone_last_strict_iff hc]
  apply sub_pos.mp
  change 0 < delta h.profile (overlapRank M p q)
  rw [← overlap_prefixSlice hp hq]
  change 0 < (h.reduce hp hq).ordinary (prefixSlice M p hp) (prefixSlice M q hq)
  rw [GainEntry.compose_reduce_ordinary e f hp hm hq]
  apply Finset.sum_pos'
  · intro C _
    exact mul_nonneg ((e.reduce hp hm).ordinary_nonneg _ C)
      ((f.reduce hm hq).ordinary_nonneg C _)
  · refine ⟨prefixSlice M m hm, mem_univ _, ?_⟩
    simp only [GainEntry.ordinary, overlap_prefixSlice]
    exact mul_pos (e.reduce_endpoint_pos hp hm he) (f.reduce_endpoint_pos hm hq hf)

theorem GainEntry.splitLeft_reduce_reserve
    (e f : GainEntry (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) (A : Slice M p) (B : Slice M q) :
    (e.reduce hp hq).ordinary A B * (f.reduce hp hq).ordinary A B ≤
      ((e.splitLeft f).reduce hp hq).ordinary A B := by
  apply newton_splitF_reserve
  · rw [← overlapRank_reduce hp hq]
    exact e.cone
  · rw [← overlapRank_reduce hp hq]
    exact f.cone
  · exact overlap_le_rank A B

theorem GainEntry.splitLeft_nonconstant
    (e f : GainEntry (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) (he : e.Nonconstant) (hf : f.Nonconstant) :
    (e.splitLeft f).Nonconstant := by
  have hc := e.cone
  have hd := f.cone
  unfold GainEntry.Nonconstant at *
  rw [overlapRank_reduce hp hq] at hc hd he hf ⊢
  apply (newtonCone_last_strict_iff (newtonCone_splitF hc hd)).mp
  exact newton_splitF_last_strict hc hd he hf

end
end CoefficientwiseRigidity.Kernel
