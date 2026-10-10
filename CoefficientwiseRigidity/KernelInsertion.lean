import CoefficientwiseRigidity.GainKernels

/-!
W2's literal two-label insertion, finite-sum injection and leaf row inequality.
Only the ordinary companion is compared: a gain need not preserve the inserted label.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset
noncomputable section
variable {M p q : ℕ}

def insertionLabels (M : ℕ) : Fin M ⊕ Bool ≃ Fin (M + 2) :=
  Fintype.equivOfCardEq (by simp)

/-- Insert the same new label at every vertex and omit the other new label. -/
def insertSlice (A : Slice M p) : Slice (M + 2) (p + 1) :=
  ⟨(liftSet A.val false).map (insertionLabels M).toEmbedding,
    by simp [card_liftSet, A.property]⟩

theorem insertSlice_injective : Function.Injective (@insertSlice M p) := by
  intro A B h
  have hm : liftSet A.val false = liftSet B.val false :=
    Finset.map_injective _ (congrArg Subtype.val h)
  apply Subtype.ext
  simpa [liftSet] using congrArg Finset.toLeft hm

@[simp] theorem overlap_insertSlice (A : Slice M p) (B : Slice M q) :
    overlap (insertSlice A) (insertSlice B) = overlap A B + 1 := by
  rw [← setOverlap_slice, ← setOverlap_slice A B]
  change setOverlap ((liftSet A.val false).map (insertionLabels M).toEmbedding)
    ((liftSet B.val false).map (insertionLabels M).toEmbedding) = _
  rw [setOverlap_map, setOverlap_lift]
  simp

theorem exists_permuteSlice_eq (A B : Slice M p) :
    ∃ σ : Equiv.Perm (Fin M), permuteSlice σ A = B := by
  obtain ⟨σ, hσ, _⟩ := exists_pair_equiv A.val A.val B.val B.val rfl
    (by rw [A.property, B.property]) (by rw [A.property, B.property])
    (by simp [A.property, B.property])
  exact ⟨σ, Subtype.ext hσ⟩

/-- The reduced entry records only the ordinary forward difference. -/
def GainEntry.reduce (e : GainEntry (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) : GainEntry M p q where
  profile := delta e.profile
  cone := newtonCone_delta (by rw [← overlapRank_reduce hp hq]; exact e.cone)
  gain := Equiv.refl _

theorem GainEntry.reduce_insertion (e : GainEntry (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) (A : Slice M p) (B : Slice M q) :
    (e.reduce hp hq).ordinary A B ≤ e.ordinary (insertSlice A) (insertSlice B) := by
  have hz : overlap A B ≤ overlapRank (M + 2) (p + 1) (q + 1) := by
    rw [overlapRank_reduce hp hq]
    exact (overlap_le_rank A B).trans (Nat.le_succ _)
  have hn := newtonCone_nonneg e.cone hz
  simp only [GainEntry.ordinary, GainEntry.reduce, overlap_insertSlice, delta, fwdDiff]
  linarith

def reduceList (L : GainList (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) : GainList M p q :=
  L.map fun e => e.reduce hp hq

theorem reduceList_insertion (L : GainList (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) (A : Slice M p) (B : Slice M q) :
    listOrdinary (reduceList L hp hq) A B ≤
      listOrdinary L (insertSlice A) (insertSlice B) := by
  induction L with
  | nil => exact le_refl _
  | cons e L ih =>
    exact add_le_add (e.reduce_insertion hp hq A B) ih

/-- An injective map into a larger finite space can only increase a nonnegative sum. -/
theorem sum_le_of_injection {α β : Type*} [Fintype α] [Fintype β]
    (i : α → β) (hi : Function.Injective i) (f : α → ℚ) (g : β → ℚ)
    (hg : ∀ b, 0 ≤ g b) (hfg : ∀ a, f a ≤ g (i a)) :
    ∑ a, f a ≤ ∑ b, g b := by
  classical
  calc
    ∑ a, f a ≤ ∑ a, g (i a) := Finset.sum_le_sum fun a _ => hfg a
    _ = ∑ b ∈ univ.map ⟨i, hi⟩, g b := by simp
    _ ≤ ∑ b, g b := Finset.sum_le_univ_sum_of_nonneg hg

/-- W2 for a leaf, with no extra binomial or slice-cardinality normalization. -/
theorem rowMass_reduce_le (L : GainList (M + 2) (p + 1) (q + 1))
    (hp : p ≤ M) (hq : q ≤ M) :
    rowMass hp (reduceList L hp hq) ≤ rowMass (by omega : p + 1 ≤ M + 2) L := by
  let A : Slice M p := ⟨initialSegment M p, card_prefix M p hp⟩
  rw [← list_ordinary_rowMass hp _ A,
    ← list_ordinary_rowMass (by omega : p + 1 ≤ M + 2) L (insertSlice A)]
  exact sum_le_of_injection insertSlice insertSlice_injective _ _
    (fun B => listOrdinary_nonneg L _ B) (reduceList_insertion L hp hq A)

end
end CoefficientwiseRigidity.Kernel
