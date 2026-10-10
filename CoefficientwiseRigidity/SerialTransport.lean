import CoefficientwiseRigidity.Slices
import Mathlib.Data.Finset.Sum

/-!
Concrete, unnormalized subset sums on arbitrary finite label types.
These lemmas prove radiality by an actual label bijection, not by an axiom
about matrices. They are part of the K2 formalization (paper status VERIFIED).
-/
namespace CoefficientwiseRigidity.Kernel
open Finset
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def setOverlap (A B : Finset α) : ℕ :=
  (A ∩ B).card - (A.card + B.card - Fintype.card α)

def setSerial (m : ℕ) (f g : ℕ → ℚ) (A B : Finset α) : ℚ :=
  ∑ C : Finset α, if C.card = m then f (setOverlap A C) * g (setOverlap C B) else 0

theorem setOverlap_lower (A B : Finset α) :
    A.card + B.card - Fintype.card α ≤ (A ∩ B).card := by
  have h := Finset.card_union_add_card_inter A B
  have hu := Finset.card_le_univ (A ∪ B)
  omega

theorem setOverlap_map (e : α ≃ β) (A B : Finset α) :
    setOverlap (A.map e.toEmbedding) (B.map e.toEmbedding) = setOverlap A B := by
  simp only [setOverlap, ← Finset.map_inter, Finset.card_map, Fintype.card_congr e]

theorem setSerial_map (e : α ≃ β) (m : ℕ) (f g : ℕ → ℚ) (A B : Finset α) :
    setSerial m f g (A.map e.toEmbedding) (B.map e.toEmbedding) = setSerial m f g A B := by
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro C
  simp only [Equiv.finsetCongr_apply, Finset.card_map, setOverlap_map]

def region (A B : Finset α) (x : α) : Bool × Bool := (decide (x ∈ A), decide (x ∈ B))

theorem region_card (A B : Finset α) (b c : Bool) :
    Fintype.card {x // region A B x = (b,c)} =
      ((if b then A else Aᶜ) ∩ (if c then B else Bᶜ)).card := by
  rw [Fintype.subtype_card]
  congr 1
  ext x
  cases b <;> cases c <;> simp [region]

theorem region_card_eq (A B : Finset α) (A' B' : Finset β)
    (hN : Fintype.card α = Fintype.card β) (hA : A.card = A'.card)
    (hB : B.card = B'.card) (hI : (A ∩ B).card = (A' ∩ B').card) (b c : Bool) :
    Fintype.card {x // region A B x = (b,c)} =
      Fintype.card {x // region A' B' x = (b,c)} := by
  rw [region_card, region_card]
  cases b <;> cases c <;> simp only [Bool.false_eq_true, if_false, if_true]
  · rw [← Finset.compl_union, ← Finset.compl_union, Finset.card_compl, Finset.card_compl]
    have h := Finset.card_union_add_card_inter A B
    have h' := Finset.card_union_add_card_inter A' B'
    omega
  · rw [Finset.inter_comm Aᶜ B, Finset.inter_comm A'ᶜ B',
      ← Finset.sdiff_eq_inter_compl, ← Finset.sdiff_eq_inter_compl]
    have h := Finset.card_inter_add_card_sdiff B A
    have h' := Finset.card_inter_add_card_sdiff B' A'
    rw [Finset.inter_comm B A] at h
    rw [Finset.inter_comm B' A'] at h'
    omega
  · rw [← Finset.sdiff_eq_inter_compl, ← Finset.sdiff_eq_inter_compl]
    have h := Finset.card_inter_add_card_sdiff A B
    have h' := Finset.card_inter_add_card_sdiff A' B'
    omega
  · exact hI

theorem exists_pair_equiv (A B : Finset α) (A' B' : Finset β)
    (hN : Fintype.card α = Fintype.card β) (hA : A.card = A'.card)
    (hB : B.card = B'.card) (hI : (A ∩ B).card = (A' ∩ B').card) :
    ∃ e : α ≃ β, A.map e.toEmbedding = A' ∧ B.map e.toEmbedding = B' := by
  classical
  let ef := fun bc : Bool × Bool =>
    Fintype.equivOfCardEq (region_card_eq A B A' B' hN hA hB hI bc.1 bc.2)
  let e : α ≃ β := Equiv.ofFiberEquiv ef
  have he : ∀ x, region A' B' (e x) = region A B x := Equiv.ofFiberEquiv_map ef
  have hmemA : ∀ x, e x ∈ A' ↔ x ∈ A := by
    intro x
    have h := congrArg Prod.fst (he x)
    simpa only [region, decide_eq_decide] using h
  have hmemB : ∀ x, e x ∈ B' ↔ x ∈ B := by
    intro x
    have h := congrArg Prod.snd (he x)
    simpa only [region, decide_eq_decide] using h
  refine ⟨e, ?_, ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa using (hmemA x).symm
  · ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa using (hmemB x).symm

theorem setSerial_eq_of_cards (m : ℕ) (f g : ℕ → ℚ) (A B : Finset α) (A' B' : Finset β)
    (hN : Fintype.card α = Fintype.card β) (hA : A.card = A'.card)
    (hB : B.card = B'.card) (hI : (A ∩ B).card = (A' ∩ B').card) :
    setSerial m f g A B = setSerial m f g A' B' := by
  obtain ⟨e, heA, heB⟩ := exists_pair_equiv A B A' B' hN hA hB hI
  rw [← heA, ← heB, setSerial_map]

theorem setOverlap_slice {M p q : ℕ} (A : Slice M p) (B : Slice M q) :
    setOverlap A.val B.val = overlap A B := by
  simp only [setOverlap, overlap, overlapShift, A.property, B.property, Fintype.card_fin]

theorem serial_eq_setSerial {M p m q : ℕ} (f g : ℕ → ℚ) (A : Slice M p) (B : Slice M q) :
    serial (m := m) f g A B = setSerial m f g A.val B.val := by
  classical
  unfold serial setSerial
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun C _ => C.val)
  · intro C _; simp [C.property]
  · intro C _ D _ h; exact Subtype.ext h
  · intro C hC; exact ⟨⟨C, by simpa using hC⟩, Finset.mem_univ _, rfl⟩
  · intro C _
    rw [setOverlap_slice A C, setOverlap_slice C B]

theorem serial_radial {M p m q : ℕ} (f g : ℕ → ℚ) (A A' : Slice M p) (B B' : Slice M q)
    (hz : overlap A B = overlap A' B') :
    serial (m := m) f g A B = serial (m := m) f g A' B' := by
  rw [serial_eq_setSerial, serial_eq_setSerial]
  apply setSerial_eq_of_cards m f g A.val B.val A'.val B'.val rfl
    (A.property.trans A'.property.symm) (B.property.trans B'.property.symm)
  have h := overlap_lower A B
  have h' := overlap_lower A' B'
  dsimp [overlap] at hz
  omega

theorem serial_nonneg {M p m q : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone (overlapRank M p m) f) (hg : NewtonCone (overlapRank M m q) g)
    (A : Slice M p) (B : Slice M q) : 0 ≤ serial (m := m) f g A B := by
  apply Finset.sum_nonneg
  intro C _
  exact mul_nonneg (newtonCone_nonneg hf (overlap_le_rank A C))
    (newtonCone_nonneg hg (overlap_le_rank C B))

/-- Radiality is established before and independently of Newton positivity. -/
theorem exists_serial_profile {M p m q : ℕ} (hp : p ≤ M) (hq : q ≤ M) (f g : ℕ → ℚ) :
    ∃ h : ℕ → ℚ, ∀ (A : Slice M p) (B : Slice M q),
      serial (m := m) f g A B = h (overlap A B) := by
  classical
  let A₀ : Slice M p := ⟨initialSegment M p, card_prefix M p hp⟩
  let h : ℕ → ℚ := fun z => if hz : z ≤ overlapRank M p q then
    serial (m := m) f g A₀ (Classical.choose (exists_overlap A₀ hq z hz)) else 0
  refine ⟨h, ?_⟩
  intro A B
  dsimp [h]
  rw [dif_pos (overlap_le_rank A B)]
  apply serial_radial
  exact (Classical.choose_spec (exists_overlap A₀ hq (overlap A B) (overlap_le_rank A B))).symm

theorem serial_profile_nonneg {M p m q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g h : ℕ → ℚ} (hf : NewtonCone (overlapRank M p m) f)
    (hg : NewtonCone (overlapRank M m q) g)
    (hh : ∀ (A : Slice M p) (B : Slice M q), serial (m := m) f g A B = h (overlap A B))
    {z : ℕ} (hz : z ≤ overlapRank M p q) : 0 ≤ h z := by
  let A : Slice M p := ⟨initialSegment M p, card_prefix M p hp⟩
  obtain ⟨B, hB⟩ := exists_overlap A hq z hz
  rw [← hB, ← hh A B]
  exact serial_nonneg hf hg A B

theorem setSerial_of_profile {M p m q : ℕ} {f g h : ℕ → ℚ}
    (hh : ∀ (A : Slice M p) (B : Slice M q), serial (m := m) f g A B = h (overlap A B))
    (A B : Finset α) (hN : Fintype.card α = M) (hA : A.card = p) (hB : B.card = q) :
    setSerial m f g A B = h (setOverlap A B) := by
  classical
  let e : α ≃ Fin M := Fintype.equivOfCardEq (by simpa using hN)
  let A' : Slice M p := ⟨A.map e.toEmbedding, by simpa using hA⟩
  let B' : Slice M q := ⟨B.map e.toEmbedding, by simpa using hB⟩
  calc
    setSerial m f g A B = setSerial m f g A'.val B'.val := (setSerial_map e m f g A B).symm
    _ = serial (m := m) f g A' B' := (serial_eq_setSerial f g A' B').symm
    _ = h (overlap A' B') := hh A' B'
    _ = h (setOverlap A B) := by rw [← setOverlap_slice]; congr 1; exact setOverlap_map e A B

end CoefficientwiseRigidity.Kernel
