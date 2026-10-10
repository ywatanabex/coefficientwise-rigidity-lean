import CoefficientwiseRigidity.Feasibility
import CoefficientwiseRigidity.Newton

/-!
Paper K1/K4 (VERIFIED paper results): actual finite subset slices, the shifted
overlap coordinate, its exact range, complement symmetry, and the top basis.
In particular, dense slices are shifted; unshifted serial closure is not assumed.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset

abbrev Slice (M p : ℕ) := {A : Finset (Fin M) // A.card = p}

theorem slice_card (M p : ℕ) : Fintype.card (Slice M p) = M.choose p := by
  simp [Slice]

def overlapShift (M p q : ℕ) : ℕ := p + q - M
def overlapRank (M p q : ℕ) : ℕ := min p q - overlapShift M p q
def overlap {M p q : ℕ} (A : Slice M p) (B : Slice M q) : ℕ :=
  (A.val ∩ B.val).card - overlapShift M p q

theorem slice_rank_le {M p : ℕ} (A : Slice M p) : p ≤ M := by
  have h := Finset.card_le_univ A.val
  simpa [A.property] using h

theorem overlapShift_le_min {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M) :
    overlapShift M p q ≤ min p q := by
  simp only [overlapShift]
  omega

theorem overlap_lower {M p q : ℕ} (A : Slice M p) (B : Slice M q) :
    overlapShift M p q ≤ (A.val ∩ B.val).card := by
  have h := Finset.card_union_add_card_inter A.val B.val
  have hu : (A.val ∪ B.val).card ≤ M := by simpa using Finset.card_le_univ (A.val ∪ B.val)
  rw [A.property, B.property] at h
  dsimp [overlapShift]
  omega

theorem overlap_upper {M p q : ℕ} (A : Slice M p) (B : Slice M q) :
    (A.val ∩ B.val).card ≤ min p q := by
  have hA := Finset.card_le_card (Finset.inter_subset_left : A.val ∩ B.val ⊆ A.val)
  have hB := Finset.card_le_card (Finset.inter_subset_right : A.val ∩ B.val ⊆ B.val)
  rw [A.property] at hA
  rw [B.property] at hB
  exact le_min hA hB

theorem overlap_le_rank {M p q : ℕ} (A : Slice M p) (B : Slice M q) :
    overlap A B ≤ overlapRank M p q := Nat.sub_le_sub_right (overlap_upper A B) _

theorem overlap_symm {M p q : ℕ} (A : Slice M p) (B : Slice M q) :
    overlap A B = overlap B A := by
  simp only [overlap, overlapShift, Finset.inter_comm, Nat.add_comm]

def complementSlice {M p : ℕ} (A : Slice M p) : Slice M (M - p) :=
  ⟨A.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, A.property]⟩

theorem overlap_complement {M p q : ℕ} (A : Slice M p) (B : Slice M q) :
    overlap (complementSlice A) (complementSlice B) = overlap A B := by
  have hp := slice_rank_le A
  have hq := slice_rank_le B
  have h := Finset.card_union_add_card_inter A.val B.val
  have hu : (A.val ∪ B.val).card ≤ M := by simpa using Finset.card_le_univ (A.val ∪ B.val)
  rw [A.property, B.property] at h
  have hcomp : (A.valᶜ ∩ B.valᶜ).card = M - (A.val ∪ B.val).card := by
    rw [← Finset.compl_union, Finset.card_compl, Fintype.card_fin]
  dsimp [overlap, complementSlice, overlapShift]
  rw [hcomp]
  omega

/-- Every coordinate in the claimed interval occurs, for each fixed first set. -/
theorem exists_overlap {M p q : ℕ} (A : Slice M p) (hq : q ≤ M)
    (z : ℕ) (hz : z ≤ overlapRank M p q) : ∃ B : Slice M q, overlap A B = z := by
  classical
  let t := overlapShift M p q + z
  have hp := slice_rank_le A
  have hs := overlapShift_le_min hp hq
  have htmin : t ≤ min p q := by dsimp [t, overlapRank] at *; omega
  have htA : t ≤ A.val.card := by rw [A.property]; exact htmin.trans (min_le_left _ _)
  have htq : t ≤ q := htmin.trans (min_le_right _ _)
  have hremaining : q - t ≤ A.valᶜ.card := by
    simp only [Finset.card_compl, Fintype.card_fin, A.property]
    dsimp [t, overlapShift]
    omega
  obtain ⟨D, hDA, hD⟩ := Finset.exists_subset_card_eq htA
  obtain ⟨E, hEA, hE⟩ := Finset.exists_subset_card_eq hremaining
  have hdis : Disjoint D E := by
    rw [Finset.disjoint_left]
    intro i hiD hiE
    exact (Finset.mem_compl.mp (hEA hiE)) (hDA hiD)
  have hcard : (D ∪ E).card = q := by rw [Finset.card_union_of_disjoint hdis, hD, hE]; omega
  have hinter : A.val ∩ (D ∪ E) = D := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_inter.mp hi with ⟨hiA, hi⟩
      rcases Finset.mem_union.mp hi with hiD | hiE
      · exact hiD
      · exact False.elim ((Finset.mem_compl.mp (hEA hiE)) hiA)
    · intro hi
      exact Finset.mem_inter.mpr ⟨hDA hi, Finset.mem_union_left _ hi⟩
  refine ⟨⟨D ∪ E, hcard⟩, ?_⟩
  simp only [overlap, hinter, hD]
  dsimp [t]
  omega

theorem overlap_eq_rank_iff_subset {M p q : ℕ} (A : Slice M p) (B : Slice M q)
    (hpq : p ≤ q) : overlap A B = overlapRank M p q ↔ A.val ⊆ B.val := by
  have hlo := overlap_lower A B
  have hup := overlap_upper A B
  have hmin : min p q = p := min_eq_left hpq
  constructor
  · intro h
    have hc : (A.val ∩ B.val).card = A.val.card := by
      rw [A.property]
      dsimp [overlap, overlapRank] at h
      rw [hmin] at h hup
      omega
    have he := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hc.ge
    rw [← he]
    exact Finset.inter_subset_right
  · intro h
    simp [overlap, overlapRank, Finset.inter_eq_left.mpr h, A.property, hmin]

/-- The actual inclusion factor is the top Newton basis, including rank zero. -/
theorem top_basis_inclusion {M p q : ℕ} (A : Slice M p) (B : Slice M q) (hpq : p ≤ q) :
    ((overlap A B).choose (overlapRank M p q) : ℚ) = if A.val ⊆ B.val then 1 else 0 := by
  classical
  by_cases h : A.val ⊆ B.val
  · rw [if_pos h, (overlap_eq_rank_iff_subset A B hpq).mpr h, Nat.choose_self, Nat.cast_one]
  · rw [if_neg h]
    have hne : overlap A B ≠ overlapRank M p q :=
      fun he => h ((overlap_eq_rank_iff_subset A B hpq).mp he)
    rw [Nat.choose_eq_zero_of_lt (lt_of_le_of_ne (overlap_le_rank A B) hne), Nat.cast_zero]

theorem inclusion_kernel_newton (M p q : ℕ) (hpq : p ≤ q) :
    ∃ f : ℕ → ℚ, NewtonCone (overlapRank M p q) f ∧
      ∀ (A : Slice M p) (B : Slice M q), f (overlap A B) = if A.val ⊆ B.val then 1 else 0 :=
  ⟨fun z => (z.choose (overlapRank M p q) : ℚ),
    newtonCone_choose _ _, fun A B => top_basis_inclusion A B hpq⟩

theorem overlap_zero_right {M p : ℕ} (A : Slice M p) (C : Slice M 0) : overlap A C = 0 := by
  have hc : C.val = ∅ := Finset.card_eq_zero.mp C.property
  simp [overlap, hc]

theorem overlap_full_right {M p : ℕ} (A : Slice M p) (C : Slice M M) : overlap A C = 0 := by
  have hc : C.val = Finset.univ := Finset.eq_univ_of_card C.val (by simpa using C.property)
  simp [overlap, overlapShift, hc, A.property]

/-- The concrete slice sum in K2; general serial closure is not an axiom. -/
def serial {M p m q : ℕ} (f g : ℕ → ℚ) (A : Slice M p) (B : Slice M q) : ℚ :=
  ∑ C : Slice M m, f (overlap A C) * g (overlap C B)

theorem serial_zero {M p q : ℕ} (f g : ℕ → ℚ) (A : Slice M p) (B : Slice M q) :
    serial (m := 0) f g A B = f 0 * g 0 := by
  have hright : ∀ C : Slice M 0, overlap C B = 0 :=
    fun C => (overlap_symm C B).trans (overlap_zero_right B C)
  simp [serial, overlap_zero_right, hright, slice_card]

theorem serial_full {M p q : ℕ} (f g : ℕ → ℚ) (A : Slice M p) (B : Slice M q) :
    serial (m := M) f g A B = f 0 * g 0 := by
  have hright : ∀ C : Slice M M, overlap C B = 0 :=
    fun C => (overlap_symm C B).trans (overlap_full_right B C)
  simp [serial, overlap_full_right, hright, slice_card]

/-- K2 is proved here for both singleton middle slices, also when M=0. -/
theorem serial_endpoint_closure {M p m q : ℕ} {f g : ℕ → ℚ}
    (hm : m = 0 ∨ m = M) (hf : NewtonCone (overlapRank M p m) f)
    (hg : NewtonCone (overlapRank M m q) g) :
    ∃ h : ℕ → ℚ, NewtonCone (overlapRank M p q) h ∧
      ∀ (A : Slice M p) (B : Slice M q), serial (m := m) f g A B = h (overlap A B) := by
  refine ⟨fun _ => f 0 * g 0, newtonCone_const _ _
    (mul_nonneg (newtonCone_nonneg hf (Nat.zero_le _))
      (newtonCone_nonneg hg (Nat.zero_le _))), ?_⟩
  intro A B
  rcases hm with rfl | rfl
  · exact serial_zero f g A B
  · exact serial_full f g A B

end CoefficientwiseRigidity.Kernel
