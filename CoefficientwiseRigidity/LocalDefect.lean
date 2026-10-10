import CoefficientwiseRigidity.KappaBounds
import CoefficientwiseRigidity.GainKernels

/-!
S3 via the already proved K2: the defect is a diagonal-minus-off-diagonal
serial kernel. Its monotonicity and W1 reduce the bound to moved-subset counts.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset
noncomputable section

def localDefect (M p q : ℕ) (f g : ℕ → ℚ) (σ : Equiv.Perm (Fin M)) : ℚ :=
  ∑ A : Slice M p, ∑ B : Slice M q,
    f (overlap A B) * (g (overlap A B) - g (overlap (permuteSlice σ A) B))

def differenceMass (M p q : ℕ) (f g : ℕ → ℚ) : ℚ :=
  ∑ A : Slice M p, ∑ B : Slice M q, delta f (overlap A B) * delta g (overlap A B)

theorem overlap_self {M p : ℕ} (A : Slice M p) : overlap A A = overlapRank M p p := by
  simp [overlap, overlapRank, A.property]

theorem overlap_eq_rank_iff_eq {M p : ℕ} (A B : Slice M p) :
    overlap A B = overlapRank M p p ↔ A = B := by
  rw [overlap_eq_rank_iff_subset A B le_rfl]
  constructor
  · intro h
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le h (by rw [A.property,B.property])
  · rintro rfl
    exact subset_rfl

theorem localDefect_serial {M p q : ℕ} (f g : ℕ → ℚ) (σ : Equiv.Perm (Fin M)) :
    localDefect M p q f g σ = ∑ A : Slice M p,
      (serial (m := q) f g A A - serial (m := q) f g A (permuteSlice σ A)) := by
  unfold localDefect
  apply Finset.sum_congr rfl
  intro A _
  simp only [serial, mul_sub, Finset.sum_sub_distrib]
  simp only [overlap_symm (permuteSlice σ A), overlap_symm A]

theorem differenceMass_serial {M p q : ℕ} (f g : ℕ → ℚ) :
    differenceMass M p q f g = ∑ A : Slice M p, serial (m := q) (delta f) (delta g) A A := by
  unfold differenceMass serial
  simp only [overlap_symm]

theorem sum_moved_indicator {M p : ℕ} (σ : Equiv.Perm (Fin M)) (c : ℚ) :
    (∑ A : Slice M p, if A.val.map σ.toEmbedding ≠ A.val then c else 0) =
      (movedSubsets M σ p : ℚ) * c := by
  classical
  rw [← Finset.sum_subtype (univ.filter (fun A : Finset (Fin M) => A.card = p))
    (by simp) (fun A => if A.map σ.toEmbedding ≠ A then c else 0)]
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The reduced mass is the top serial difference times the number of reduced outer sets. -/
theorem differenceMass_profile {M p q : ℕ} {f g h : ℕ → ℚ}
    (hh : ∀ A B : Slice (M + 2) (p + 1), serial (m := q + 1) f g A B = h (overlap A B)) :
    differenceMass M p q f g = (M.choose p : ℚ) * delta h (overlapRank M p p) := by
  rw [differenceMass_serial]
  have he : (∑ A : Slice M p, serial (m := q) (delta f) (delta g) A A) =
      ∑ _A : Slice M p, delta h (overlapRank M p p) := by
    apply Finset.sum_congr rfl
    intro A _
    rw [← serial_profile_difference hh A A, overlap_self]
  rw [he, Finset.sum_const, Finset.card_univ, slice_card, nsmul_eq_mul]

/-- Distinct same-rank sets lose at least the final increment of a monotone radial profile. -/
theorem radial_defect_lower {M p : ℕ} {h : ℕ → ℚ}
    (hh : NewtonCone (overlapRank (M + 2) (p + 1) (p + 1)) h) (hp : p ≤ M)
    (A B : Slice (M + 2) (p + 1)) :
    (if A = B then 0 else delta h (overlapRank M p p)) ≤
      h (overlap A A) - h (overlap A B) := by
  have hr := overlapRank_reduce hp hp
  rw [overlap_self, hr]
  by_cases he : A = B
  · subst B
    simp [overlap_self, hr]
  · rw [if_neg he]
    have hlt : overlap A B < overlapRank (M + 2) (p + 1) (p + 1) := by
      have hle := overlap_le_rank A B
      have hne : overlap A B ≠ overlapRank (M + 2) (p + 1) (p + 1) :=
        fun hz => he ((overlap_eq_rank_iff_eq A B).mp hz)
      omega
    have hm := newtonCone_monotone hh (show overlap A B ≤ overlapRank M p p by omega)
      (show overlapRank M p p ≤ overlapRank (M + 2) (p + 1) (p + 1) by omega)
    simp only [delta, fwdDiff]
    linarith

/-- A stronger rank-specific bound; K2 and W1 are independently proved inputs. -/
theorem localDefect_lower_of_moved {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (σ : Equiv.Perm (Fin (M + 2))) (c : ℚ)
    (hc : c * (M.choose p : ℚ) ≤ movedSubsets (M + 2) σ (p + 1)) :
    c * differenceMass M p q f g ≤ localDefect (M + 2) (p + 1) (q + 1) f g σ := by
  have hg' : NewtonCone (overlapRank (M + 2) (q + 1) (p + 1)) g := by
    simpa only [overlapRank_symm] using hg
  obtain ⟨h,hcone,hh⟩ := serial_newton_closure (M + 2) (p + 1) (q + 1) (p + 1)
    (by omega) (by omega) (by omega) f g hf hg'
  have hr := overlapRank_reduce hp hp
  have hdelta : 0 ≤ delta h (overlapRank M p p) := by
    have hm := newtonCone_monotone hcone (Nat.le_succ (overlapRank M p p))
      (show overlapRank M p p + 1 ≤ overlapRank (M + 2) (p + 1) (p + 1) by omega)
    simp only [delta, fwdDiff]
    linarith
  have hsum : (movedSubsets (M + 2) σ (p + 1) : ℚ) * delta h (overlapRank M p p) ≤
      localDefect (M + 2) (p + 1) (q + 1) f g σ := by
    rw [localDefect_serial, ← sum_moved_indicator]
    apply Finset.sum_le_sum
    intro A _
    rw [hh A A, hh A (permuteSlice σ A)]
    have he : A = permuteSlice σ A ↔ A.val.map σ.toEmbedding = A.val := by
      simp only [Subtype.ext_iff, permuteSlice]
      exact eq_comm
    simpa only [he, ne_eq, ite_not] using radial_defect_lower hcone hp A (permuteSlice σ A)
  rw [differenceMass_profile hh]
  calc
    c * ((M.choose p : ℚ) * delta h (overlapRank M p p)) =
      (c * (M.choose p : ℚ)) * delta h (overlapRank M p p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hdelta
    _ ≤ _ := hsum

theorem overlap_swap_of_moved {M p : ℕ} (A : Slice (M + 2) (p + 1))
    {x y : Fin (M + 2)} (hm : A.val.map (Equiv.swap x y).toEmbedding ≠ A.val) :
    overlap A (permuteSlice (Equiv.swap x y) A) = overlapRank M p p := by
  have hc := card_inter_swap_of_moved hm
  rw [A.property] at hc
  simp only [overlap, permuteSlice, overlapRank, overlapShift, min_self]
  rw [hc]
  omega

/-- S3a holds for arbitrary rational profiles: no cone hypothesis is needed. -/
theorem localDefect_swap {M p : ℕ} (hp : p ≤ M) (q : ℕ) (f g : ℕ → ℚ)
    (x y : Fin (M + 2)) (hxy : x ≠ y) :
    localDefect (M + 2) (p + 1) (q + 1) f g (Equiv.swap x y) =
      2 * differenceMass M p q f g := by
  obtain ⟨h,hh⟩ := exists_serial_profile (M := M + 2) (p := p + 1) (q := p + 1)
    (m := q + 1) (by omega) (by omega) f g
  have hr := overlapRank_reduce hp hp
  rw [localDefect_serial]
  have he : (∑ A : Slice (M + 2) (p + 1),
      (serial (m := q + 1) f g A A - serial (m := q + 1) f g A (permuteSlice (Equiv.swap x y) A))) =
      ∑ A : Slice (M + 2) (p + 1),
        if A.val.map (Equiv.swap x y).toEmbedding ≠ A.val then delta h (overlapRank M p p) else 0 := by
    apply Finset.sum_congr rfl
    intro A _
    by_cases hm : A.val.map (Equiv.swap x y).toEmbedding = A.val
    · have ha : permuteSlice (Equiv.swap x y) A = A := Subtype.ext hm
      rw [ha]
      simp [hm]
    · rw [hh A A, hh A _, overlap_self, hr, overlap_swap_of_moved A hm]
      simp [hm, delta, fwdDiff]
  rw [he, sum_moved_indicator, movedSubsets_swap hxy (by omega), differenceMass_profile hh]
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem localDefect_ge_two {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (σ : Equiv.Perm (Fin (M + 2))) (hσ : σ ≠ 1) :
    2 * differenceMass M p q f g ≤ localDefect (M + 2) (p + 1) (q + 1) f g σ := by
  apply localDefect_lower_of_moved hp hq hf hg σ 2
  exact_mod_cast (by simpa using two_choose_le_movedSubsets σ hσ (k := p + 1) (by omega) :
    2 * M.choose p ≤ movedSubsets (M + 2) σ (p + 1))

theorem localDefect_ge_three_of_square_ne_one {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (σ : Equiv.Perm (Fin (M + 2))) (hσ : σ ^ 2 ≠ 1) :
    3 * differenceMass M p q f g ≤ localDefect (M + 2) (p + 1) (q + 1) f g σ := by
  apply localDefect_lower_of_moved hp hq hf hg σ 3
  exact_mod_cast (by simpa using three_choose_le_movedSubsets σ hσ (k := p + 1) (by omega) :
    3 * M.choose p ≤ movedSubsets (M + 2) σ (p + 1))

/-- Paper S3, for the original subgroup minimum and every nonidentity member. -/
theorem localDefect_ge_kappa {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (Γ : Subgroup (Equiv.Perm (Fin (M + 2)))) {σ : Equiv.Perm (Fin (M + 2))}
    (hmem : σ ∈ Γ) (hσ : σ ≠ 1) :
    kappa (M + 2) Γ * differenceMass M p q f g ≤
      localDefect (M + 2) (p + 1) (q + 1) f g σ := by
  apply localDefect_lower_of_moved hp hq hf hg σ (kappa (M + 2) Γ)
  simpa using kappa_mul_choose_le_movedSubsets_interior Γ hmem hσ (k := p + 1)
    (by omega) (by omega)

theorem localDefect_ge_three_of_odd {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (Γ : Subgroup (Equiv.Perm (Fin (M + 2)))) (hodd : Odd (Nat.card Γ))
    {σ : Equiv.Perm (Fin (M + 2))} (hmem : σ ∈ Γ) (hσ : σ ≠ 1) :
    3 * differenceMass M p q f g ≤ localDefect (M + 2) (p + 1) (q + 1) f g σ :=
  localDefect_ge_three_of_square_ne_one hp hq hf hg σ
    (square_ne_one_of_odd_subgroup Γ hodd hmem hσ)

theorem differenceMass_nonneg {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g) :
    0 ≤ differenceMass M p q f g := by
  rw [overlapRank_reduce hp hq] at hf hg
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro B _
  exact mul_nonneg (newtonCone_nonneg (newtonCone_delta hf) (overlap_le_rank A B))
    (newtonCone_nonneg (newtonCone_delta hg) (overlap_le_rank A B))

theorem differenceMass_pos {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (hnf : ∃ n, n ≤ overlapRank (M + 2) (p + 1) (q + 1) ∧ f n ≠ f 0)
    (hng : ∃ n, n ≤ overlapRank (M + 2) (p + 1) (q + 1) ∧ g n ≠ g 0) :
    0 < differenceMass M p q f g := by
  rw [overlapRank_reduce hp hq] at hf hg hnf hng
  have hfpos : 0 < delta f (overlapRank M p q) := sub_pos.mpr ((newtonCone_last_strict_iff hf).mpr hnf)
  have hgpos : 0 < delta g (overlapRank M p q) := sub_pos.mpr ((newtonCone_last_strict_iff hg).mpr hng)
  have hn (A : Slice M p) (B : Slice M q) :
      0 ≤ delta f (overlap A B) * delta g (overlap A B) :=
    mul_nonneg (newtonCone_nonneg (newtonCone_delta hf) (overlap_le_rank A B))
      (newtonCone_nonneg (newtonCone_delta hg) (overlap_le_rank A B))
  let A : Slice M p := ⟨initialSegment M p,card_prefix M p hp⟩
  obtain ⟨B,hB⟩ := exists_overlap A hq (overlapRank M p q) le_rfl
  apply Finset.sum_pos' (fun C _ => Finset.sum_nonneg (fun D _ => hn C D))
  refine ⟨A,mem_univ _,Finset.sum_pos' (fun D _ => hn A D) ⟨B,mem_univ _,?_⟩⟩
  rw [hB]
  exact mul_pos hfpos hgpos

/-- The original M,p,q indexing, including M=2 and all reduced endpoint boundaries. -/
theorem localDefect_ge_kappa_interior {M p q : ℕ} (hM : 2 ≤ M)
    (hp : 1 ≤ p) (hpM : p < M) (hq : 1 ≤ q) (hqM : q < M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank M p q) f)
    (hg : NewtonCone (overlapRank M p q) g)
    (Γ : Subgroup (Equiv.Perm (Fin M))) {σ : Equiv.Perm (Fin M)}
    (hmem : σ ∈ Γ) (hσ : σ ≠ 1) :
    kappa M Γ * differenceMass (M - 2) (p - 1) (q - 1) f g ≤ localDefect M p q f g σ := by
  obtain ⟨N,hN⟩ := Nat.exists_eq_add_of_le hM
  have hN' : M = N + 2 := by omega
  clear hN
  subst M
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hp
  have ha' : p = a + 1 := by omega
  clear ha
  subst p
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le hq
  have hb' : q = b + 1 := by omega
  clear hb
  subst q
  simpa using localDefect_ge_kappa (by omega : a ≤ N) (by omega : b ≤ N) hf hg Γ hmem hσ

theorem localDefect_ge_rank_ratio {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (σ : Equiv.Perm (Fin (M + 2))) :
    ((movedSubsets (M + 2) σ (p + 1) : ℚ) / (M.choose p : ℚ)) * differenceMass M p q f g ≤
      localDefect (M + 2) (p + 1) (q + 1) f g σ := by
  apply localDefect_lower_of_moved hp hq hf hg σ
  have hden : (M.choose p : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.choose_pos hp)
  rw [div_mul_cancel₀ _ hden]

theorem localDefect_pos_of_nonconstant {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {f g : ℕ → ℚ} (hf : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) f)
    (hg : NewtonCone (overlapRank (M + 2) (p + 1) (q + 1)) g)
    (hnf : ∃ n, n ≤ overlapRank (M + 2) (p + 1) (q + 1) ∧ f n ≠ f 0)
    (hng : ∃ n, n ≤ overlapRank (M + 2) (p + 1) (q + 1) ∧ g n ≠ g 0)
    (σ : Equiv.Perm (Fin (M + 2))) (hσ : σ ≠ 1) :
    0 < localDefect (M + 2) (p + 1) (q + 1) f g σ := by
  have hpQ := differenceMass_pos hp hq hf hg hnf hng
  have hb := localDefect_ge_two hp hq hf hg σ hσ
  linarith

end
end CoefficientwiseRigidity.Kernel
