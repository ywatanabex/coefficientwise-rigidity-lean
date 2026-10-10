import CoefficientwiseRigidity.Targets
import Mathlib.Data.Finset.Powerset
import Mathlib.GroupTheory.OrderOfElement

/-! Exact subset counts and cumulative moved-subset bounds for S3. -/
namespace CoefficientwiseRigidity
open Finset
noncomputable section
variable {M : ℕ}

def orientedSubsets (k : ℕ) (x y : Fin M) : Finset (Finset (Fin M)) :=
  univ.filter fun A => A.card = k ∧ x ∈ A ∧ y ∉ A

theorem orientedSubsets_image {k : ℕ} (hk : 1 ≤ k) {x y : Fin M} (hxy : x ≠ y) :
    orientedSubsets k x y =
      (((univ.erase x).erase y).powersetCard (k - 1)).image (insert x) := by
  ext A
  simp only [orientedSubsets, mem_filter, mem_univ, true_and, mem_image, mem_powersetCard]
  constructor
  · rintro ⟨hA,hx,hy⟩
    refine ⟨A.erase x, ?_, ?_⟩
    · constructor
      · intro z hz
        obtain ⟨hzx,hzA⟩ := mem_erase.mp hz
        simp only [mem_erase, mem_univ, and_true]
        exact ⟨fun hzy => hy (hzy ▸ hzA), hzx⟩
      · rw [card_erase_of_mem hx, hA]
    · exact insert_erase hx
  · rintro ⟨B,⟨hB,hcard⟩,rfl⟩
    have hx : x ∉ B := by
      intro hx
      exact (mem_erase.mp (mem_erase.mp (hB hx)).2).1 rfl
    have hy : y ∉ B := by
      intro hy
      exact (mem_erase.mp (hB hy)).1 rfl
    simp only [card_insert_of_not_mem hx, hcard, mem_insert_self, mem_insert, not_or,
      true_and]
    exact ⟨by omega, hxy.symm, hy⟩

theorem card_orientedSubsets {k : ℕ} (hk : 1 ≤ k) {x y : Fin M} (hxy : x ≠ y) :
    (orientedSubsets k x y).card = (M - 2).choose (k - 1) := by
  rw [orientedSubsets_image hk hxy, card_image_iff.mpr, card_powersetCard]
  · simp [card_erase_of_mem, hxy.symm, Nat.sub_sub]
  · intro A hA B hB he
    have hxA : x ∉ A := by
      intro hx
      exact (mem_erase.mp (mem_erase.mp ((mem_powersetCard.mp hA).1 hx)).2).1 rfl
    have hxB : x ∉ B := by
      intro hx
      exact (mem_erase.mp (mem_erase.mp ((mem_powersetCard.mp hB).1 hx)).2).1 rfl
    have := congrArg (fun S : Finset (Fin M) => S.erase x) he
    simpa [hxA,hxB] using this

def separates (A : Finset (Fin M)) (x y : Fin M) : Prop := ¬ (x ∈ A ↔ y ∈ A)

instance (A : Finset (Fin M)) (x y : Fin M) : Decidable (separates A x y) :=
  inferInstanceAs (Decidable (¬ (x ∈ A ↔ y ∈ A)))

def separatingSubsets (k : ℕ) (x y : Fin M) : Finset (Finset (Fin M)) := by
  classical
  exact univ.filter fun A => A.card = k ∧ separates A x y

theorem card_separatingSubsets {k : ℕ} (hk : 1 ≤ k) {x y : Fin M} (hxy : x ≠ y) :
    (separatingSubsets k x y).card = 2 * (M - 2).choose (k - 1) := by
  classical
  have he : separatingSubsets k x y = orientedSubsets k x y ∪ orientedSubsets k y x := by
    ext A
    simp only [separatingSubsets, orientedSubsets, mem_filter, mem_univ, true_and, mem_union,
      separates]
    tauto
  have hd : Disjoint (orientedSubsets k x y) (orientedSubsets k y x) := by
    apply Finset.disjoint_left.mpr
    intro A hA hB
    simp only [orientedSubsets, mem_filter, mem_univ, true_and] at hA hB
    exact hA.2.2 hB.2.1
  rw [he, card_union_of_disjoint hd, card_orientedSubsets hk hxy,
    card_orientedSubsets hk hxy.symm]
  omega

/-- A set invariant under the permutation has constant membership along its orbit. -/
theorem invariant_mem_apply (σ : Equiv.Perm (Fin M)) {A : Finset (Fin M)}
    (hA : A.map σ.toEmbedding = A) (x : Fin M) : x ∈ A ↔ σ x ∈ A := by
  conv_rhs => rw [← hA]
  simp

theorem separates_moved (σ : Equiv.Perm (Fin M)) {A : Finset (Fin M)} (x : Fin M)
    (hx : separates A x (σ x)) : A.map σ.toEmbedding ≠ A := by
  intro hA
  exact hx (invariant_mem_apply σ hA x)

theorem map_swap_eq_self_iff (A : Finset (Fin M)) (x y : Fin M) :
    A.map (Equiv.swap x y).toEmbedding = A ↔ (x ∈ A ↔ y ∈ A) := by
  constructor
  · intro hA
    simpa using invariant_mem_apply (Equiv.swap x y) hA x
  · intro hxy
    ext z
    obtain ⟨w,rfl⟩ := (Equiv.swap x y).surjective z
    simp only [Finset.mem_map_equiv]
    by_cases hx : w = x
    · subst w
      simpa using hxy
    by_cases hy : w = y
    · subst w
      simpa using hxy.symm
    · simp [Equiv.swap_apply_of_ne_of_ne hx hy]

theorem movedSubsets_swap {x y : Fin M} (hxy : x ≠ y) {k : ℕ} (hk : 1 ≤ k) :
    movedSubsets M (Equiv.swap x y) k = 2 * (M - 2).choose (k - 1) := by
  classical
  rw [← card_separatingSubsets hk hxy]
  unfold movedSubsets separatingSubsets
  congr 1
  ext A
  simp [map_swap_eq_self_iff, separates]

theorem map_compl_perm (σ : Equiv.Perm (Fin M)) (A : Finset (Fin M)) :
    Aᶜ.map σ.toEmbedding = (A.map σ.toEmbedding)ᶜ := by
  ext z
  obtain ⟨x,rfl⟩ := σ.surjective z
  simp

theorem inter_swap_of_not_mem {A : Finset (Fin M)} {x y : Fin M}
    (hy : y ∉ A) : A ∩ A.map (Equiv.swap x y).toEmbedding = A.erase x := by
  ext z
  by_cases hzx : z = x
  · subst z
    simp [Finset.mem_map_equiv, hy]
  by_cases hzy : z = y
  · subst z
    simp [hy]
  · simp [Finset.mem_map_equiv, Equiv.swap_apply_of_ne_of_ne hzx hzy, hzx]

theorem card_inter_swap_of_moved {A : Finset (Fin M)} {x y : Fin M}
    (hm : A.map (Equiv.swap x y).toEmbedding ≠ A) :
    (A ∩ A.map (Equiv.swap x y).toEmbedding).card = A.card - 1 := by
  have hsep : ¬ (x ∈ A ↔ y ∈ A) := fun he => hm ((map_swap_eq_self_iff A x y).mpr he)
  by_cases hx : x ∈ A
  · have hy : y ∉ A := by tauto
    rw [inter_swap_of_not_mem hy, card_erase_of_mem hx]
  · have hy : y ∈ A := by tauto
    rw [Equiv.swap_comm x y, inter_swap_of_not_mem hx, card_erase_of_mem hy]

theorem movedSubsets_complement (σ : Equiv.Perm (Fin M)) {k : ℕ} (hk : k ≤ M) :
    movedSubsets M σ (M - k) = movedSubsets M σ k := by
  classical
  unfold movedSubsets
  apply Finset.card_equiv (⟨compl,compl,compl_compl,compl_compl⟩ :
    Finset (Fin M) ≃ Finset (Fin M))
  intro A
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_fn_mk,
    card_compl, Fintype.card_fin, map_compl_perm, ne_eq, compl_inj_iff]
  have hA : A.card ≤ M := by simpa using card_le_univ A
  constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨by omega,h₂⟩

/-- Every nonidentity permutation moves at least the transposition count. -/
theorem two_choose_le_movedSubsets (σ : Equiv.Perm (Fin M)) (hσ : σ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) : 2 * (M - 2).choose (k - 1) ≤ movedSubsets M σ k := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hn
    apply hσ
    apply Equiv.ext
    intro x
    simpa using not_exists.mp hn x
  rw [← card_separatingSubsets hk hx.symm]
  apply card_le_card
  intro A hA
  simp only [separatingSubsets, mem_filter, mem_univ, true_and] at hA
  exact mem_filter.mpr ⟨mem_univ _, hA.1, separates_moved σ x hA.2⟩

theorem three_separations_le (σ : Equiv.Perm (Fin M)) (x y z : Fin M)
    (hxy : σ x = y) (hyz : σ y = z) (A : Finset (Fin M)) (k : ℕ) :
    (if A.card = k ∧ separates A x y then 1 else 0) +
      (if A.card = k ∧ separates A y z then 1 else 0) +
      (if A.card = k ∧ separates A x z then 1 else 0) ≤
        2 * (if A.card = k ∧ A.map σ.toEmbedding ≠ A then 1 else 0 : ℕ) := by
  classical
  by_cases hk : A.card = k
  · simp only [hk, true_and]
    by_cases hA : A.map σ.toEmbedding = A
    · have hab := invariant_mem_apply σ hA x
      have hbc := invariant_mem_apply σ hA y
      rw [hxy] at hab
      rw [hyz] at hbc
      simp [separates, hab, hbc, hA]
    · simp only [hA, ne_eq, not_false_eq_true, if_true]
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> by_cases hz : z ∈ A <;>
        simp [separates, hx, hy, hz]
  · simp [hk]

/-- Three successive distinct orbit labels force the improved cumulative count. -/
theorem three_choose_le_movedSubsets_of_chain (σ : Equiv.Perm (Fin M))
    (x y z : Fin M) (hxy : σ x = y) (hyz : σ y = z)
    (h₁ : x ≠ y) (h₂ : y ≠ z) (h₃ : x ≠ z) {k : ℕ} (hk : 1 ≤ k) :
    3 * (M - 2).choose (k - 1) ≤ movedSubsets M σ k := by
  classical
  have hsum := Finset.sum_le_sum (s := (univ : Finset (Finset (Fin M))))
    (fun A _ => three_separations_le σ x y z hxy hyz A k)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [← Finset.card_filter] at hsum
  change (separatingSubsets k x y).card + (separatingSubsets k y z).card +
    (separatingSubsets k x z).card ≤ 2 * movedSubsets M σ k at hsum
  rw [card_separatingSubsets hk h₁, card_separatingSubsets hk h₂,
    card_separatingSubsets hk h₃] at hsum
  omega

/-- A permutation whose square is nonidentity contains three distinct successive labels. -/
theorem exists_three_chain (σ : Equiv.Perm (Fin M)) (hσ : σ ^ 2 ≠ 1) :
    ∃ x : Fin M, x ≠ σ x ∧ σ x ≠ σ (σ x) ∧ x ≠ σ (σ x) := by
  obtain ⟨x,hx⟩ : ∃ x, σ (σ x) ≠ x := by
    by_contra hn
    apply hσ
    apply Equiv.ext
    intro x
    simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, not_not] using not_exists.mp hn x
  have hfirst : x ≠ σ x := by intro he; apply hx; rw [← he, ← he]
  exact ⟨x,hfirst,fun he => hfirst (σ.injective he),hx.symm⟩

theorem three_choose_le_movedSubsets (σ : Equiv.Perm (Fin M)) (hσ : σ ^ 2 ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) : 3 * (M - 2).choose (k - 1) ≤ movedSubsets M σ k := by
  obtain ⟨x,h₁,h₂,h₃⟩ := exists_three_chain σ hσ
  exact three_choose_le_movedSubsets_of_chain σ x (σ x) (σ (σ x)) rfl rfl h₁ h₂ h₃ hk

/-- In an odd-order subgroup a nonidentity element cannot square to one. -/
theorem square_ne_one_of_odd_subgroup (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hΓ : Odd (Nat.card Γ)) {σ : Equiv.Perm (Fin M)} (hmem : σ ∈ Γ) (hσ : σ ≠ 1) :
    σ ^ 2 ≠ 1 := by
  intro hs
  have hd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hs
  have ho : orderOf σ = 2 := by
    have he := (Nat.dvd_prime Nat.prime_two).mp hd
    rcases he with he | he
    · exact False.elim (hσ (orderOf_eq_one_iff.mp he))
    · exact he
  apply hΓ.not_two_dvd_nat
  rw [← ho]
  exact Γ.orderOf_dvd_natCard hmem

theorem three_choose_le_movedSubsets_of_odd (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hΓ : Odd (Nat.card Γ)) {σ : Equiv.Perm (Fin M)} (hmem : σ ∈ Γ) (hσ : σ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) : 3 * (M - 2).choose (k - 1) ≤ movedSubsets M σ k :=
  three_choose_le_movedSubsets σ (square_ne_one_of_odd_subgroup Γ hΓ hmem hσ) hk

end
end CoefficientwiseRigidity
