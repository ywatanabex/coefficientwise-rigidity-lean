import CoefficientwiseRigidity.MovedSubsets
import CoefficientwiseRigidity.Holonomy

/-! Bounds for the original finite minimum defining the paper's kappa. -/
namespace CoefficientwiseRigidity
open Finset
noncomputable section
variable {M : ℕ}

def kappaRatios (M : ℕ) (Γ : Subgroup (Equiv.Perm (Fin M))) : Finset ℚ := by
  classical
  exact (univ.filter fun σ : Equiv.Perm (Fin M) => σ ∈ Γ ∧ σ ≠ 1).biUnion fun σ =>
    (Icc 1 (M / 2)).image fun k => (movedSubsets M σ k : ℚ) / ((M - 2).choose (k - 1) : ℚ)

theorem kappa_eq_min (Γ : Subgroup (Equiv.Perm (Fin M))) :
    kappa M Γ = if h : (kappaRatios M Γ).Nonempty then (kappaRatios M Γ).min' h else 0 := rfl

theorem mem_kappaRatios_iff (Γ : Subgroup (Equiv.Perm (Fin M))) (a : ℚ) :
    a ∈ kappaRatios M Γ ↔ ∃ σ : Equiv.Perm (Fin M), σ ∈ Γ ∧ σ ≠ 1 ∧
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ M / 2 ∧
        (movedSubsets M σ k : ℚ) / ((M - 2).choose (k - 1) : ℚ) = a := by
  classical
  simp [kappaRatios, and_assoc]

theorem two_le_of_nonidentity (σ : Equiv.Perm (Fin M)) (hσ : σ ≠ 1) : 2 ≤ M := by
  obtain ⟨x,hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hn
    apply hσ
    apply Equiv.ext
    intro x
    simpa using not_exists.mp hn x
  have hc := card_le_univ ({x,σ x} : Finset (Fin M))
  simpa [hx.symm] using hc

theorem kappaRatios_nonempty (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hΓ : ∃ σ : Equiv.Perm (Fin M), σ ∈ Γ ∧ σ ≠ 1) : (kappaRatios M Γ).Nonempty := by
  obtain ⟨σ,hmem,hσ⟩ := hΓ
  have hM := two_le_of_nonidentity σ hσ
  refine ⟨_, (mem_kappaRatios_iff Γ _).mpr ⟨σ,hmem,hσ,1,le_rfl,?_,rfl⟩⟩
  omega

theorem kappa_denominator_pos {k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (hkM : k ≤ M / 2) :
    (0 : ℚ) < (M - 2).choose (k - 1) := by
  exact_mod_cast Nat.choose_pos (show k - 1 ≤ M - 2 by omega)

theorem kappa_le_ratio (Γ : Subgroup (Equiv.Perm (Fin M)))
    {σ : Equiv.Perm (Fin M)} (hmem : σ ∈ Γ) (hσ : σ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M / 2) :
    kappa M Γ ≤ (movedSubsets M σ k : ℚ) / ((M - 2).choose (k - 1) : ℚ) := by
  have hmember := (mem_kappaRatios_iff Γ _).mpr ⟨σ,hmem,hσ,k,hk,hkM,rfl⟩
  have hne : (kappaRatios M Γ).Nonempty := ⟨_,hmember⟩
  rw [kappa_eq_min, dif_pos hne]
  exact Finset.min'_le _ _ hmember

/-- This is the estimate used by weighted cumulative subset deficits. -/
theorem kappa_mul_choose_le_movedSubsets (Γ : Subgroup (Equiv.Perm (Fin M)))
    {σ : Equiv.Perm (Fin M)} (hmem : σ ∈ Γ) (hσ : σ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M / 2) :
    kappa M Γ * ((M - 2).choose (k - 1) : ℚ) ≤ movedSubsets M σ k := by
  exact (le_div_iff₀ (kappa_denominator_pos (two_le_of_nonidentity σ hσ) hk hkM)).mp
    (kappa_le_ratio Γ hmem hσ hk hkM)

theorem le_kappa_of_bounds (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hΓ : ∃ σ : Equiv.Perm (Fin M), σ ∈ Γ ∧ σ ≠ 1) (c : ℚ)
    (hc : ∀ σ : Equiv.Perm (Fin M), σ ∈ Γ → σ ≠ 1 → ∀ k : ℕ,
      1 ≤ k → k ≤ M / 2 → c * ((M - 2).choose (k - 1) : ℚ) ≤ movedSubsets M σ k) :
    c ≤ kappa M Γ := by
  rw [kappa_eq_min, dif_pos (kappaRatios_nonempty Γ hΓ)]
  apply Finset.le_min'
  intro a ha
  obtain ⟨σ,hmem,hσ,k,hk,hkM,rfl⟩ := (mem_kappaRatios_iff Γ a).mp ha
  exact (le_div_iff₀ (kappa_denominator_pos (two_le_of_nonidentity σ hσ) hk hkM)).mpr
    (hc σ hmem hσ k hk hkM)

theorem kappa_mul_choose_le_movedSubsets_interior (Γ : Subgroup (Equiv.Perm (Fin M)))
    {σ : Equiv.Perm (Fin M)} (hmem : σ ∈ Γ) (hσ : σ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (hkM : k < M) :
    kappa M Γ * ((M - 2).choose (k - 1) : ℚ) ≤ movedSubsets M σ k := by
  by_cases hlo : k ≤ M / 2
  · exact kappa_mul_choose_le_movedSubsets Γ hmem hσ hk hlo
  · have hb := kappa_mul_choose_le_movedSubsets Γ hmem hσ
      (k := M - k) (by omega) (by omega)
    have he : (M - 2).choose (M - k - 1) = (M - 2).choose (k - 1) := by
      rw [← Nat.choose_symm (show k - 1 ≤ M - 2 by omega)]
      congr 1
      omega
    rwa [he, movedSubsets_complement σ (by omega)] at hb

theorem two_le_kappa (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hΓ : ∃ σ : Equiv.Perm (Fin M), σ ∈ Γ ∧ σ ≠ 1) : 2 ≤ kappa M Γ := by
  apply le_kappa_of_bounds Γ hΓ 2
  intro σ _ hσ k hk _
  exact_mod_cast two_choose_le_movedSubsets σ hσ hk

theorem three_le_kappa_of_odd (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hΓ : ∃ σ : Equiv.Perm (Fin M), σ ∈ Γ ∧ σ ≠ 1) (hodd : Odd (Nat.card Γ)) :
    3 ≤ kappa M Γ := by
  apply le_kappa_of_bounds Γ hΓ 3
  intro σ hmem hσ k hk _
  exact_mod_cast three_choose_le_movedSubsets_of_odd Γ hodd hmem hσ hk

/-- Connected nonflat covers supply a nonidentity element of the actual holonomy subgroup. -/
theorem holonomy_nontrivial_of_not_flat {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (X : Cover G M) (hc : G.Connected) (root : V) (hn : ¬ Flat X) :
    ∃ σ : Equiv.Perm (Fin M), σ ∈ holonomyGroup X root ∧ σ ≠ 1 := by
  obtain ⟨p,hp⟩ : ∃ p : G.Walk root root, walkTransport X p ≠ Equiv.refl _ := by
    by_contra h
    apply hn
    apply flat_of_trivial_root_walks X hc root
    intro p
    simpa using not_exists.mp h p
  refine ⟨walkTransport X p, Subgroup.subset_closure ⟨p,rfl⟩,hp⟩

theorem holonomy_kappa_bounds {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (X : Cover G M) (hc : G.Connected) (root : V) (hn : ¬ Flat X) :
    2 ≤ kappa M (holonomyGroup X root) ∧
      (Odd (Nat.card (holonomyGroup X root)) → 3 ≤ kappa M (holonomyGroup X root)) := by
  have ht := holonomy_nontrivial_of_not_flat X hc root hn
  exact ⟨two_le_kappa _ ht, three_le_kappa_of_odd _ ht⟩

end
end CoefficientwiseRigidity
