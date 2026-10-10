import CoefficientwiseRigidity.NetworkJoin
import CoefficientwiseRigidity.LocalDefect

/-!
W3's terminal calculation on concrete joined flat components. This proves the
exact defect and reserve factorization and the kappa loss. Finding these two
components in a general width-two elimination remains a structural obligation.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset
noncomputable section
variable {M p q : ℕ}

theorem twoEntry_defect (e f : GainEntry M p q) :
    (∑ A : Slice M p, ∑ B : Slice M q, e.ordinary A B * f.ordinary A B) -
      (∑ A : Slice M p, ∑ B : Slice M q, e.value A B * f.value A B) =
        localDefect M p q e.profile f.profile (e.gain.trans f.gain.symm) := by
  have hs : (∑ A : Slice M p, ∑ B : Slice M q, e.value A B * f.value A B) =
      ∑ A : Slice M p, ∑ B : Slice M q,
        e.profile (overlap A B) * f.profile (overlap (permuteSlice (e.gain.trans f.gain.symm) A) B) := by
    symm
    apply Fintype.sum_equiv (slicePerm e.gain)
    intro A
    apply Finset.sum_congr rfl
    intro B _
    have ht : overlap (permuteSlice e.gain A) (permuteSlice f.gain B) =
        overlap (permuteSlice (e.gain.trans f.gain.symm) A) B := by
      rw [← overlap_permute f.gain.symm]
      simp only [← permuteSlice_trans, Equiv.self_trans_symm, permuteSlice_refl]
    simp only [GainEntry.value, slicePerm, Equiv.coe_fn_mk, overlap_permute, ht]
  rw [hs]
  simp only [localDefect, GainEntry.ordinary, mul_sub, Finset.sum_sub_distrib]

theorem relative_gain_ne_one (e f : GainEntry M p q) (hef : e.gain ≠ f.gain) :
    e.gain.trans f.gain.symm ≠ 1 := by
  intro h
  apply hef
  apply Equiv.ext
  intro i
  have hi : f.gain.symm (e.gain i) = i := congrArg (fun σ => σ i) h
  simpa using congrArg f.gain hi

end
end CoefficientwiseRigidity.Kernel

namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V W : Type*} [Fintype V] [Fintype W] {p : V → ℕ} {q : W → ℕ}

theorem Net.joinTwo_flat_factor (N : Net M p) (K : Net M q)
    (hN : N.Flat) (hK : K.Flat) (u : V) (v : W)
    (A : Slice M (p u)) (B : Slice M (q v))
    (e f : GainEntry M (p u) (q v)) (b : Bool) :
    (N.joinTwo K u v e f).value b = N.pinnedValue u A true * K.pinnedValue v B true *
      ∑ C : Slice M (p u), ∑ D : Slice M (q v), kernel b [e] C D * kernel b [f] C D := by
  classical
  have hn : ∀ C, N.pinnedValue u C b = N.pinnedValue u A true := by
    intro C
    cases b
    · exact hN.pinnedValue_eq u C A
    · exact N.pinnedValue_ordinary_constant u C A
  have hk : ∀ D, K.pinnedValue v D b = K.pinnedValue v B true := by
    intro D
    cases b
    · exact hK.pinnedValue_eq v D B
    · exact K.pinnedValue_ordinary_constant v D B
  rw [Net.joinTwo_value]
  simp only [hn, hk, Finset.mul_sum, mul_assoc]

/-- Exact terminal loss, including nonidentity gains on both joining edges. -/
theorem Net.joinTwo_flat_defect (N : Net M p) (K : Net M q)
    (hN : N.Flat) (hK : K.Flat) (u : V) (v : W)
    (A : Slice M (p u)) (B : Slice M (q v))
    (e f : GainEntry M (p u) (q v)) :
    (N.joinTwo K u v e f).value true - (N.joinTwo K u v e f).value false =
      N.pinnedValue u A true * K.pinnedValue v B true *
        localDefect M (p u) (q v) e.profile f.profile (e.gain.trans f.gain.symm) := by
  rw [N.joinTwo_flat_factor K hN hK u v A B e f true,
    N.joinTwo_flat_factor K hN hK u v A B e f false, ← mul_sub]
  simp only [kernel, Bool.false_eq_true, if_false, if_true, listOrdinary_cons, listOrdinary_nil,
    listValue_cons, listValue_nil, add_zero, twoEntry_defect]

omit [Fintype V] in
/-- Every reduced gain is the identity, so the reduced network is flat. -/
theorem Net.reduce_flat (N : Net (M + 2) (fun v => p v + 1)) (hp : ∀ v, p v ≤ M) :
    (N.reduce hp).Flat := by
  refine ⟨fun _ => Equiv.refl _, ?_⟩
  intro e he f hf i
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
  rfl

/-- Exact reserve of the joined reduced components; root-only components also fit. -/
theorem Net.joinTwo_reduced_value (N : Net (M + 2) (fun v => p v + 1))
    (K : Net (M + 2) (fun v => q v + 1)) (hp : ∀ v, p v ≤ M) (hq : ∀ v, q v ≤ M)
    (u : V) (v : W) (A : Slice M (p u)) (B : Slice M (q v))
    (e f : GainEntry (M + 2) (p u + 1) (q v + 1)) :
    ((N.reduce hp).joinTwo (K.reduce hq) u v (e.reduce (hp u) (hq v))
      (f.reduce (hp u) (hq v))).value true =
      (N.reduce hp).pinnedValue u A true * (K.reduce hq).pinnedValue v B true *
        differenceMass M (p u) (q v) e.profile f.profile := by
  rw [Net.joinTwo_flat_factor _ _ (N.reduce_flat hp) (K.reduce_flat hq) u v A B _ _ true]
  simp [kernel, GainEntry.ordinary, GainEntry.reduce, differenceMass]

theorem Net.joinTwo_reduced_value_pos (N : Net (M + 2) (fun v => p v + 1))
    (K : Net (M + 2) (fun v => q v + 1)) (hp : ∀ v, p v ≤ M) (hq : ∀ v, q v ≤ M)
    (hs : 0 < N.scalar) (ht : 0 < K.scalar)
    (hN : ∀ e ∈ N.edges, e.Nonconstant) (hK : ∀ e ∈ K.edges, e.Nonconstant)
    (u : V) (v : W) (e f : GainEntry (M + 2) (p u + 1) (q v + 1))
    (he : e.Nonconstant) (hf : f.Nonconstant) :
    0 < ((N.reduce hp).joinTwo (K.reduce hq) u v (e.reduce (hp u) (hq v))
      (f.reduce (hp u) (hq v))).value true := by
  rw [N.joinTwo_reduced_value K hp hq u v (prefixSlice M (p u) (hp u))
    (prefixSlice M (q v) (hq v)) e f]
  exact mul_pos (mul_pos (N.pinnedValue_reduce_pos hp hs hN u _)
    (K.pinnedValue_reduce_pos hq ht hK v _))
    (differenceMass_pos (hp u) (hq v) e.cone f.cone he hf)

/-- W2 and S3 retain the full kappa reserve when the two components are flat.
The hypotheses refer to concrete components and edge gains, not a desired deficit. -/
theorem Net.joinTwo_flat_kappa (N : Net (M + 2) (fun v => p v + 1))
    (K : Net (M + 2) (fun v => q v + 1)) (hp : ∀ v, p v ≤ M) (hq : ∀ v, q v ≤ M)
    (hN : N.Flat) (hK : K.Flat) (u : V) (v : W)
    (e f : GainEntry (M + 2) (p u + 1) (q v + 1))
    (Γ : Subgroup (Equiv.Perm (Fin (M + 2)))) (he : e.gain ∈ Γ) (hf : f.gain ∈ Γ)
    (hef : e.gain ≠ f.gain) :
    kappa (M + 2) Γ * ((N.reduce hp).joinTwo (K.reduce hq) u v
      (e.reduce (hp u) (hq v)) (f.reduce (hp u) (hq v))).value true ≤
      (N.joinTwo K u v e f).value true - (N.joinTwo K u v e f).value false := by
  let A := prefixSlice M (p u) (hp u)
  let B := prefixSlice M (q v) (hq v)
  rw [N.joinTwo_flat_defect K hN hK u v (insertSlice A) (insertSlice B) e f,
    N.joinTwo_reduced_value K hp hq u v A B e f]
  have hmem : e.gain.trans f.gain.symm ∈ Γ := Γ.mul_mem (Γ.inv_mem hf) he
  have hne := relative_gain_ne_one e f hef
  have hkappa : 0 ≤ kappa (M + 2) Γ :=
    (by norm_num : (0 : ℚ) ≤ 2).trans (two_le_kappa Γ ⟨_, hmem, hne⟩)
  have hlocal := localDefect_ge_kappa (hp u) (hq v) e.cone f.cone Γ hmem hne
  have hQ := differenceMass_nonneg (hp u) (hq v) e.cone f.cone
  have hprod := mul_le_mul (N.pinnedValue_reduce_le_insert hp u A)
    (K.pinnedValue_reduce_le_insert hq v B)
    ((K.reduce hq).pinnedValue_nonneg v B true) (N.pinnedValue_nonneg u (insertSlice A) true)
  calc
    _ = ((N.reduce hp).pinnedValue u A true * (K.reduce hq).pinnedValue v B true) *
        (kappa (M + 2) Γ * differenceMass M (p u) (q v) e.profile f.profile) := by ring
    _ ≤ (N.pinnedValue u (insertSlice A) true * K.pinnedValue v (insertSlice B) true) *
        (kappa (M + 2) Γ * differenceMass M (p u) (q v) e.profile f.profile) :=
      mul_le_mul_of_nonneg_right hprod (mul_nonneg hkappa hQ)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlocal (mul_nonneg
      (N.pinnedValue_nonneg u (insertSlice A) true) (K.pinnedValue_nonneg v (insertSlice B) true))

end
end CoefficientwiseRigidity.Network
