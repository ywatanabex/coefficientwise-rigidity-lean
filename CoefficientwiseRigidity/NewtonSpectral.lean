import CoefficientwiseRigidity.SliceComplement

/-!
S2 for the existing rational finite Newton cone. Embeddings depend only on the
rank pair, not the profile; dense pairs use the same complement at both ends.
-/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

def reducedSize (M p q k : ℕ) : ℕ := if p + q ≤ M then k else M - k

def adaptedLift (p q k i : ℕ) : Space M →ₗ[ℝ] Space M :=
  if p + q ≤ M then normalizedLift i (k - i)
  else complement.toLinearMap.comp (normalizedLift i (M - k - i))

theorem adaptedLift_permute (p q k i : ℕ) (σ : Equiv.Perm (Fin M)) (f : Space M) :
    permute σ (adaptedLift p q k i f) = adaptedLift p q k i (permute σ f) := by
  by_cases hpq : p + q ≤ M
  · simp only [adaptedLift, if_pos hpq, permute_normalizedLift]
  · simp only [adaptedLift, if_neg hpq, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← complement_permute, permute_normalizedLift]

theorem adaptedLift_counting {p q k i : ℕ} (hi : i ≤ k) (hk : k + i ≤ M)
    {h : Space M} (hh : Harmonic i h) (f : Space M) :
    counting (adaptedLift p q k i f) (adaptedLift p q k i h) = counting f h := by
  by_cases hpq : p + q ≤ M
  · simp only [adaptedLift, if_pos hpq]
    exact counting_normalizedLift hh (by omega) (by omega) f
  · simp only [adaptedLift, if_neg hpq, LinearMap.comp_apply, LinearEquiv.coe_coe,
      counting_complement]
    exact counting_normalizedLift hh (by omega) (by omega) f

theorem kernelMatrix_congr {p q : ℕ} {F G : ℕ → ℝ}
    (h : ∀ n, n ≤ Kernel.overlapRank M p q → F n = G n) :
    kernelMatrix (M := M) p q F = kernelMatrix p q G := by
  apply LinearMap.ext
  intro f
  funext A
  by_cases hA : A.card = p
  · rw [kernelMatrix_apply F f ⟨A,hA⟩, kernelMatrix_apply G f ⟨A,hA⟩]
    apply Finset.sum_congr rfl
    intro B _
    rw [h _ (Kernel.overlap_le_rank _ _)]
  · rw [kernelMatrix_onLevel p q F f A hA, kernelMatrix_onLevel p q G f A hA]

theorem adaptedLift_onLevel {p q k i : ℕ} (hi : i ≤ k) (hk : k + i ≤ M)
    {h : Space M} (hh : OnLevel i h) : OnLevel k (adaptedLift p q k i h) := by
  have hl (l : ℕ) (hil : i ≤ l) : OnLevel l (normalizedLift i (l - i) h) := by
    apply (levelSpace M l).smul_mem
    simpa only [Nat.add_sub_of_le hil] using onLevel_incidenceLift hh (l - i)
  by_cases hpq : p + q ≤ M
  · simp only [adaptedLift, if_pos hpq]
    exact hl k hi
  · simp only [adaptedLift, if_neg hpq, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hc := onLevel_complement (Nat.sub_le M k) (hl (M - k) (by omega))
    simpa only [Nat.sub_sub_self (show k ≤ M by omega)] using hc

theorem normalizedLift_orthogonal {i j k : ℕ} {f h : Space M}
    (hh : Harmonic j h) (hij : i < j) (hjk : j ≤ k) :
    counting (normalizedLift i (k - i) f) (normalizedLift j (k - j) h) = 0 := by
  simp only [normalizedLift, incidenceLift, LinearMap.smul_apply,
    counting_smul_left, counting_smul_right, harmonic_lifts_orthogonal hh hij hjk, mul_zero]

theorem adaptedLift_orthogonal {p q k i j : ℕ} {f h : Space M}
    (hh : Harmonic j h) (hij : i < j) (hjk : j ≤ k) (hkj : k + j ≤ M) :
    counting (adaptedLift p q k i f) (adaptedLift p q k j h) = 0 := by
  by_cases hpq : p + q ≤ M
  · simp only [adaptedLift, if_pos hpq]
    exact normalizedLift_orthogonal hh hij hjk
  · simp only [adaptedLift, if_neg hpq, LinearMap.comp_apply, LinearEquiv.coe_coe,
      counting_complement]
    exact normalizedLift_orthogonal hh hij (by omega)

theorem overlapRank_reduced {p q : ℕ} (hp : p ≤ M) (hq : q ≤ M) :
    Kernel.overlapRank M p q = min (reducedSize M p q p) (reducedSize M p q q) := by
  unfold Kernel.overlapRank Kernel.overlapShift reducedSize
  split_ifs <;> omega

theorem reduced_sum_le {p q : ℕ} (hp : p ≤ M) (hq : q ≤ M) :
    reducedSize M p q p + reducedSize M p q q ≤ M := by
  unfold reducedSize
  split_ifs <;> omega

/-- The cast is pointwise and only uses the cone on its finite overlap interval. -/
theorem rational_kernel_expansion {p q : ℕ} (F c : ℕ → ℚ)
    (he : ∀ n, n ≤ Kernel.overlapRank M p q →
      F n = Kernel.newtonSum (Kernel.overlapRank M p q) c n) :
    kernelMatrix (M := M) p q (fun n => (F n : ℝ)) =
      kernelMatrix p q (fun n => ∑ d ∈ range (Kernel.overlapRank M p q + 1),
        (c d : ℝ) * (n.choose d : ℝ)) := by
  apply kernelMatrix_congr
  intro n hn
  rw [he n hn]
  simp [Kernel.newtonSum]

theorem newton_kernel_adapted {p q r i : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    (hr : r = Kernel.overlapRank M p q) (c : ℕ → ℝ)
    {h : Space M} (hh : Harmonic i h) (hiq : i ≤ q) (hqi : q + i ≤ M) :
    kernelMatrix p q (fun n => ∑ d ∈ range (r + 1), c d * (n.choose d : ℝ))
        (adaptedLift p q q i h) =
      commonScalar M (reducedSize M p q p) (reducedSize M p q q) r c i •
        adaptedLift p q p i h := by
  have hrange := overlapRank_reduced hp hq
  rw [← hr] at hrange
  by_cases hpq : p + q ≤ M
  · simp only [reducedSize, if_pos hpq] at hrange
    simp only [adaptedLift, reducedSize, if_pos hpq, kernelMatrix_newton hpq]
    exact newtonMatrix_normalized hh hpq (by omega) (by omega) hiq hqi c
  · have hc : M - p + (M - q) ≤ M := by omega
    simp only [reducedSize, if_neg hpq] at hrange
    simp only [adaptedLift, reducedSize, if_neg hpq, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [kernelMatrix_complement hp hq, complement_complement, kernelMatrix_newton hc,
      newtonMatrix_normalized hh hc (by omega) (by omega) (by omega) (by omega), map_smul]

/-- S2: one common family of equivariant isometric embeddings for every cone profile. -/
theorem newtonCone_common_scalars {p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {F : ℕ → ℚ} (hF : Kernel.NewtonCone (Kernel.overlapRank M p q) F) :
    ∃ κ : ℕ → ℝ, (∀ i, 0 ≤ κ i) ∧ Antitone κ ∧
      (∀ i, Kernel.overlapRank M p q < i → κ i = 0) ∧
      ∀ i, i ≤ q → q + i ≤ M → ∀ h : Space M, Harmonic i h →
        kernelMatrix p q (fun n => (F n : ℝ)) (adaptedLift p q q i h) =
          κ i • adaptedLift p q p i h := by
  obtain ⟨c,hc,he⟩ := hF
  let cR : ℕ → ℝ := fun d => (c d : ℝ)
  have hcR : ∀ d, d ≤ Kernel.overlapRank M p q → 0 ≤ cR d := by
    intro d hd
    change (0 : ℝ) ≤ (c d : ℝ)
    exact_mod_cast hc d hd
  refine ⟨commonScalar M (reducedSize M p q p) (reducedSize M p q q)
    (Kernel.overlapRank M p q) cR,
    commonScalar_nonneg _ _ _ _ _ hcR, commonScalar_antitone _ _ _ _ _ hcR, ?_, ?_⟩
  · intro i hi
    exact commonScalar_zero_above _ _ _ _ _ hi
  · intro i hi hqi h hh
    rw [rational_kernel_expansion F c he]
    exact newton_kernel_adapted hp hq rfl cR hh hi hqi

/-- Completeness of the adapted family; its indexing uses the complemented slice when dense. -/
theorem adapted_complete (p q k : ℕ) (hk : k ≤ M) (f : levelSpace M k) :
    ∃ hs : Blocks M (reducedSize M p q k),
      (∑ i, adaptedLift p q k i.val (hs i).val) = f.val := by
  by_cases hpq : p + q ≤ M
  · simp only [reducedSize]
    rw [if_pos hpq]
    simp only [adaptedLift, if_pos hpq]
    obtain ⟨hs,he⟩ := (normalizedDecomposition hk).surjective f
    refine ⟨hs, ?_⟩
    have hv := congrArg Subtype.val he
    simpa only [normalizedDecomposition_apply, Submodule.coe_sum, normalizedBlock_val] using hv
  · simp only [reducedSize]
    rw [if_neg hpq]
    simp only [adaptedLift, if_neg hpq, LinearMap.comp_apply, LinearEquiv.coe_coe]
    let cf : levelSpace M (M - k) := ⟨complement f.val, onLevel_complement hk f.property⟩
    obtain ⟨hs,he⟩ := (normalizedDecomposition (Nat.sub_le M k)).surjective cf
    refine ⟨hs, ?_⟩
    have hv := congrArg Subtype.val he
    have hsum : (∑ i, normalizedLift i.val (M - k - i.val) (hs i).val) = complement f.val := by
      simpa only [normalizedDecomposition_apply, Submodule.coe_sum, normalizedBlock_val] using hv
    rw [← map_sum, hsum, complement_complement]

theorem adapted_index_bounds {p q k : ℕ} (hk : k ≤ M)
    (i : BlockIndex M (reducedSize M p q k)) : i.val ≤ k ∧ k + i.val ≤ M := by
  have hb := block_index_bounds i
  unfold reducedSize at hb
  split_ifs at hb <;> omega

/-- Full operator expansion on every actual input vector, not only selected test blocks. -/
theorem newtonCone_spectral_expansion {p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    {F : ℕ → ℚ} (hF : Kernel.NewtonCone (Kernel.overlapRank M p q) F) :
    ∃ κ : ℕ → ℝ, (∀ i, 0 ≤ κ i) ∧ Antitone κ ∧
      (∀ i, Kernel.overlapRank M p q < i → κ i = 0) ∧
      ∀ f : levelSpace M q, ∃ hs : Blocks M (reducedSize M p q q),
        (∑ i, adaptedLift p q q i.val (hs i).val) = f.val ∧
        kernelMatrix p q (fun n => (F n : ℝ)) f.val =
          ∑ i, κ i.val • adaptedLift p q p i.val (hs i).val := by
  obtain ⟨κ,hκ,hmono,hzero,haction⟩ := newtonCone_common_scalars hp hq hF
  refine ⟨κ,hκ,hmono,hzero,?_⟩
  intro f
  obtain ⟨hs,he⟩ := adapted_complete p q q hq f
  refine ⟨hs,he,?_⟩
  rw [← he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hb := adapted_index_bounds hq i
  exact haction i.val hb.1 hb.2 (hs i).val (hs i).property

end
end CoefficientwiseRigidity.Spectral
