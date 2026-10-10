import CoefficientwiseRigidity.IncidenceMatrix

/-! The computed nonnegative scalars act on the same normalized harmonic embeddings. -/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

theorem incidenceLift_normalized {i d k : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : i ≤ d) (hd : d ≤ k) (hdM : 2 * d ≤ M) :
    incidenceLift (k - d) (normalizedLift i (d - i) h) =
      incidenceScalar M k d i • normalizedLift i (k - i) h := by
  have he : k - d + (d - i) = k - i := by omega
  by_cases hk : k + i ≤ M
  · have hs : Real.sqrt ((M - 2 * i).choose (k - i) : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      exact_mod_cast Nat.choose_pos (show k - i ≤ M - 2 * i by omega)
    simp only [normalizedLift, LinearMap.smul_apply, map_smul, incidenceLift_comp, he, smul_smul]
    rw [incidenceScalar_eq_ratio hi hd hk]
    congr 1
    field_simp [hs]
    rw [mul_div_mul_right _ _ hs]
  · have hz : raise (k - i) h = 0 := raise_eq_zero_above hh (by omega) (by omega)
    simp only [normalizedLift, LinearMap.smul_apply, map_smul, incidenceLift_comp, he]
    simp only [incidenceLift, hz, LinearMap.smul_apply, smul_zero]

theorem coIncidenceLift_normalized {i d k : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : i ≤ d) (hd : d ≤ k) (hk : k + i ≤ M) :
    coIncidenceLift (k - d) (normalizedLift i (k - i) h) =
      incidenceScalar M k d i • normalizedLift i (d - i) h := by
  have he : d - i + (k - d) = k - i := by omega
  have hn : M - 2 * i - (d - i) = M - d - i := by omega
  have hs : Real.sqrt ((M - 2 * i).choose (d - i) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (show d - i ≤ M - 2 * i by omega)
  simp only [normalizedLift, LinearMap.smul_apply, map_smul]
  rw [← he, coIncidenceLift_incidenceLift hh (by omega) (d - i) (k - d) (by omega), hn, he]
  rw [incidenceScalar_eq_co_ratio hi hd hk, smul_smul, smul_smul]
  congr 1
  field_simp [hs]
  rw [mul_div_mul_right _ _ hs]

theorem coIncidenceLift_normalized_zero {i d k : ℕ} {h : Space M} (hh : Harmonic i h)
    (hd : d < i) (hi : i ≤ k) :
    coIncidenceLift (k - d) (normalizedLift i (k - i) h) = 0 := by
  simp only [normalizedLift, LinearMap.smul_apply, map_smul,
    coIncidenceLift_excess hh (k - d) (k - i) (by omega), smul_zero]

/-- Every overlap basis has the same block embeddings, including its terminal zero blocks. -/
theorem overlapMatrix_normalized {p q d i : ℕ} {h : Space M} (hh : Harmonic i h)
    (hpq : p + q ≤ M) (hdp : d ≤ p) (hdq : d ≤ q)
    (hiq : i ≤ q) (hqi : q + i ≤ M) :
    overlapMatrix p q d (normalizedLift i (q - i) h) =
      basisScalar M p q d i • normalizedLift i (p - i) h := by
  have hl : OnLevel q (normalizedLift i (q - i) h) := by
    apply (levelSpace M q).smul_mem
    simpa only [Nat.add_sub_of_le hiq] using onLevel_incidenceLift hh.1 (q - i)
  rw [overlapMatrix_factorization hdp hdq hl]
  by_cases hid : i ≤ d
  · rw [coIncidenceLift_normalized hh hid hdq hqi, map_smul,
      incidenceLift_normalized hh hid hdp (by omega), smul_smul]
    unfold basisScalar
    rw [mul_comm]
  · rw [coIncidenceLift_normalized_zero hh (by omega) hiq, map_zero]
    simp [basisScalar, incidenceScalar, incidenceSquare_zero_of_large (by omega : d < i)]

/-- A finite Newton combination of the actual matrices. -/
def newtonMatrix (p q r : ℕ) (c : ℕ → ℝ) : Space M →ₗ[ℝ] Space M :=
  ∑ d ∈ range (r + 1), c d • overlapMatrix p q d

theorem newtonMatrix_normalized {p q r i : ℕ} {h : Space M} (hh : Harmonic i h)
    (hpq : p + q ≤ M) (hrp : r ≤ p) (hrq : r ≤ q)
    (hiq : i ≤ q) (hqi : q + i ≤ M) (c : ℕ → ℝ) :
    newtonMatrix p q r c (normalizedLift i (q - i) h) =
      commonScalar M p q r c i • normalizedLift i (p - i) h := by
  simp only [newtonMatrix, LinearMap.sum_apply, LinearMap.smul_apply, commonScalar, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro d hd
  have hdr : d ≤ r := by have := Finset.mem_range.mp hd; omega
  rw [overlapMatrix_normalized hh hpq (hdr.trans hrp) (hdr.trans hrq) hiq hqi, smul_smul]

end
end CoefficientwiseRigidity.Spectral
