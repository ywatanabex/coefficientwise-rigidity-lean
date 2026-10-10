import CoefficientwiseRigidity.IncidenceAlgebra

/-!
The exact S2 scalar formulas. A complementary-binomial form makes monotonicity
termwise: both factors have the fixed lower index k-d. The cutoff i<=d is explicit.
-/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section

def incidenceSquare (M k d i : ℕ) : ℕ :=
  if i ≤ d then (k - i).choose (k - d) * (M - d - i).choose (k - d) else 0

theorem incidenceSquare_eq {M k d i : ℕ} (hi : i ≤ d) (hd : d ≤ k) :
    incidenceSquare M k d i = (k - i).choose (d - i) * (M - d - i).choose (k - d) := by
  unfold incidenceSquare
  rw [if_pos hi, ← Nat.choose_symm (show d - i ≤ k - i by omega)]
  congr 2
  omega

theorem incidenceSquare_antitone (M k d : ℕ) : Antitone (incidenceSquare M k d) := by
  intro i j hij
  by_cases hj : j ≤ d
  · simp only [incidenceSquare, if_pos hj, if_pos (hij.trans hj)]
    exact Nat.mul_le_mul
      (Nat.choose_le_choose _ (Nat.sub_le_sub_left hij k))
      (Nat.choose_le_choose _ (Nat.sub_le_sub_left hij (M - d)))
  · simp only [incidenceSquare, if_neg hj]
    exact Nat.zero_le _

theorem incidenceSquare_zero_of_large {M k d i : ℕ} (hi : d < i) :
    incidenceSquare M k d i = 0 := by simp [incidenceSquare, Nat.not_le.mpr hi]

theorem incidenceSquare_zero_of_missing {M k d i : ℕ}
    (hd : d ≤ k) (hdM : 2 * d ≤ M) (hi : M - k < i) :
    incidenceSquare M k d i = 0 := by
  by_cases hid : i ≤ d
  · unfold incidenceSquare
    rw [if_pos hid, Nat.choose_eq_zero_of_lt (show M - d - i < k - d by omega), mul_zero]
  · simp [incidenceSquare, hid]

def incidenceScalar (M k d i : ℕ) : ℝ := Real.sqrt (incidenceSquare M k d i : ℝ)

theorem incidenceScalar_nonneg (M k d i : ℕ) : 0 ≤ incidenceScalar M k d i :=
  Real.sqrt_nonneg _

theorem incidenceScalar_antitone (M k d : ℕ) : Antitone (incidenceScalar M k d) := by
  intro i j hij
  exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (incidenceSquare_antitone M k d hij))

@[simp] theorem incidenceScalar_sq (M k d i : ℕ) :
    incidenceScalar M k d i ^ 2 = (incidenceSquare M k d i : ℝ) :=
  Real.sq_sqrt (Nat.cast_nonneg _)

/-- The factorial cancellation is a binomial double-counting identity. -/
theorem incidenceSquare_balance {M k d i : ℕ}
    (hi : i ≤ d) (hd : d ≤ k) (hk : k + i ≤ M) :
    (M - 2 * i).choose (k - i) * ((k - i).choose (d - i)) ^ 2 =
      incidenceSquare M k d i * (M - 2 * i).choose (d - i) := by
  have he := Nat.choose_mul (show k - i ≤ M - 2 * i by omega)
    (show d - i ≤ k - i by omega)
  have hn : M - 2 * i - (d - i) = M - d - i := by omega
  have hm : k - i - (d - i) = k - d := by omega
  rw [hn, hm] at he
  rw [incidenceSquare_eq hi hd]
  calc
    _ = ((M - 2 * i).choose (k - i) * (k - i).choose (d - i)) *
      (k - i).choose (d - i) := by ring
    _ = _ := by rw [he]; ring

theorem incidenceScalar_eq_ratio {M k d i : ℕ}
    (hi : i ≤ d) (hd : d ≤ k) (hk : k + i ≤ M) :
    incidenceScalar M k d i = (k - i).choose (d - i) *
      Real.sqrt ((M - 2 * i).choose (k - i) : ℝ) /
      Real.sqrt ((M - 2 * i).choose (d - i) : ℝ) := by
  have hC : (0 : ℝ) < (M - 2 * i).choose (d - i) := by
    exact_mod_cast Nat.choose_pos (show d - i ≤ M - 2 * i by omega)
  apply (sq_eq_sq₀ (incidenceScalar_nonneg ..) (by positivity)).mp
  rw [incidenceScalar_sq, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg _)]
  apply (eq_div_iff (ne_of_gt hC)).mpr
  have he : ((M - 2 * i).choose (k - i) : ℝ) * ((k - i).choose (d - i) : ℝ) ^ 2 =
      (incidenceSquare M k d i : ℝ) * (M - 2 * i).choose (d - i) := by
    exact_mod_cast incidenceSquare_balance hi hd hk
  nlinarith [he]

theorem incidenceScalar_eq_co_ratio {M k d i : ℕ}
    (hi : i ≤ d) (hd : d ≤ k) (hk : k + i ≤ M) :
    incidenceScalar M k d i = (M - d - i).choose (k - d) *
      Real.sqrt ((M - 2 * i).choose (d - i) : ℝ) /
      Real.sqrt ((M - 2 * i).choose (k - i) : ℝ) := by
  rw [incidenceScalar_eq_ratio hi hd hk]
  have hdC : (0 : ℝ) < (M - 2 * i).choose (d - i) := by
    exact_mod_cast Nat.choose_pos (show d - i ≤ M - 2 * i by omega)
  have hkC : (0 : ℝ) < (M - 2 * i).choose (k - i) := by
    exact_mod_cast Nat.choose_pos (show k - i ≤ M - 2 * i by omega)
  have he := Nat.choose_mul (show k - i ≤ M - 2 * i by omega)
    (show d - i ≤ k - i by omega)
  have hn : M - 2 * i - (d - i) = M - d - i := by omega
  have hm : k - i - (d - i) = k - d := by omega
  rw [hn, hm] at he
  have heR : ((M - 2 * i).choose (k - i) : ℝ) * (k - i).choose (d - i) =
      ((M - 2 * i).choose (d - i) : ℝ) * (M - d - i).choose (k - d) := by
    exact_mod_cast he
  apply (div_eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr hdC))
    (ne_of_gt (Real.sqrt_pos.mpr hkC))).mpr
  nlinarith [Real.sq_sqrt hdC.le, Real.sq_sqrt hkC.le]

def basisScalar (M p q d i : ℕ) : ℝ := incidenceScalar M p d i * incidenceScalar M q d i

theorem basisScalar_nonneg (M p q d i : ℕ) : 0 ≤ basisScalar M p q d i :=
  mul_nonneg (incidenceScalar_nonneg ..) (incidenceScalar_nonneg ..)

theorem basisScalar_antitone (M p q d : ℕ) : Antitone (basisScalar M p q d) := by
  intro i j hij
  exact mul_le_mul (incidenceScalar_antitone M p d hij)
    (incidenceScalar_antitone M q d hij) (incidenceScalar_nonneg ..) (incidenceScalar_nonneg ..)

/-- Scalars of a finite nonnegative real Newton combination. -/
def commonScalar (M p q r : ℕ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ d ∈ range (r + 1), c d * basisScalar M p q d i

theorem commonScalar_nonneg (M p q r : ℕ) (c : ℕ → ℝ)
    (hc : ∀ d, d ≤ r → 0 ≤ c d) (i : ℕ) : 0 ≤ commonScalar M p q r c i := by
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (hc d (by have := Finset.mem_range.mp hd; omega)) (basisScalar_nonneg ..)

theorem commonScalar_antitone (M p q r : ℕ) (c : ℕ → ℝ)
    (hc : ∀ d, d ≤ r → 0 ≤ c d) : Antitone (commonScalar M p q r c) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (basisScalar_antitone M p q d hij)
    (hc d (by have := Finset.mem_range.mp hd; omega))

theorem commonScalar_zero_above (M p q r : ℕ) (c : ℕ → ℝ) {i : ℕ} (hi : r < i) :
    commonScalar M p q r c i = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  have hdi : d < i := by have := Finset.mem_range.mp hd; omega
  simp [basisScalar, incidenceScalar, incidenceSquare_zero_of_large hdi]

end
end CoefficientwiseRigidity.Spectral
