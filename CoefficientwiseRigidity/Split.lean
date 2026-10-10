import Mathlib.Tactic

/-!
Paper K3: the diagonal-exact asymmetric split, with no graph or spectral
assumptions. Finite Newton-cone closure and local bounds are proved in `NewtonSplit`.
-/
namespace CoefficientwiseRigidity.Kernel

def splitF (f g : ℕ → ℚ) : ℕ → ℚ
  | 0 => f 0 * g 0
  | n + 1 => splitF f g n + (f (n + 1) - f n) * g (n + 1)

def splitG (f g : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => splitG f g n + f n * (g (n + 1) - g n)

theorem split_diagonal (f g : ℕ → ℚ) (n : ℕ) :
    splitF f g n + splitG f g n = f n * g n := by
  induction n with
  | zero => simp [splitF, splitG]
  | succ n ih =>
    simp only [splitF, splitG]
    linear_combination ih

theorem split_bound_above (f g : ℕ → ℚ) (hf : Monotone f) (hg : Monotone g)
    (x y : ℕ) (hxy : x ≤ y) : f x * g y ≤ splitF f g x + splitG f g y := by
  induction y, hxy using Nat.le_induction with
  | base => exact (split_diagonal f g x).symm.le
  | succ n hn ih =>
    have hfn := hf hn
    have hgn := hg (Nat.le_succ n)
    have hmul := mul_nonneg (sub_nonneg.mpr hfn) (sub_nonneg.mpr hgn)
    simp only [splitG]
    nlinarith

theorem split_bound_below (f g : ℕ → ℚ) (hf : Monotone f) (hg : Monotone g)
    (x y : ℕ) (hyx : y ≤ x) : f x * g y ≤ splitF f g x + splitG f g y := by
  induction x, hyx using Nat.le_induction with
  | base => exact (split_diagonal f g y).symm.le
  | succ n hn ih =>
    have hfn := hf (Nat.le_succ n)
    have hgn := hg (Nat.le_trans hn (Nat.le_succ n))
    have hmul := mul_nonneg (sub_nonneg.mpr hfn) (sub_nonneg.mpr hgn)
    simp only [splitF]
    nlinarith

theorem split_bound (f g : ℕ → ℚ) (hf : Monotone f) (hg : Monotone g)
    (x y : ℕ) : f x * g y ≤ splitF f g x + splitG f g y := by
  rcases le_total x y with h | h
  · exact split_bound_above f g hf hg x y h
  · exact split_bound_below f g hf hg x y h

theorem splitF_nonneg (f g : ℕ → ℚ) (hf : Monotone f)
    (hf0 : 0 ≤ f 0) (hg0 : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ splitF f g n := by
  induction n with
  | zero => exact mul_nonneg hf0 (hg0 0)
  | succ n ih =>
    exact add_nonneg ih (mul_nonneg (sub_nonneg.mpr (hf (Nat.le_succ n))) (hg0 _))

theorem splitG_nonneg (f g : ℕ → ℚ) (hg : Monotone g)
    (hf0 : ∀ n, 0 ≤ f n) (n : ℕ) : 0 ≤ splitG f g n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    exact add_nonneg ih (mul_nonneg (hf0 _) (sub_nonneg.mpr (hg (Nat.le_succ n))))

theorem splitF_difference (f g : ℕ → ℚ) (n : ℕ) :
    splitF f g (n + 1) - splitF f g n = (f (n + 1) - f n) * g (n + 1) := by
  simp [splitF]

theorem splitF_reserve (f g : ℕ → ℚ) (hf : Monotone f)
    (hg0 : ∀ n, 0 ≤ g n) (n : ℕ) :
    (f (n + 1) - f n) * (g (n + 1) - g n) ≤
      splitF f g (n + 1) - splitF f g n := by
  rw [splitF_difference]
  have := mul_nonneg (sub_nonneg.mpr (hf (Nat.le_succ n))) (hg0 n)
  nlinarith

theorem splitF_strict_step (f g : ℕ → ℚ) (n : ℕ)
    (hf : f n < f (n + 1)) (hg : 0 < g (n + 1)) :
    splitF f g n < splitF f g (n + 1) := by
  have := mul_pos (sub_pos.mpr hf) hg
  simp only [splitF]
  linarith

end CoefficientwiseRigidity.Kernel
