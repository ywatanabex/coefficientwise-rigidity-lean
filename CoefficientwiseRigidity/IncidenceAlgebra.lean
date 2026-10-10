import CoefficientwiseRigidity.SliceIncidence

/-! Composition and adjoints of actual incidence lifts, with exact harmonic scalars. -/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

def lower (j : ℕ) : Space M →ₗ[ℝ] Space M := down ^ j
def coIncidenceLift (j : ℕ) : Space M →ₗ[ℝ] Space M :=
  (j.factorial : ℝ)⁻¹ • lower j

@[simp] theorem lower_zero (f : Space M) : lower 0 f = f := rfl

theorem lower_succ (j : ℕ) (f : Space M) : lower (j + 1) f = lower j (down f) := by
  simp only [lower, pow_succ, LinearMap.mul_apply]

theorem counting_raise_lower (j : ℕ) (f g : Space M) :
    counting (raise j f) g = counting f (lower j g) := by
  induction j generalizing g with
  | zero => rfl
  | succ j ih => rw [raise_succ, counting_up, ih, lower_succ]

theorem counting_incidence_adjoint (j : ℕ) (f g : Space M) :
    counting (incidenceLift j f) g = counting f (coIncidenceLift j g) := by
  simp only [incidenceLift, coIncidenceLift, LinearMap.smul_apply,
    counting_smul_left, counting_smul_right, counting_raise_lower]

theorem incidenceLift_comp (a b : ℕ) (f : Space M) :
    incidenceLift a (incidenceLift b f) = ((a + b).choose b : ℝ) • incidenceLift (a + b) f := by
  have ha : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hab : ((a + b).factorial : ℝ) ≠ 0 := by exact_mod_cast (a + b).factorial_ne_zero
  have hf : ((a + b).choose b : ℝ) * a.factorial * b.factorial = (a + b).factorial := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial a b
  simp only [incidenceLift, LinearMap.smul_apply, map_smul, smul_smul]
  have he : raise a (raise b f) = raise (a + b) f := by
    simp only [raise, pow_add, LinearMap.mul_apply]
  rw [he]
  congr 1
  field_simp
  nlinarith [hf]

theorem down_incidenceLift {i : ℕ} {h : Space M} (hh : Harmonic i h) (j : ℕ) :
    down (incidenceLift (j + 1) h) =
      ((M : ℝ) - 2 * i - j) • incidenceLift j h := by
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  simp only [incidenceLift, LinearMap.smul_apply, map_smul, down_raise hh, smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem coIncidenceLift_succ (n : ℕ) (f : Space M) :
    coIncidenceLift (n + 1) f = ((n : ℝ) + 1)⁻¹ • coIncidenceLift n (down f) := by
  simp only [coIncidenceLift, LinearMap.smul_apply, lower_succ, smul_smul,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  rw [mul_comm]

/-- The exact lowering scalar on unnormalized harmonic incidence lifts. -/
theorem coIncidenceLift_incidenceLift {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : 2 * i ≤ M) (j n : ℕ) (hjn : j + n ≤ M - 2 * i) :
    coIncidenceLift n (incidenceLift (j + n) h) =
      ((M - 2 * i - j).choose n : ℝ) • incidenceLift j h := by
  induction n with
  | zero => simp [coIncidenceLift, incidenceLift, lower, raise]
  | succ n ih =>
    rw [coIncidenceLift_succ, ← Nat.add_assoc, down_incidenceLift hh,
      map_smul, ih (by omega), smul_smul, smul_smul]
    congr 1
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have he : (M : ℝ) - 2 * i - (j + n) = ((M - 2 * i - j - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : n ≤ M - 2 * i - j),
        Nat.cast_sub (by omega : j ≤ M - 2 * i), Nat.cast_sub hi, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [Nat.cast_add, he]
    have hc : (((M - 2 * i - j).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) =
        ((M - 2 * i - j).choose n : ℝ) * (M - 2 * i - j - n : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq (M - 2 * i - j) n
    field_simp
    nlinarith [hc]

theorem lower_raise_excess {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (n j : ℕ) (hjn : j < n) : lower n (raise j h) = 0 := by
  apply (counting_self_eq_zero_iff _).mp
  rw [← counting_raise_lower]
  exact counting_raise_excess hh _ n j hjn

theorem coIncidenceLift_excess {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (n j : ℕ) (hjn : j < n) : coIncidenceLift n (incidenceLift j h) = 0 := by
  simp only [coIncidenceLift, incidenceLift, LinearMap.smul_apply, map_smul,
    lower_raise_excess hh n j hjn, smul_zero]

end
end CoefficientwiseRigidity.Spectral
