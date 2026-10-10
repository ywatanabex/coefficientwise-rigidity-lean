import CoefficientwiseRigidity.SliceOperators
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
Harmonic raising, its exact counting normalization and orthogonality.
No spectral decomposition or multiplicity-one theorem is assumed here.
-/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

def Harmonic (i : ℕ) (f : Space M) : Prop := OnLevel i f ∧ down f = 0

def raise (j : ℕ) : Space M →ₗ[ℝ] Space M := up ^ j

@[simp] theorem raise_zero (f : Space M) : raise 0 f = f := rfl

theorem raise_succ (j : ℕ) (f : Space M) : raise (j + 1) f = up (raise j f) := by
  simp only [raise, pow_succ', LinearMap.mul_apply]

theorem onLevel_raise {i : ℕ} {f : Space M} (hf : OnLevel i f) (j : ℕ) :
    OnLevel (i + j) (raise j f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih => simpa only [raise_succ, Nat.add_assoc] using onLevel_up ih

/-- The scalar is in ℝ, so no truncated natural subtraction enters the ladder identity. -/
theorem down_raise {i : ℕ} {h : Space M} (hh : Harmonic i h) (j : ℕ) :
    down (raise (j + 1) h) =
      (((j : ℝ) + 1) * ((M : ℝ) - 2 * i - j)) • raise j h := by
  induction j with
  | zero =>
    rw [raise_succ, raise_zero, commutator_onLevel hh.1, hh.2, map_zero, zero_add]
    simp
  | succ j ih =>
    rw [raise_succ (j + 1), commutator_onLevel (onLevel_raise hh.1 (j + 1)),
      ih, map_smul, ← raise_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← add_smul]
    congr 1
    ring

theorem counting_raise_succ {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (f : Space M) (j : ℕ) :
    counting (raise (j + 1) f) (raise (j + 1) h) =
      (((j : ℝ) + 1) * ((M : ℝ) - 2 * i - j)) * counting (raise j f) (raise j h) := by
  rw [raise_succ j f, counting_up, down_raise hh, counting_smul_right]

theorem counting_raise_product {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (f : Space M) (j : ℕ) :
    counting (raise j f) (raise j h) =
      (∏ l ∈ range j, (((l : ℝ) + 1) * ((M : ℝ) - 2 * i - l))) * counting f h := by
  induction j with
  | zero => simp
  | succ j ih => rw [counting_raise_succ hh, ih, Finset.prod_range_succ]; ring

/-- Exact norm factor, including zero blocks beyond the end of the ladder. -/
theorem counting_raise {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : 2 * i ≤ M) (f : Space M) (j : ℕ) :
    counting (raise j f) (raise j h) =
      ((j.factorial : ℝ) ^ 2 * ((M - 2 * i).choose j : ℝ)) * counting f h := by
  rw [counting_raise_product hh, Finset.prod_mul_distrib]
  have hfirst : (∏ l ∈ range j, ((l : ℝ) + 1)) = (j.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial j
  have hcast : (M : ℝ) - 2 * i = ((M - 2 * i : ℕ) : ℝ) := by
    rw [Nat.cast_sub hi, Nat.cast_mul, Nat.cast_ofNat]
  rw [hfirst, hcast, Finset.prod_range_natCast_sub,
    ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

theorem counting_self_raise {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : 2 * i ≤ M) (j : ℕ) :
    counting (raise j h) (raise j h) =
      ((j.factorial : ℝ) ^ 2 * ((M - 2 * i).choose j : ℝ)) * counting h h :=
  counting_raise hh hi h j

/-- More raising operators on the left than on the harmonic right give zero. -/
theorem counting_raise_excess {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (f : Space M) (j l : ℕ) (hlj : l < j) :
    counting (raise j f) (raise l h) = 0 := by
  induction l generalizing j with
  | zero =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [raise_succ, raise_zero, counting_up, hh.2, counting_zero_right]
  | succ l ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [raise_succ j f, counting_up, down_raise hh, counting_smul_right,
      ih j (by omega), mul_zero]

/-- Different-degree harmonic blocks are orthogonal at every common level. -/
theorem harmonic_lifts_orthogonal {i l k : ℕ} {f h : Space M}
    (hh : Harmonic l h) (hil : i < l) (hlk : l ≤ k) :
    counting (raise (k - i) f) (raise (k - l) h) = 0 :=
  counting_raise_excess hh f _ _ (by omega)

/-- The factorial-scaled raising map used in the paper's incidence normalization. -/
def incidenceLift (j : ℕ) : Space M →ₗ[ℝ] Space M :=
  (j.factorial : ℝ)⁻¹ • raise j

theorem counting_incidenceLift {i : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : 2 * i ≤ M) (f : Space M) (j : ℕ) :
    counting (incidenceLift j f) (incidenceLift j h) =
      ((M - 2 * i).choose j : ℝ) * counting f h := by
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  simp only [incidenceLift, LinearMap.smul_apply, counting_smul_right]
  rw [counting_symm, counting_smul_right, counting_symm (raise j h), counting_raise hh hi]
  field_simp
  ring

theorem raise_injective_on_harmonic {i j : ℕ} (hi : 2 * i ≤ M) (hj : j ≤ M - 2 * i)
    {h : Space M} (hh : Harmonic i h) (hz : raise j h = 0) : h = 0 := by
  have he := counting_self_raise hh hi j
  rw [hz, counting_zero_right] at he
  have hp : 0 < (j.factorial : ℝ) ^ 2 * ((M - 2 * i).choose j : ℝ) := by
    apply mul_pos
    · exact sq_pos_of_pos (by exact_mod_cast j.factorial_pos)
    · exact_mod_cast Nat.choose_pos hj
  exact (counting_self_eq_zero_iff h).mp ((mul_eq_zero.mp he.symm).resolve_left (ne_of_gt hp))

theorem raise_eq_zero_above {i j : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : 2 * i ≤ M) (hj : M - 2 * i < j) : raise j h = 0 := by
  apply (counting_self_eq_zero_iff _).mp
  rw [counting_self_raise hh hi, Nat.choose_eq_zero_of_lt hj]
  simp

end
end CoefficientwiseRigidity.Spectral
