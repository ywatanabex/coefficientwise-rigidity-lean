import CoefficientwiseRigidity.Polynomial

/-! The manuscript reserve, including its negative-exponent convention. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

theorem coefficient_zero_profile {G : SimpleGraph V} {M : ℕ} (X : Cover G M) :
    coefficient X (fun _ => 0) = 1 := by
  let e : Configuration X (fun _ => 0) ≃ Unit := {
    toFun := fun _ => Unit.unit
    invFun := fun _ => ⟨fun _ => ∅, ⟨fun _ => rfl, by simp⟩⟩
    left_inv := by
      intro S
      apply Subtype.ext
      funext v
      exact (Finset.card_eq_zero.mp (S.property.1 v)).symm
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (by simp)

theorem reserve_singleton (G : SimpleGraph V) (M : ℕ) : reserve G M (fun _ => 1) = 1 :=
  coefficient_zero_profile (trivialCover G (M - 2))

/-- Coefficient of x^a in x^V p_G^(M-2). A zero occupation gives zero. -/
def paperReserve (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) : ℕ :=
  if Positive a then reserve G M a else 0

theorem paperReserve_eq_reserve (G : SimpleGraph V) (M : ℕ) (a : V → ℕ)
    (hp : Positive a) : paperReserve G M a = reserve G M a := by
  simp [paperReserve, hp]

theorem paperReserve_eq_zero (G : SimpleGraph V) (M : ℕ) (a : V → ℕ)
    (v : V) (hv : a v = 0) : paperReserve G M a = 0 := by
  have hp : ¬ Positive a := by intro h; have := h v; omega
  simp [paperReserve, hp]

/-- Exact polynomial normalization, valid also at zero occupations and M=2. -/
theorem paperReserve_eq_polynomial_coefficient (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) :
    paperReserve G M a = MvPolynomial.coeff (exponent a)
      (MvPolynomial.monomial (exponent (fun _ : V => 1)) 1 *
        independencePolynomial G ^ (M - 2)) := by
  rw [MvPolynomial.coeff_monomial_mul']
  have hpos : exponent (fun _ : V => 1) ≤ exponent a ↔ Positive a := by
    change (∀ v, 1 ≤ a v) ↔ ∀ v, 0 < a v
    exact ⟨fun h v => h v, fun h v => h v⟩
  have hsub : exponent a - exponent (fun _ : V => 1) =
      exponent (fun v => a v - 1) := by ext v; rfl
  by_cases hp : Positive a
  · rw [if_pos (hpos.mpr hp), one_mul, hsub, paperReserve_eq_reserve G M a hp]
    exact ordinary_eq_polynomial_coefficient G (M - 2) (fun v => a v - 1)
  · simp [paperReserve, hp, hpos]

end
end CoefficientwiseRigidity
