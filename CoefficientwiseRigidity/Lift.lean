import CoefficientwiseRigidity.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename

/-! F1 for the actual graph lift and the variable projection π, not an abstract count. -/
namespace CoefficientwiseRigidity
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def liftGraph (X : Cover G M) : SimpleGraph (V × Fin M) where
  Adj x y := G.Adj x.1 y.1 ∧ X.transport x.1 y.1 x.2 = y.2
  symm := by
    intro x y h
    refine ⟨G.symm h.1, ?_⟩
    rw [X.reverse h.1, ← h.2]
    exact Equiv.symm_apply_apply _ _
  loopless := fun x h => G.loopless x.1 h.1

def selectedLift (S : Assignment V M) : Finset (V × Fin M) :=
  Finset.univ.filter (fun x => x.2 ∈ S x.1)

omit [DecidableEq V] in
@[simp] theorem mem_selectedLift (S : Assignment V M) (v : V) (i : Fin M) :
    (v, i) ∈ selectedLift S ↔ i ∈ S v := by simp [selectedLift]

def assignmentLiftEquiv : Assignment V M ≃ Finset (V × Fin M) where
  toFun := selectedLift
  invFun I v := Finset.univ.filter (fun i => (v, i) ∈ I)
  left_inv S := by funext v; ext i; simp
  right_inv I := by ext x; rcases x with ⟨v, i⟩; simp

omit [DecidableEq V] in
theorem legal_iff_lift_independent (X : Cover G M) (S : Assignment V M) :
    EdgeLegal X S ↔ Independent (liftGraph X) (selectedLift S) := by
  constructor
  · intro hs x hx y hy hxy
    have hxi : x.2 ∈ S x.1 := by simpa [selectedLift] using hx
    have hyi : y.2 ∈ S y.1 := by simpa [selectedLift] using hy
    exact hs x.1 y.1 hxy.1 x.2 hxi (hxy.2.symm ▸ hyi)
  · intro hs u v huv i hi hj
    exact hs (u, i) ((mem_selectedLift S u i).mpr hi)
      (v, X.transport u v i) ((mem_selectedLift S v _).mpr hj) ⟨huv, rfl⟩

theorem projected_exponent (S : Assignment V M) :
    (exponent (fun x : V × Fin M => if x ∈ selectedLift S then 1 else 0)).mapDomain Prod.fst =
      exponent (fun v => (S v).card) := by
  ext v
  rw [Finsupp.mapDomain, Finsupp.sum_fintype]
  · simp [Fintype.sum_prod_type, Finsupp.single_apply, Finset.sum_apply]
  · intro x
    simp

theorem rename_vertexMonomial (S : Assignment V M) :
    MvPolynomial.rename Prod.fst (vertexMonomial (selectedLift S)) =
      MvPolynomial.monomial (exponent (fun v => (S v).card)) (1 : ℕ) := by
  rw [vertexMonomial, MvPolynomial.rename_monomial, projected_exponent]

/-- The occupation polynomial is exactly the projected independent-set polynomial. -/
theorem projected_lift_polynomial (X : Cover G M) :
    MvPolynomial.rename Prod.fst (independencePolynomial (liftGraph X)) =
      coverPolynomial X := by
  classical
  unfold independencePolynomial
  rw [map_sum]
  rw [← assignmentLiftEquiv.sum_comp]
  unfold coverPolynomial
  apply Finset.sum_congr rfl
  intro S _
  change MvPolynomial.rename Prod.fst
    (if Independent (liftGraph X) (selectedLift S) then vertexMonomial (selectedLift S) else 0) = _
  by_cases h : EdgeLegal X S
  · have hi := (legal_iff_lift_independent X S).mp h
    simp only [if_pos hi, if_pos h]
    exact rename_vertexMonomial S
  · have hi : ¬ Independent (liftGraph X) (selectedLift S) :=
      fun hi => h ((legal_iff_lift_independent X S).mpr hi)
    simp [hi, h]

theorem coefficient_eq_projected_lift (X : Cover G M) (a : V → ℕ) :
    coefficient X a = MvPolynomial.coeff (exponent a)
      (MvPolynomial.rename Prod.fst (independencePolynomial (liftGraph X))) := by
  rw [projected_lift_polynomial, coeff_coverPolynomial]

theorem flat_polynomial_identity (X : Cover G M) (h : Flat X) :
    MvPolynomial.rename Prod.fst (independencePolynomial (liftGraph X)) =
      independencePolynomial G ^ M := by
  rw [projected_lift_polynomial, flat_coverPolynomial_eq X h, trivial_coverPolynomial]

end CoefficientwiseRigidity
