import CoefficientwiseRigidity.Gauge
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A concrete occupation generating polynomial and its coefficient theorem. -/
namespace CoefficientwiseRigidity
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def EdgeLegal (X : Cover G M) (S : Assignment V M) : Prop :=
  ∀ u v, G.Adj u v → ∀ i ∈ S u, X.transport u v i ∉ S v

noncomputable def exponent (a : V → ℕ) : V →₀ ℕ := Finsupp.equivFunOnFinite.symm a

omit [DecidableEq V] in
@[simp] theorem exponent_apply (a : V → ℕ) (v : V) : exponent a v = a v := by
  simp [exponent]

omit [DecidableEq V] in
theorem exponent_eq_iff (a b : V → ℕ) : exponent a = exponent b ↔ ∀ v, a v = b v := by
  constructor
  · intro h v
    simpa using congrArg (fun f : V →₀ ℕ => f v) h
  · intro h
    ext v
    exact h v

/-- The occupation polynomial obtained by summing each legal selection once. -/
noncomputable def coverPolynomial (X : Cover G M) : MvPolynomial V ℕ := by
  classical
  exact ∑ S : Assignment V M, if EdgeLegal X S then
    MvPolynomial.monomial (exponent (fun v => (S v).card)) 1 else 0

theorem coeff_coverPolynomial (X : Cover G M) (a : V → ℕ) :
    MvPolynomial.coeff (exponent a) (coverPolynomial X) = coefficient X a := by
  classical
  rw [coverPolynomial, MvPolynomial.coeff_sum]
  unfold coefficient
  rw [Fintype.card_subtype, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases he : EdgeLegal X S
  · by_cases hr : ∀ v, (S v).card = a v
    · have had : Admissible X a S := ⟨hr, he⟩
      simp [he, had, exponent_eq_iff, hr]
    · have had : ¬ Admissible X a S := fun h => hr h.1
      simp [he, had, exponent_eq_iff, hr]
  · have had : ¬ Admissible X a S := fun h => he h.2
    simp [he, had]

theorem coverPolynomial_eq_of_gauge (X Y : Cover G M)
    (h : ∀ a, GaugeEquivalent X Y a) : coverPolynomial X = coverPolynomial Y := by
  apply MvPolynomial.ext
  intro d
  have hd : exponent (fun v => d v) = d := by ext v; rfl
  rw [← hd, coeff_coverPolynomial, coeff_coverPolynomial]
  exact coefficient_eq_of_gauge X Y _ (h _)

theorem flat_coverPolynomial_eq (X : Cover G M) (h : Flat X) :
    coverPolynomial X = coverPolynomial (trivialCover G M) := by
  apply MvPolynomial.ext
  intro d
  have hd : exponent (fun v => d v) = d := by ext v; rfl
  rw [← hd, coeff_coverPolynomial, coeff_coverPolynomial]
  exact activeFlat_coefficient_eq X _ (flat_activeFlat X _ h)

def Independent (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v

noncomputable def vertexMonomial (I : Finset V) : MvPolynomial V ℕ :=
  MvPolynomial.monomial (exponent (fun v => if v ∈ I then 1 else 0)) 1

/-- The usual multivariate independent-set polynomial, with coefficient one per set. -/
noncomputable def independencePolynomial (G : SimpleGraph V) : MvPolynomial V ℕ := by
  classical
  exact ∑ I : Finset V, if Independent G I then vertexMonomial I else 0

def transposeAssignment (S : Assignment V M) (i : Fin M) : Finset V :=
  Finset.univ.filter (fun v => i ∈ S v)

omit [DecidableEq V] in
@[simp] theorem mem_transposeAssignment (S : Assignment V M) (i : Fin M) (v : V) :
    v ∈ transposeAssignment S i ↔ i ∈ S v := by simp [transposeAssignment]

def assignmentTransposeEquiv : Assignment V M ≃ (Fin M → Finset V) where
  toFun := transposeAssignment
  invFun T v := Finset.univ.filter (fun i => v ∈ T i)
  left_inv S := by funext v; ext i; simp
  right_inv T := by funext i; ext v; simp

omit [DecidableEq V] in
theorem legal_iff_independent_layers (S : Assignment V M) :
    EdgeLegal (trivialCover G M) S ↔ ∀ i, Independent G (transposeAssignment S i) := by
  constructor
  · intro hs i u hu v hv huv
    exact hs u v huv i ((mem_transposeAssignment S i u).mp hu)
      ((mem_transposeAssignment S i v).mp hv)
  · intro hs u v huv i hi hj
    exact hs i u ((mem_transposeAssignment S i u).mpr hi)
      v ((mem_transposeAssignment S i v).mpr hj) huv

theorem product_vertexMonomial (S : Assignment V M) :
    (∏ i, vertexMonomial (transposeAssignment S i)) =
      MvPolynomial.monomial (exponent (fun v => (S v).card)) 1 := by
  unfold vertexMonomial
  rw [← MvPolynomial.monomial_sum_one]
  have he : (∑ i : Fin M, exponent (fun v => if v ∈ transposeAssignment S i then 1 else 0)) =
      exponent (fun v => (S v).card) := by
    ext v
    simp
  rw [he]

theorem product_independent_weights (S : Assignment V M) :
    (∏ i, if Independent G (transposeAssignment S i) then
      vertexMonomial (transposeAssignment S i) else 0) =
    if EdgeLegal (trivialCover G M) S then
      MvPolynomial.monomial (exponent (fun v => (S v).card)) 1 else 0 := by
  classical
  by_cases h : EdgeLegal (trivialCover G M) S
  · have hi := (legal_iff_independent_layers S).mp h
    simp only [if_pos h, if_pos (hi _)]
    exact product_vertexMonomial S
  · rw [if_neg h]
    have hn : ¬ ∀ i, Independent G (transposeAssignment S i) :=
      fun ha => h ((legal_iff_independent_layers S).mpr ha)
    push_neg at hn
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The coefficient-count normalization is exactly p_G^M, with no factorial factor. -/
theorem trivial_coverPolynomial (G : SimpleGraph V) (M : ℕ) :
    coverPolynomial (trivialCover G M) = independencePolynomial G ^ M := by
  classical
  symm
  calc
    independencePolynomial G ^ M = ∏ _i : Fin M, independencePolynomial G := by simp
    _ = ∑ T : Fin M → Finset V,
        ∏ i, if Independent G (T i) then vertexMonomial (T i) else 0 :=
      Fintype.prod_sum (fun (_i : Fin M) (I : Finset V) =>
        if Independent G I then vertexMonomial I else 0)
    _ = ∑ S : Assignment V M, ∏ i,
        if Independent G (transposeAssignment S i) then
          vertexMonomial (transposeAssignment S i) else 0 :=
      (assignmentTransposeEquiv.sum_comp _).symm
    _ = coverPolynomial (trivialCover G M) := by
      unfold coverPolynomial
      exact Finset.sum_congr rfl (fun S _ => product_independent_weights S)

theorem ordinary_eq_polynomial_coefficient (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) :
    ordinary G M a = MvPolynomial.coeff (exponent a) (independencePolynomial G ^ M) := by
  rw [← trivial_coverPolynomial, coeff_coverPolynomial]
  rfl

end CoefficientwiseRigidity
