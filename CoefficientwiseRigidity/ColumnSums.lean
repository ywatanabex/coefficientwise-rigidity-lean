import CoefficientwiseRigidity.IncreasingProductCone

/-! Exact unnormalised subset sums, eliminating the first listed column first. -/
namespace CoefficientwiseRigidity.Intersections
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {M : ℕ}

/-- The first column is the innermost sum. With a duplicate-free list this
sums each independent choice once, retaining all unlisted coordinates. -/
def sumColumns (q : V → ℕ) : List V → ((V → Finset (Fin M)) → ℚ) → (V → Finset (Fin M)) → ℚ
  | [], F, Q => F Q
  | v :: L, F, Q => sumColumns q L
      (fun R => ∑ A : Finset (Fin M), if A.card = q v then F (Function.update R v A) else 0) Q

theorem sumColumns_mono (q : V → ℕ) (L : List V) {F G : (V → Finset (Fin M)) → ℚ}
    (h : ∀ Q, F Q ≤ G Q) (Q : V → Finset (Fin M)) : sumColumns q L F Q ≤ sumColumns q L G Q := by
  induction L generalizing F G with
  | nil => exact h Q
  | cons v L ih =>
    apply ih
    intro R
    apply Finset.sum_le_sum
    intro A _
    split_ifs
    · exact h _
    · exact le_refl _

theorem sumColumns_congr (q : V → ℕ) (L : List V) {F G : (V → Finset (Fin M)) → ℚ}
    (h : ∀ Q, F Q = G Q) (Q : V → Finset (Fin M)) : sumColumns q L F Q = sumColumns q L G Q :=
  le_antisymm (sumColumns_mono q L (fun Q => (h Q).le) Q)
    (sumColumns_mono q L (fun Q => (h Q).ge) Q)

theorem sumColumns_nonneg (q : V → ℕ) (L : List V) {F : (V → Finset (Fin M)) → ℚ}
    (h : ∀ Q, 0 ≤ F Q) (Q : V → Finset (Fin M)) : 0 ≤ sumColumns q L F Q := by
  induction L generalizing F with
  | nil => exact h Q
  | cons v L ih =>
    apply ih
    intro R
    apply Finset.sum_nonneg
    intro A _
    split_ifs
    · exact h _
    · exact le_refl _

theorem sumColumns_sum {T : Type*} (s : Finset T) (q : V → ℕ) (L : List V)
    (F : T → (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q L (fun R => ∑ t ∈ s, F t R) Q = ∑ t ∈ s, sumColumns q L (F t) Q := by
  induction L generalizing F with
  | nil => rfl
  | cons v L ih =>
    simp only [sumColumns]
    rw [← ih]
    apply sumColumns_congr
    intro R
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    split_ifs <;> simp

theorem sumColumns_append (q : V → ℕ) (L K : List V)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q (L ++ K) F Q = sumColumns q K (fun R => sumColumns q L F R) Q := by
  induction L generalizing F with
  | nil => rfl
  | cons v L ih => exact ih _

theorem sumColumns_swap (q : V → ℕ) (a b : V) (L : List V)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q (a :: b :: L) F Q = sumColumns q (b :: a :: L) F Q := by
  by_cases hab : a = b
  · subst b; rfl
  simp only [sumColumns]
  apply sumColumns_congr
  intro R
  have hd (p : Prop) [Decidable p] (f : Finset (Fin M) → ℚ) :
      (if p then ∑ x, f x else 0) = ∑ x, if p then f x else 0 := by
    by_cases hp : p <;> simp [hp]
  simp_rw [hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  by_cases ha : A.card = q a <;> by_cases hb : B.card = q b <;> simp [ha,hb,Function.update_comm hab]

theorem sumColumns_perm (q : V → ℕ) {L K : List V} (h : L.Perm K)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q L F Q = sumColumns q K F Q := by
  induction h generalizing F with
  | nil => rfl
  | cons v h ih => exact ih _
  | swap a b L => exact sumColumns_swap q b a L F Q
  | trans h h' ih ih' => exact (ih F).trans (ih' F)

/-- Canonical sum over a finite set of columns, independent of enumeration. -/
def sumSet (q : V → ℕ) (U : Finset V) (F : (V → Finset (Fin M)) → ℚ)
    (Q : V → Finset (Fin M)) : ℚ := sumColumns q U.toList F Q


end
end CoefficientwiseRigidity.Intersections
