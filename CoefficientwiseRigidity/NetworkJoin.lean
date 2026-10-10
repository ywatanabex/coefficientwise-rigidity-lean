import CoefficientwiseRigidity.NetworkGauge

/-!
Exact fibre factorization for two disjoint concrete networks joined by two
parallel factors at their roots. Edge multiplicities and scalars are retained.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V W : Type*} {p : V → ℕ} {q : W → ℕ}

def sumState (A : State M p) (B : State M q) : State M (Sum.elim p q)
  | Sum.inl v => A v
  | Sum.inr w => B w

def sumStateEquiv : State M (Sum.elim p q) ≃ State M p × State M q where
  toFun S := ⟨fun v => S (Sum.inl v), fun w => S (Sum.inr w)⟩
  invFun S := sumState S.1 S.2
  left_inv S := by funext v; cases v <;> rfl
  right_inv S := rfl

theorem sum_sumState [Fintype V] [Fintype W] (F : State M (Sum.elim p q) → ℚ) :
    ∑ S, F S = ∑ A : State M p, ∑ B : State M q, F (sumState A B) := by
  classical
  calc
    _ = ∑ S : State M p × State M q, F (sumState S.1 S.2) :=
      Fintype.sum_equiv sumStateEquiv _ _ (fun S => congrArg F
        (sumStateEquiv.left_inv S).symm)
    _ = _ := Fintype.sum_prod_type _

def Edge.inl (e : Edge M p) (q : W → ℕ) : Edge M (Sum.elim p q) :=
  ⟨Sum.inl e.left, Sum.inl e.right, fun h => e.distinct (Sum.inl.inj h), e.kernels⟩

def Edge.inr (e : Edge M q) (p : V → ℕ) : Edge M (Sum.elim p q) :=
  ⟨Sum.inr e.left, Sum.inr e.right, fun h => e.distinct (Sum.inr.inj h), e.kernels⟩

def Net.disjointUnion (N : Net M p) (K : Net M q) : Net M (Sum.elim p q) :=
  ⟨N.scalar * K.scalar, mul_nonneg N.scalar_nonneg K.scalar_nonneg,
    N.edges.map (fun e => e.inl q) ++ K.edges.map (fun e => e.inr p)⟩

theorem weight_disjointUnion (N : Net M p) (K : Net M q) (b : Bool)
    (A : State M p) (B : State M q) :
    weight (N.disjointUnion K).edges b (sumState A B) =
      weight N.edges b A * weight K.edges b B := by
  simp [Net.disjointUnion, weight, Edge.inl, Edge.inr, Edge.eval, sumState, Function.comp_def]

/-- Two parallel factors, not a relaxed single-edge substitute. -/
def Net.joinTwo (N : Net M p) (K : Net M q) (u : V) (v : W)
    (e f : GainEntry M (p u) (q v)) : Net M (Sum.elim p q) :=
  ((N.disjointUnion K).addEdge (Sum.inl u) (Sum.inr v) (by simp) [f]).addEdge
    (Sum.inl u) (Sum.inr v) (by simp) [e]

theorem Net.sum_pinnedValue_mul [Fintype V] (N : Net M p) (u : V)
    (b : Bool) (F : Slice M (p u) → ℚ) :
    (∑ A, N.pinnedValue u A b * F A) =
      N.scalar * ∑ S : State M p, weight N.edges b S * F (S u) := by
  classical
  simp only [Net.pinnedValue, mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp

/-- The precise unnormalized two-root fibre identity for the actual joined net. -/
theorem Net.joinTwo_value [Fintype V] [Fintype W]
    (N : Net M p) (K : Net M q) (u : V) (v : W)
    (e f : GainEntry M (p u) (q v)) (b : Bool) :
    (N.joinTwo K u v e f).value b =
      ∑ A : Slice M (p u), ∑ B : Slice M (q v),
        N.pinnedValue u A b * K.pinnedValue v B b * kernel b [e] A B * kernel b [f] A B := by
  classical
  change (N.scalar * K.scalar) * (∑ S, kernel b [e] (S (.inl u)) (S (.inr v)) *
    (kernel b [f] (S (.inl u)) (S (.inr v)) * weight (N.disjointUnion K).edges b S)) = _
  rw [sum_sumState]
  simp only [weight_disjointUnion, sumState]
  symm
  calc
    _ = ∑ A, N.pinnedValue u A b *
        ∑ B, K.pinnedValue v B b * (kernel b [e] A B * kernel b [f] A B) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = ∑ A, N.pinnedValue u A b *
        (K.scalar * ∑ T, weight K.edges b T * (kernel b [e] A (T v) * kernel b [f] A (T v))) := by
      simp_rw [K.sum_pinnedValue_mul v b]
    _ = N.scalar * ∑ S, weight N.edges b S *
        (K.scalar * ∑ T, weight K.edges b T *
          (kernel b [e] (S u) (T v) * kernel b [f] (S u) (T v))) :=
      N.sum_pinnedValue_mul u b _
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      ring

end
end CoefficientwiseRigidity.Network
