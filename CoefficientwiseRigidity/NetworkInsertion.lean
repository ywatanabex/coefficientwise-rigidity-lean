import CoefficientwiseRigidity.Networks
import CoefficientwiseRigidity.KernelInsertion

/-!
W2 for actual finite network sums, including any prescribed ordinary root set.
The original scalar is retained; every edge-list entry is replaced by its
forward difference. No graph-class or connectivity premise is needed here.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V : Type*} {p : V → ℕ}

def insertState (A : State M p) : State (M + 2) (fun v => p v + 1) :=
  fun v => insertSlice (A v)

theorem insertState_injective : Function.Injective (@insertState M V p) := by
  intro A B h
  funext v
  exact insertSlice_injective (congrFun h v)

def Edge.reduce (e : Edge (M + 2) (fun v => p v + 1)) (hp : ∀ v, p v ≤ M) : Edge M p :=
  ⟨e.left, e.right, e.distinct, reduceList e.kernels (hp e.left) (hp e.right)⟩

def Net.reduce (N : Net (M + 2) (fun v => p v + 1)) (hp : ∀ v, p v ≤ M) : Net M p :=
  ⟨N.scalar, N.scalar_nonneg, N.edges.map (fun e => e.reduce hp)⟩

theorem weight_reduce_insertion (E : List (Edge (M + 2) (fun v => p v + 1)))
    (hp : ∀ v, p v ≤ M) (A : State M p) :
    weight (E.map fun e => e.reduce hp) true A ≤ weight E true (insertState A) := by
  induction E with
  | nil => exact le_refl _
  | cons e E ih =>
    apply mul_le_mul
      (reduceList_insertion e.kernels (hp e.left) (hp e.right) (A e.left) (A e.right)) ih
      (weight_nonneg _ _ _) (kernel_nonneg true e.kernels _ _)

/-- W2's ordinary unpinned inequality, for arbitrary finite gain-list networks. -/
theorem Net.reduce_value_le [Fintype V] (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) : (N.reduce hp).value true ≤ N.value true := by
  classical
  apply mul_le_mul_of_nonneg_left _ N.scalar_nonneg
  exact sum_le_of_injection insertState insertState_injective _ _
    (weight_nonneg N.edges true) (weight_reduce_insertion N.edges hp)

def permuteState (σ : Equiv.Perm (Fin M)) (A : State M p) : State M p :=
  fun v => permuteSlice σ (A v)

def statePerm (σ : Equiv.Perm (Fin M)) : Equiv.Perm (State M p) where
  toFun := permuteState σ
  invFun := permuteState σ.symm
  left_inv A := by funext v; simp [permuteState, ← permuteSlice_trans]
  right_inv A := by funext v; simp [permuteState, ← permuteSlice_trans]

theorem weight_ordinary_permute (E : List (Edge M p))
    (σ : Equiv.Perm (Fin M)) (A : State M p) :
    weight E true (permuteState σ A) = weight E true A := by
  simp [weight, Edge.eval, kernel, listOrdinary, GainEntry.ordinary, permuteState,
    overlap_permute]

def Net.pinnedValue [Fintype V] (N : Net M p) (r : V) (A : Slice M (p r))
    (ordinary : Bool) : ℚ := by
  classical
  exact N.scalar * ∑ S : State M p, if S r = A then weight N.edges ordinary S else 0

theorem Net.pinnedValue_nonneg [Fintype V] (N : Net M p)
    (r : V) (A : Slice M (p r)) (b : Bool) : 0 ≤ N.pinnedValue r A b := by
  classical
  apply mul_nonneg N.scalar_nonneg
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact weight_nonneg _ _ _
  · exact le_refl _

/-- Ordinary rooted sums are constant over the entire root slice. -/
theorem Net.pinnedValue_ordinary_constant [Fintype V] (N : Net M p)
    (r : V) (A B : Slice M (p r)) : N.pinnedValue r A true = N.pinnedValue r B true := by
  classical
  obtain ⟨σ, hσ⟩ := exists_permuteSlice_eq A B
  unfold Net.pinnedValue
  congr 1
  apply Fintype.sum_equiv (statePerm σ)
  intro S
  have he : (permuteState σ S) r = B ↔ S r = A := by
    rw [← hσ]
    exact (slicePerm σ).injective.eq_iff
  simp only [statePerm, Equiv.coe_fn_mk, he, weight_ordinary_permute]

theorem Net.pinnedValue_reduce_le_insert [Fintype V]
    (N : Net (M + 2) (fun v => p v + 1)) (hp : ∀ v, p v ≤ M)
    (r : V) (A : Slice M (p r)) :
    (N.reduce hp).pinnedValue r A true ≤ N.pinnedValue r (insertSlice A) true := by
  classical
  apply mul_le_mul_of_nonneg_left _ N.scalar_nonneg
  apply sum_le_of_injection insertState insertState_injective
  · intro S
    split_ifs
    · exact weight_nonneg _ _ _
    · exact le_refl _
  · intro S
    by_cases hS : S r = A
    · have hI : insertState S r = insertSlice A := congrArg insertSlice hS
      simp only [hS, hI, if_true]
      exact weight_reduce_insertion N.edges hp S
    · simp only [hS, if_false]
      split_ifs
      · exact weight_nonneg _ _ _
      · exact le_refl _

/-- W2 for arbitrary prescribed root sets, on the ordinary companions only. -/
theorem Net.pinnedValue_reduce_le [Fintype V]
    (N : Net (M + 2) (fun v => p v + 1)) (hp : ∀ v, p v ≤ M)
    (r : V) (A : Slice M (p r)) (B : Slice (M + 2) (p r + 1)) :
    (N.reduce hp).pinnedValue r A true ≤ N.pinnedValue r B true := by
  rw [← N.pinnedValue_ordinary_constant r (insertSlice A) B]
  exact N.pinnedValue_reduce_le_insert hp r A

end
end CoefficientwiseRigidity.Network
