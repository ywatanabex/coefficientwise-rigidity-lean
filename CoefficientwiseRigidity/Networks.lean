import CoefficientwiseRigidity.GainKernels

/-!
Actual finite K4 network sums and local elimination operations.
An edge list retains multiplicities. Parallel edges are merged by K3;
they are never silently erased. `true` selects the ordinary companion.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V : Type*} {p : V → ℕ}

abbrev State (M : ℕ) (p : V → ℕ) := (v : V) → Slice M (p v)

noncomputable instance stateFintype [Fintype V] : Fintype (State M p) := by
  classical
  unfold State
  infer_instance

structure Edge (M : ℕ) (p : V → ℕ) where
  left : V
  right : V
  distinct : left ≠ right
  kernels : GainList M (p left) (p right)

def kernel (ordinary : Bool) {a b : ℕ} (L : GainList M a b)
    (A : Slice M a) (B : Slice M b) : ℚ :=
  if ordinary then listOrdinary L A B else listValue L A B

theorem kernel_nonneg (ordinary : Bool) {a b : ℕ} (L : GainList M a b)
    (A : Slice M a) (B : Slice M b) : 0 ≤ kernel ordinary L A B := by
  cases ordinary
  · exact listValue_nonneg L A B
  · exact listOrdinary_nonneg L A B

def Edge.eval (e : Edge M p) (ordinary : Bool) (A : State M p) : ℚ :=
  kernel ordinary e.kernels (A e.left) (A e.right)

def weight (E : List (Edge M p)) (ordinary : Bool) (A : State M p) : ℚ :=
  (E.map fun e => e.eval ordinary A).prod

@[simp] theorem weight_nil (ordinary : Bool) (A : State M p) : weight [] ordinary A = 1 := rfl
@[simp] theorem weight_cons (e : Edge M p) (E : List (Edge M p)) (ordinary : Bool) (A : State M p) :
    weight (e :: E) ordinary A = e.eval ordinary A * weight E ordinary A := rfl

theorem weight_nonneg (E : List (Edge M p)) (ordinary : Bool) (A : State M p) :
    0 ≤ weight E ordinary A := by
  induction E with
  | nil => exact zero_le_one
  | cons e E ih => exact mul_nonneg (kernel_nonneg ordinary e.kernels _ _) ih

structure Net (M : ℕ) (p : V → ℕ) where
  scalar : ℚ
  scalar_nonneg : 0 ≤ scalar
  edges : List (Edge M p)

def Net.value [Fintype V] (N : Net M p) (ordinary : Bool) : ℚ := by
  classical
  exact N.scalar * ∑ A : State M p, weight N.edges ordinary A

theorem Net.value_nonneg [Fintype V] (N : Net M p) (ordinary : Bool) : 0 ≤ N.value ordinary := by
  classical
  exact mul_nonneg N.scalar_nonneg (Finset.sum_nonneg fun A _ => weight_nonneg N.edges ordinary A)

def Net.scale (N : Net M p) (c : ℚ) (hc : 0 ≤ c) : Net M p :=
  ⟨c * N.scalar, mul_nonneg hc N.scalar_nonneg, N.edges⟩

@[simp] theorem Net.scale_value [Fintype V] (N : Net M p) (c : ℚ) (hc : 0 ≤ c) (b : Bool) :
    (N.scale c hc).value b = c * N.value b := by
  simp only [Net.value, Net.scale, mul_assoc]

def Net.addEdge (N : Net M p) (u v : V) (huv : u ≠ v) (L : GainList M (p u) (p v)) : Net M p :=
  {N with edges := ⟨u,v,huv,L⟩ :: N.edges}

def extendRanks (m : ℕ) (p : V → ℕ) : Option V → ℕ := Option.elim' m p

def extendState (m : ℕ) (A : State M p) (C : Slice M m) : State M (extendRanks m p)
  | none => C
  | some v => A v

def liftEdge (m : ℕ) (e : Edge M p) : Edge M (extendRanks m p) :=
  ⟨some e.left, some e.right, fun h => e.distinct (Option.some.inj h), e.kernels⟩

def Net.lift (N : Net M p) (m : ℕ) : Net M (extendRanks m p) :=
  ⟨N.scalar, N.scalar_nonneg, N.edges.map (liftEdge m)⟩

@[simp] theorem weight_lift (E : List (Edge M p)) (m : ℕ) (b : Bool) (A : State M p) (C : Slice M m) :
    weight (E.map (liftEdge m)) b (extendState m A C) = weight E b A := by
  induction E with
  | nil => rfl
  | cons e E ih => simpa [weight, Edge.eval, liftEdge, extendState] using congrArg (e.eval b A * ·) ih

theorem sum_extendState [Fintype V] (m : ℕ) (F : State M (extendRanks m p) → ℚ) :
    (∑ A, F A) = ∑ A : State M p, ∑ C : Slice M m, F (extendState m A C) := by
  classical
  calc
    (∑ A, F A) = ∑ CA : Slice M m × State M p, F (extendState m CA.2 CA.1) :=
      Fintype.sum_equiv Equiv.piOptionEquivProd _ _ (fun A => by
        congr 1
        funext v
        cases v <;> rfl)
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem Net.isolated_value [Fintype V] (N : Net M p) (m : ℕ) (b : Bool) :
    (N.lift m).value b = (M.choose m : ℚ) * N.value b := by
  classical
  unfold Net.value
  rw [sum_extendState]
  simp only [Net.lift, weight_lift, Finset.sum_const, Finset.card_univ, slice_card, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem kernel_rowMass {a b : ℕ} (ha : a ≤ M) (L : GainList M a b) (A : Slice M a) (o : Bool) :
    (∑ B : Slice M b, kernel o L A B) = rowMass ha L := by
  cases o
  · exact list_value_rowMass ha L A
  · exact list_ordinary_rowMass ha L A

def Net.attachLeaf (N : Net M p) (m : ℕ) (u : V) (L : GainList M (p u) m) :
    Net M (extendRanks m p) :=
  (N.lift m).addEdge (some u) none (by simp) L

theorem Net.leaf_value [Fintype V] (N : Net M p) (m : ℕ) (u : V)
    (hu : p u ≤ M) (L : GainList M (p u) m) (b : Bool) :
    (N.attachLeaf m u L).value b = rowMass hu L * N.value b := by
  classical
  unfold Net.value
  rw [sum_extendState]
  simp only [Net.attachLeaf, Net.addEdge, Net.lift, weight_cons, weight_lift, Edge.eval, extendState]
  simp_rw [← Finset.sum_mul, kernel_rowMass hu]
  rw [← Finset.mul_sum]
  ring

theorem kernel_serial {a b c : ℕ} (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M)
    (L : GainList M a b) (K : GainList M b c) (A : Slice M a) (B : Slice M c) (o : Bool) :
    kernel o (serialLists ha hb hc L K) A B =
      ∑ C : Slice M b, kernel o L A C * kernel o K C B := by
  cases o
  · exact serialLists_value ha hb hc L K A B
  · exact serialLists_ordinary ha hb hc L K A B

def Net.attachSeries (N : Net M p) (m : ℕ) (u v : V)
    (L : GainList M (p u) m) (K : GainList M m (p v)) : Net M (extendRanks m p) :=
  ((N.lift m).addEdge none (some v) (by simp) K).addEdge (some u) none (by simp) L

theorem Net.series_value [Fintype V] (N : Net M p) (m : ℕ) (u v : V) (huv : u ≠ v)
    (hu : p u ≤ M) (hm : m ≤ M) (hv : p v ≤ M)
    (L : GainList M (p u) m) (K : GainList M m (p v)) (b : Bool) :
    (N.attachSeries m u v L K).value b =
      (N.addEdge u v huv (serialLists hu hm hv L K)).value b := by
  classical
  unfold Net.value
  rw [sum_extendState]
  simp only [Net.attachSeries, Net.addEdge, Net.lift, weight_cons, weight_lift, Edge.eval, extendState]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← kernel_serial hu hm hv]

theorem Net.parallel_bound [Fintype V] (N : Net M p) (u v : V) (huv : u ≠ v)
    (L K : GainList M (p u) (p v)) :
    ((N.addEdge u v huv K).addEdge u v huv L).value false ≤
      (N.addEdge u v huv (parallelLists L K)).value false := by
  classical
  apply mul_le_mul_of_nonneg_left _ N.scalar_nonneg
  apply Finset.sum_le_sum
  intro A _
  simp only [Net.addEdge, weight_cons, Edge.eval, kernel, Bool.false_eq_true, if_false]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (parallelLists_bound L K (A u) (A v)) (weight_nonneg N.edges false A)

theorem Net.parallel_ordinary [Fintype V] (N : Net M p) (u v : V) (huv : u ≠ v)
    (L K : GainList M (p u) (p v)) :
    ((N.addEdge u v huv K).addEdge u v huv L).value true =
      (N.addEdge u v huv (parallelLists L K)).value true := by
  classical
  unfold Net.value
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  simp [Net.addEdge, Edge.eval, kernel, parallelLists_ordinary, mul_assoc]

/-- At termination there are no vertices or edges; both values equal the scalar. -/
theorem Net.empty_value [Fintype V] [IsEmpty V] (N : Net M p) (b : Bool) : N.value b = N.scalar := by
  classical
  have he : N.edges = [] := by
    cases h : N.edges with
    | nil => rfl
    | cons e E => exact isEmptyElim e.left
  simp [Net.value, he, State]

end
end CoefficientwiseRigidity.Network
