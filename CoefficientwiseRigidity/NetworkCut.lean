import CoefficientwiseRigidity.NetworkBridge
import CoefficientwiseRigidity.NetworkJoin

/-!
Construct the two actual network pieces on a separating vertex cut.
Each piece has scalar one; the original scalar is retained outside the product.
The state bijection and edge-list identities prove the exact counting bridge.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
open scoped Classical
noncomputable section
variable {M : ℕ} {V : Type*} {p : V → ℕ}

def splitState (S : Set V) (A : State M (fun v : S => p v))
    (B : State M (fun v : (Sᶜ : Set V) => p v)) : State M p := by
  classical
  exact fun v => if h : v ∈ S then A ⟨v,h⟩ else B ⟨v,h⟩

def cutStateEquiv (S : Set V) : State M p ≃
    State M (fun v : S => p v) × State M (fun v : (Sᶜ : Set V) => p v) where
  toFun A := ⟨fun v => A v, fun v => A v⟩
  invFun A := splitState S A.1 A.2
  left_inv A := by
    classical
    funext v
    simp only [splitState]
    split_ifs <;> rfl
  right_inv A := by
    classical
    apply Prod.ext
    · funext v
      simp [splitState, v.property]
    · funext v
      have hv : v.val ∉ S := v.property
      simp [splitState, hv]

def Edge.onSet (e : Edge M p) (S : Set V) (h : e.left ∈ S ∧ e.right ∈ S) :
    Edge M (fun v : S => p v) :=
  ⟨⟨e.left,h.1⟩, ⟨e.right,h.2⟩, fun h => e.distinct (congrArg Subtype.val h), e.kernels⟩

def edgesOnSet (E : List (Edge M p)) (S : Set V) : List (Edge M (fun v : S => p v)) := by
  classical
  exact E.filterMap fun e => if h : e.left ∈ S ∧ e.right ∈ S then some (e.onSet S h) else none

def Net.onSet (N : Net M p) (S : Set V) : Net M (fun v : S => p v) :=
  ⟨1, zero_le_one, edgesOnSet N.edges S⟩

theorem weight_cut (E : List (Edge M p)) (S : Set V)
    (hS : ∀ e ∈ E, e.left ∈ S ↔ e.right ∈ S) (b : Bool)
    (A : State M (fun v : S => p v)) (B : State M (fun v : (Sᶜ : Set V) => p v)) :
    weight E b (splitState S A B) = weight (edgesOnSet E S) b A * weight (edgesOnSet E Sᶜ) b B := by
  classical
  induction E with
  | nil => simp [edgesOnSet]
  | cons e E ih =>
    have hE := ih (fun f hf => hS f (List.mem_cons_of_mem e hf))
    have he := hS e (List.mem_cons_self _ _)
    rw [weight_cons, hE]
    by_cases hl : e.left ∈ S
    · have hr := he.mp hl
      simp [edgesOnSet, List.filterMap_cons, hl, hr, weight_cons, Edge.eval, Edge.onSet,
        splitState, mul_assoc]
    · have hr : e.right ∉ S := fun h => hl (he.mpr h)
      simp [edgesOnSet, List.filterMap_cons, hl, hr, weight_cons, Edge.eval, Edge.onSet,
        splitState]
      ring

theorem sum_splitState [Fintype V] (S : Set V) (F : State M p → ℚ) :
    ∑ A, F A = ∑ A : State M (fun v : S => p v),
      ∑ B : State M (fun v : (Sᶜ : Set V) => p v), F (splitState S A B) := by
  classical
  calc
    _ = ∑ A : State M (fun v : S => p v) × State M (fun v : (Sᶜ : Set V) => p v),
        F (splitState S A.1 A.2) :=
      Fintype.sum_equiv (cutStateEquiv S) _ _ (fun A => congrArg F
        ((cutStateEquiv S).left_inv A).symm)
    _ = _ := Fintype.sum_prod_type _

theorem Net.onSet_flat {N : Net M p} (hN : N.Flat) (S : Set V) : (N.onSet S).Flat := by
  classical
  obtain ⟨γ, hγ⟩ := hN
  refine ⟨fun v => γ v, ?_⟩
  intro e he f hf i
  obtain ⟨e', he', h⟩ := List.mem_filterMap.mp he
  split_ifs at h with hs
  · cases Option.some.inj h
    exact hγ e' he' f hf i

theorem Net.onSet_reduce (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (S : Set V) :
    (N.reduce hp).onSet S = (N.onSet S).reduce (fun v => hp v) := by
  classical
  unfold Net.onSet Net.reduce
  congr 1
  unfold edgesOnSet
  rw [List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro e _
  by_cases hs : e.left ∈ S ∧ e.right ∈ S
  · simp [Edge.reduce, hs, Edge.onSet, reduceList]
  · simp [Edge.reduce, hs]

theorem Net.reduce_addSingle (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (u v : V) (huv : u ≠ v)
    (e : GainEntry (M + 2) (p u + 1) (p v + 1)) :
    (N.addEdge u v huv [e]).reduce hp =
      (N.reduce hp).addEdge u v huv [e.reduce (hp u) (hp v)] := rfl

/-- The actual background sum is the product on the two constructed vertex types. -/
theorem Net.value_cut [Fintype V] (N : Net M p) (S : Set V)
    (hS : ∀ e ∈ N.edges, e.left ∈ S ↔ e.right ∈ S) (b : Bool) :
    N.value b = N.scalar * (N.onSet S).value b * (N.onSet Sᶜ).value b := by
  classical
  simp only [Net.value, Net.onSet, one_mul]
  rw [sum_splitState S]
  simp_rw [weight_cut N.edges S hS b]
  rw [← Finset.sum_mul_sum]
  ring

/-- Exact bridge to the previously proved concrete two-component terminal theorem. -/
theorem Net.parallel_value_cut [Fintype V] (N : Net M p) (S : Set V)
    (hS : ∀ e ∈ N.edges, e.left ∈ S ↔ e.right ∈ S)
    (u v : V) (huv : u ≠ v) (hu : u ∈ S) (hv : v ∉ S)
    (e f : GainEntry M (p u) (p v)) (b : Bool) :
    ((N.addEdge u v huv [f]).addEdge u v huv [e]).value b = N.scalar *
      ((N.onSet S).joinTwo (N.onSet Sᶜ) ⟨u,hu⟩ ⟨v,hv⟩ e f).value b := by
  classical
  unfold Net.value
  rw [sum_splitState S, sum_sumState]
  simp only [Net.addEdge, weight_cons, Net.joinTwo, Net.disjointUnion, Net.onSet,
    one_mul, mul_one, Edge.eval, weight_disjointUnion, sumState]
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  rw [weight_cut N.edges S hS b A B]
  have hw := weight_disjointUnion (N.onSet S) (N.onSet Sᶜ) b A B
  simp only [Net.disjointUnion, Net.onSet] at hw
  rw [hw]
  simp [splitState, hu, hv]

end
end CoefficientwiseRigidity.Network
