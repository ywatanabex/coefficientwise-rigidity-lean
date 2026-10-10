import CoefficientwiseRigidity.ParallelRigidity
import CoefficientwiseRigidity.NetworkTreewidth

/-!
The other parallel case of W3: an induction bound on the nonflat F branch
pays the original reserve. The G branch is controlled by the already proved
unconditional treewidth-two comparison, even when it is zero or constant.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V : Type} [Fintype V] {p : V → ℕ}

theorem Net.addEdge_append_value (N : Net M p) (u v : V) (huv : u ≠ v)
    (L K : GainList M (p u) (p v)) (b : Bool) :
    (N.addEdge u v huv (L ++ K)).value b =
      (N.addEdge u v huv L).value b + (N.addEdge u v huv K).value b := by
  classical
  cases b <;> simp [Net.value, Net.addEdge, weight_cons, Edge.eval, kernel,
    listOrdinary_append, listValue_append, add_mul, Finset.sum_add_distrib, mul_add]

theorem Net.parallel_split_deficit (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v)) :
    ((N.addEdge u v huv [e.splitLeft f]).value true - (N.addEdge u v huv [e.splitLeft f]).value false) +
      ((N.addEdge u v huv [e.splitRight f]).value true - (N.addEdge u v huv [e.splitRight f]).value false) ≤
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).value true -
        ((N.addEdge u v huv [f]).addEdge u v huv [e]).value false := by
  have hg := N.parallel_bound u v huv [e] [f]
  have ho := N.parallel_ordinary u v huv [e] [f]
  have he (b : Bool) : (N.addEdge u v huv (parallelLists [e] [f])).value b =
      (N.addEdge u v huv [e.splitLeft f]).value b + (N.addEdge u v huv [e.splitRight f]).value b := by
    simpa [parallelLists] using N.addEdge_append_value u v huv [e.splitLeft f] [e.splitRight f] b
  rw [he false] at hg
  rw [he true] at ho
  linarith

/-- The split comparison retains the actual reduced parallel network. -/
theorem Net.parallel_reduce_le_splitLeft (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (u v : V) (huv : u ≠ v)
    (e f : GainEntry (M + 2) (p u + 1) (p v + 1)) :
    (((N.addEdge u v huv [f]).addEdge u v huv [e]).reduce hp).value true ≤
      ((N.addEdge u v huv [e.splitLeft f]).reduce hp).value true := by
  classical
  rw [Net.reduce_addSingle, Net.reduce_addSingle, Net.reduce_addSingle]
  apply mul_le_mul_of_nonneg_left _ N.scalar_nonneg
  apply Finset.sum_le_sum
  intro A _
  simp only [Net.addEdge, weight_cons, Edge.eval, kernel, if_true,
    listOrdinary_cons, listOrdinary_nil, add_zero]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (e.splitLeft_reduce_reserve f (hp u) (hp v) (A u) (A v))
    (weight_nonneg _ true A)

/-- Inductive propagation on a specified F branch; its deficit premise is the induction hypothesis. -/
theorem Net.parallel_bound_of_splitLeft (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (u v : V) (huv : u ≠ v)
    (e f : GainEntry (M + 2) (p u + 1) (p v + 1)) (c : ℚ) (hc : 0 ≤ c)
    (hF : c * ((N.addEdge u v huv [e.splitLeft f]).reduce hp).value true ≤
      (N.addEdge u v huv [e.splitLeft f]).value true - (N.addEdge u v huv [e.splitLeft f]).value false)
    (hG : (N.addEdge u v huv [e.splitRight f]).value false ≤
      (N.addEdge u v huv [e.splitRight f]).value true) :
    c * (((N.addEdge u v huv [f]).addEdge u v huv [e]).reduce hp).value true ≤
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).value true -
        ((N.addEdge u v huv [f]).addEdge u v huv [e]).value false := by
  have hR := mul_le_mul_of_nonneg_left (N.parallel_reduce_le_splitLeft hp u v huv e f) hc
  have hD := N.parallel_split_deficit u v huv e f
  linarith

/-- K4 supplies the entire G-branch premise from the original graph-class definition. -/
theorem Net.parallel_bound_of_treewidth_splitLeft (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (u v : V) (huv : u ≠ v)
    (e f : GainEntry (M + 2) (p u + 1) (p v + 1)) (c : ℚ) (hc : 0 ≤ c)
    (hwidth : TreewidthAtMostTwo (N.addEdge u v huv [e]).graph)
    (hF : c * ((N.addEdge u v huv [e.splitLeft f]).reduce hp).value true ≤
      (N.addEdge u v huv [e.splitLeft f]).value true - (N.addEdge u v huv [e.splitLeft f]).value false) :
    c * (((N.addEdge u v huv [f]).addEdge u v huv [e]).reduce hp).value true ≤
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).value true -
        ((N.addEdge u v huv [f]).addEdge u v huv [e]).value false := by
  classical
  apply N.parallel_bound_of_splitLeft hp u v huv e f c hc hF
  apply Net.comparison_of_treewidth
  · intro w
    have := hp w
    omega
  · rwa [Net.graph_addEdge] at hwidth ⊢

end
end CoefficientwiseRigidity.Network
