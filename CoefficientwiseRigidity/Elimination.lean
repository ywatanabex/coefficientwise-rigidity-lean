import CoefficientwiseRigidity.NetworkRelabel

/-!
Soundness of a finite, concrete elimination derivation. Constructors contain
only the explicit K4 operations, never a comparison assumption. The general
tree-bag comparison is proved directly in NetworkTreewidth, without requiring
construction of this particular syntactic certificate.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section

variable {M : ℕ} {V : Type} [Fintype V] {p : V → ℕ}

omit [Fintype V] in
theorem weight_perm {E F : List (Edge M p)} (h : E.Perm F) (b : Bool) (A : State M p) :
    weight E b A = weight F b A := (h.map (fun e : Edge M p => e.eval b A)).prod_eq

theorem Net.reorder_value (N : Net M p) (E : List (Edge M p)) (h : N.edges.Perm E) (b : Bool) :
    ({N with edges := E} : Net M p).value b = N.value b := by
  classical
  unfold Net.value
  congr 1
  exact Finset.sum_congr rfl fun A _ => (weight_perm h b A).symm

def Edge.reverse (e : Edge M p) : Edge M p :=
  ⟨e.right, e.left, e.distinct.symm, reverseList e.kernels⟩

omit [Fintype V] in
theorem Edge.reverse_eval (e : Edge M p) (b : Bool) (A : State M p) :
    e.reverse.eval b A = e.eval b A := by
  cases b <;> simp [Edge.eval, Edge.reverse, kernel]

theorem Net.reverse_head_value (N : Net M p) (e : Edge M p) (b : Bool) :
    ({N with edges := e.reverse :: N.edges} : Net M p).value b =
      ({N with edges := e :: N.edges} : Net M p).value b := by
  classical
  simp only [Net.value, weight_cons, Edge.reverse_eval]

/-- A structural computation using only actual elimination and merge rules.
This is not the definition of treewidth and is not assumed in any A–C target. -/
inductive Eliminates (M : ℕ) : {V : Type} → [Fintype V] → {p : V → ℕ} → Net M p → Prop where
  | empty {V : Type} [Fintype V] [IsEmpty V] {p : V → ℕ} (N : Net M p) : Eliminates M N
  | isolated {V : Type} [Fintype V] {p : V → ℕ} (N : Net M p) (m : ℕ)
      (rest : Eliminates M (N.scale (M.choose m) (Nat.cast_nonneg _))) :
      Eliminates M (N.lift m)
  | leaf {V : Type} [Fintype V] {p : V → ℕ} (N : Net M p) (m : ℕ) (u : V)
      (hu : p u ≤ M) (L : GainList M (p u) m)
      (rest : Eliminates M (N.scale (rowMass hu L) (rowMass_nonneg hu L))) :
      Eliminates M (N.attachLeaf m u L)
  | series {V : Type} [Fintype V] {p : V → ℕ} (N : Net M p) (m : ℕ) (u v : V)
      (huv : u ≠ v) (hu : p u ≤ M) (hm : m ≤ M) (hv : p v ≤ M)
      (L : GainList M (p u) m) (K : GainList M m (p v))
      (rest : Eliminates M (N.addEdge u v huv (serialLists hu hm hv L K))) :
      Eliminates M (N.attachSeries m u v L K)
  | parallel {V : Type} [Fintype V] {p : V → ℕ} (N : Net M p) (u v : V) (huv : u ≠ v)
      (L K : GainList M (p u) (p v))
      (rest : Eliminates M (N.addEdge u v huv (parallelLists L K))) :
      Eliminates M ((N.addEdge u v huv K).addEdge u v huv L)
  | reorder {V : Type} [Fintype V] {p : V → ℕ} (N : Net M p) (E : List (Edge M p))
      (h : N.edges.Perm E) (rest : Eliminates M ({N with edges := E} : Net M p)) : Eliminates M N
  | rename {V W : Type} [Fintype V] [Fintype W] {p : V → ℕ} (N : Net M p) (e : V ≃ W)
      (rest : Eliminates M (N.rename e)) : Eliminates M N
  | reverse {V : Type} [Fintype V] {p : V → ℕ} (N : Net M p) (e : Edge M p)
      (rest : Eliminates M ({N with edges := e.reverse :: N.edges} : Net M p)) :
      Eliminates M ({N with edges := e :: N.edges} : Net M p)

/-- K4a along an arbitrary finite derivation: gained ≤ final scalar = ordinary.
No positivity of a denominator, nonzero row, or nonzero network is required. -/
theorem Eliminates.comparison {N : Net M p} (h : Eliminates M N) :
    N.value false ≤ N.value true := by
  induction h with
  | empty N => simp only [Net.empty_value, le_refl]
  | isolated N m rest ih =>
    simpa only [Net.isolated_value, Net.scale_value] using ih
  | leaf N m u hu L rest ih =>
    simpa only [Net.leaf_value N m u hu L, Net.scale_value] using ih
  | series N m u v huv hu hm hv L K rest ih =>
    simpa only [Net.series_value N m u v huv hu hm hv L K] using ih
  | parallel N u v huv L K rest ih =>
    exact (N.parallel_bound u v huv L K).trans (ih.trans_eq (N.parallel_ordinary u v huv L K).symm)
  | reorder N E h rest ih => simpa only [Net.reorder_value N E h] using ih
  | rename N e rest ih => simpa only [Net.rename_value] using ih
  | reverse N e rest ih => simpa only [Net.reverse_head_value] using ih

end
end CoefficientwiseRigidity.Network
