import CoefficientwiseRigidity.Targets
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
Tree-bag structure for LF-02. The bag definition is the one in Targets;
no elimination-order or graph-comparison assumption is added to it.
-/
namespace CoefficientwiseRigidity.Structure
open SimpleGraph Finset
noncomputable section
variable {I J V : Type} [DecidableEq V]

/-- Walks may be sent to walks with some edges collapsed to vertices. -/
theorem reachable_map_edges {G : SimpleGraph I} {H : SimpleGraph J} (f : I → J)
    (hf : ∀ u v, G.Adj u v → H.Reachable (f u) (f v)) {u v : I}
    (h : G.Reachable u v) : H.Reachable (f u) (f v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons h _ ih => exact (hf _ _ h).trans ih

theorem reachable_first {G : SimpleGraph I} {u v : I} (h : G.Reachable u v) :
    u = v ∨ ∃ w, G.Adj u w := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => exact Or.inl rfl
  | cons h _ => exact Or.inr ⟨_, h⟩

theorem acyclic_induce (T : SimpleGraph I) (hT : T.IsAcyclic) (P : Set I) :
    (T.induce P).IsAcyclic := by
  let f : T.induce P →g T := ⟨Subtype.val, fun h => h⟩
  intro v c hc
  exact hT (c.map f) (hc.map Subtype.val_injective)

/-- Every finite tree has a vertex with at most one neighbour. -/
theorem tree_leaf [Fintype I] (T : SimpleGraph I) (hT : T.IsTree) :
    ∃ l, ∀ u v, T.Adj l u → T.Adj l v → u = v := by
  classical
  have hd : ∃ l, T.degree l ≤ 1 := by
    by_contra hn
    push_neg at hn
    have hsum : ∑ _i : I, 2 ≤ ∑ i : I, T.degree i :=
      Finset.sum_le_sum fun i _ => Nat.succ_le_of_lt (hn i)
    rw [T.sum_degrees_eq_twice_card_edges] at hsum
    have hc := hT.card_edgeFinset
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
    omega
  obtain ⟨l, hl⟩ := hd
  refine ⟨l, ?_⟩
  intro u v hu hv
  exact Finset.card_le_one.mp hl u (by simpa using hu) v (by simpa using hv)

def foldLeaf [DecidableEq I] (l t : I) (ht : t ≠ l) (x : I) : {x : I // x ≠ l} :=
  if hx : x = l then ⟨t,ht⟩ else ⟨x,hx⟩

@[simp] theorem foldLeaf_fixed [DecidableEq I] (l t : I) (ht : t ≠ l) (x : {x : I // x ≠ l}) :
    foldLeaf l t ht x.val = x := by simp [foldLeaf, x.property]

theorem foldLeaf_adj [DecidableEq I] (T : SimpleGraph I) (l t : I) (ht : t ≠ l)
    (hl : ∀ x, T.Adj l x → x = t) {x y : I} (hxy : T.Adj x y) :
    foldLeaf l t ht x = foldLeaf l t ht y ∨
      (T.induce {x | x ≠ l}).Adj (foldLeaf l t ht x) (foldLeaf l t ht y) := by
  by_cases hx : x = l
  · subst x
    have hy := hl y hxy
    subst y
    simp [foldLeaf, ht]
  · by_cases hy : y = l
    · subst y
      have he := hl x hxy.symm
      subst x
      simp [foldLeaf, ht]
    · exact Or.inr (by simpa [foldLeaf, hx, hy] using hxy)

theorem foldLeaf_mem [DecidableEq I] (l t : I) (ht : t ≠ l) (P : I → Prop)
    (hP : P l → P t) {x : I} (hx : P x) : P (foldLeaf l t ht x).val := by
  by_cases h : x = l
  · subst x; simpa [foldLeaf] using hP hx
  · simpa [foldLeaf, h] using hx

/-- Pruning a redundant leaf preserves connected occurrence sets. -/
theorem preconnected_prune [DecidableEq I] (T : SimpleGraph I) (l t : I) (ht : t ≠ l)
    (hl : ∀ x, T.Adj l x → x = t) (P : I → Prop) (hP : P l → P t)
    (hc : (T.induce {x | P x}).Preconnected) :
    ((T.induce {x | x ≠ l}).induce {x | P x.val}).Preconnected := by
  let f : {x : I // P x} → {x : {x : I // x ≠ l} // P x.val} :=
    fun x => ⟨foldLeaf l t ht x.val, foldLeaf_mem l t ht P hP x.property⟩
  intro x y
  let x' : {x : I // P x} := ⟨x.val.val,x.property⟩
  let y' : {x : I // P x} := ⟨y.val.val,y.property⟩
  have h := reachable_map_edges (H := (T.induce {x | x ≠ l}).induce {x | P x.val})
    f (fun u v huv => ?_) (hc x' y')
  · simpa [f, x', y'] using h
  · rcases foldLeaf_adj T l t ht hl huv with he | he
    · have hf : f u = f v := Subtype.ext he
      rw [hf]
    · exact SimpleGraph.Adj.reachable he

theorem tree_prune [DecidableEq I] (T : SimpleGraph I) (hT : T.IsTree) (l t : I)
    (ht : t ≠ l) (hl : ∀ x, T.Adj l x → x = t) :
    (T.induce {x | x ≠ l}).IsTree := by
  refine { isConnected := { preconnected := ?_, nonempty := ⟨⟨t,ht⟩⟩ }, IsAcyclic := acyclic_induce T hT.IsAcyclic _ }
  intro x y
  have h := reachable_map_edges (H := T.induce {x | x ≠ l})
    (foldLeaf l t ht) (fun u v huv => ?_) (hT.isConnected x.val y.val)
  · simpa using h
  · rcases foldLeaf_adj T l t ht hl huv with he | he
    · rw [he]
    · exact he.reachable

/-- Bags indexed by any finite type, for induction when a leaf is removed. -/
structure Bags (G : SimpleGraph V) (I : Type) where
  tree : SimpleGraph I
  isTree : tree.IsTree
  bag : I → Finset V
  small : ∀ i, (bag i).card ≤ 3
  cover : ∀ v, ∃ i, v ∈ bag i
  edge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  running : ∀ v, (tree.induce {i | v ∈ bag i}).Preconnected

def Bags.prune {G : SimpleGraph V} [DecidableEq I] (D : Bags G I) (l t : I)
    (ht : t ≠ l) (hl : ∀ x, D.tree.Adj l x → x = t) (hsub : D.bag l ⊆ D.bag t) :
    Bags G {x : I // x ≠ l} where
  tree := D.tree.induce {x | x ≠ l}
  isTree := tree_prune D.tree D.isTree l t ht hl
  bag x := D.bag x.val
  small x := D.small x.val
  cover v := by
    obtain ⟨i, hi⟩ := D.cover v
    by_cases h : i = l
    · subst i; exact ⟨⟨t,ht⟩, hsub hi⟩
    · exact ⟨⟨i,h⟩, hi⟩
  edge u v huv := by
    obtain ⟨i, hi, hj⟩ := D.edge u v huv
    by_cases h : i = l
    · subst i; exact ⟨⟨t,ht⟩, hsub hi, hsub hj⟩
    · exact ⟨⟨i,h⟩, hi, hj⟩
  running v := preconnected_prune D.tree l t ht hl (fun i => v ∈ D.bag i)
    (fun h => hsub h) (D.running v)

theorem isTree_of_iso {T : SimpleGraph I} {U : SimpleGraph J} (e : T ≃g U) (hU : U.IsTree) :
    T.IsTree := by
  refine ⟨e.connected_iff.mpr hU.isConnected, ?_⟩
  intro v c hc
  exact hU.IsAcyclic (c.map e.toHom) (hc.map e.injective)

/-- Index renaming, used to return to the original Fin n bag definition. -/
def Bags.reindex {G : SimpleGraph V} (D : Bags G I) (e : J ≃ I) : Bags G J where
  tree := D.tree.comap e.toEmbedding
  isTree := isTree_of_iso (SimpleGraph.Iso.comap e D.tree) D.isTree
  bag j := D.bag (e j)
  small j := D.small (e j)
  cover v := by
    obtain ⟨i, hi⟩ := D.cover v
    exact ⟨e.symm i, by simpa using hi⟩
  edge u v huv := by
    obtain ⟨i, hu, hv⟩ := D.edge u v huv
    exact ⟨e.symm i, by simpa using hu, by simpa using hv⟩
  running v := by
    let f : (D.tree.comap e.toEmbedding).induce {j | v ∈ D.bag (e j)} ≃g
        D.tree.induce {i | v ∈ D.bag i} := {
      toFun := fun j => ⟨e j.val, j.property⟩
      invFun := fun i => ⟨e.symm i.val, by
        change v ∈ D.bag (e (e.symm i.val))
        rw [e.apply_symm_apply]
        exact i.property⟩
      left_inv := by intro j; apply Subtype.ext; exact e.symm_apply_apply j.val
      right_inv := by intro i; apply Subtype.ext; exact e.apply_symm_apply i.val
      map_rel_iff' := by intros; rfl }
    exact f.preconnected_iff.mpr (D.running v)

omit [DecidableEq V] in
theorem Bags.treewidth [Fintype V] [Fintype I] {G : SimpleGraph V} (D : Bags G I) : TreewidthAtMostTwo G := by
  classical
  let E := D.reindex (Fintype.equivFin I).symm
  exact ⟨Fintype.card I, E.tree, E.bag, E.isTree, E.small, E.cover, E.edge, E.running⟩

omit [DecidableEq V] in
theorem bags_of_treewidth [Fintype V] {G : SimpleGraph V} (h : TreewidthAtMostTwo G) :
    ∃ n, Nonempty (Bags G (Fin n)) := by
  obtain ⟨n,T,bag,ht,hs,hv,he,hr⟩ := h
  exact ⟨n, ⟨⟨T,ht,bag,hs,hv,he,hr⟩⟩⟩

end
end CoefficientwiseRigidity.Structure
