import CoefficientwiseRigidity.TreeBags

/-!
Low-degree vertices and smoothing directly from width-two tree bags.
The original graph-class definition is unchanged.
-/
namespace CoefficientwiseRigidity.Structure
open SimpleGraph Finset
noncomputable section
variable {I V : Type} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem Bags.only_at_leaf (D : Bags G I) (l t : I)
    (hl : ∀ x, D.tree.Adj l x → x = t) {v : V}
    (hvl : v ∈ D.bag l) (hvt : v ∉ D.bag t) {i : I} (hvi : v ∈ D.bag i) : i = l := by
  rcases reachable_first (D.running v ⟨l,hvl⟩ ⟨i,hvi⟩) with he | ⟨j,hj⟩
  · exact (congrArg Subtype.val he).symm
  · have he : j.val = t := hl j.val hj
    exact False.elim (hvt (he ▸ j.property))

private theorem bag_neighborhood_aux [Nonempty V] (n : ℕ) :
    ∀ (I : Type) [Fintype I], Fintype.card I = n → ∀ D : Bags G I,
      ∃ v i, v ∈ D.bag i ∧ ∀ w, G.Adj v w → w ∈ D.bag i := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I _ hI D
    obtain ⟨l, hl⟩ := tree_leaf D.tree D.isTree
    by_cases hn : ∃ t, D.tree.Adj l t
    · obtain ⟨t, hlt⟩ := hn
      have ht : t ≠ l := hlt.ne.symm
      have hleaf : ∀ x, D.tree.Adj l x → x = t := fun x hx => hl x t hx hlt
      by_cases hsub : D.bag l ⊆ D.bag t
      · have hcard : Fintype.card {x : I // x ≠ l} < n := by
          rw [← hI]
          exact Fintype.card_subtype_lt (by simp : ¬ (l ≠ l))
        obtain ⟨v, i, hvi, hni⟩ := ih _ hcard {x : I // x ≠ l} rfl (D.prune l t ht hleaf hsub)
        exact ⟨v, i.val, hvi, hni⟩
      · obtain ⟨v, hvl, hvt⟩ := Finset.not_subset.mp hsub
        refine ⟨v,l,hvl,?_⟩
        intro w hvw
        obtain ⟨i,hvi,hwi⟩ := D.edge v w hvw
        simpa only [D.only_at_leaf l t hleaf hvl hvt hvi] using hwi
    · have hall : ∀ i : I, i = l := by
        intro i
        rcases reachable_first (D.isTree.isConnected l i) with he | he
        · exact he.symm
        · exact False.elim (hn he)
      obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨i,hi⟩ := D.cover v
      refine ⟨v,l,by simpa only [hall i] using hi,?_⟩
      intro w hvw
      obtain ⟨j,_,hw⟩ := D.edge v w hvw
      simpa only [hall j] using hw

/-- Some vertex and all its neighbours lie in one bag of size at most three. -/
theorem Bags.exists_bag_neighborhood [Fintype I] [Nonempty V] (D : Bags G I) :
    ∃ v i, v ∈ D.bag i ∧ ∀ w, G.Adj v w → w ∈ D.bag i :=
  bag_neighborhood_aux (Fintype.card I) I rfl D

/-- Delete v and join its distinct neighbours. No loop or multiedge is introduced. -/
def smooth (G : SimpleGraph V) (v : V) : SimpleGraph {w : V // w ≠ v} where
  Adj u w := u ≠ w ∧ (G.Adj u.val w.val ∨ (G.Adj u.val v ∧ G.Adj v w.val))
  symm := by
    intro u w h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h.2.symm,h.1.symm⟩
  loopless := fun _ h => h.1 rfl

/-- Removing the vertex from every bag covers the fill edge in the same bag. -/
def Bags.smooth (D : Bags G I) (v : V) (i : I)
    (hneigh : ∀ w, G.Adj v w → w ∈ D.bag i) : Bags (smooth G v) I where
  tree := D.tree
  isTree := D.isTree
  bag j := (D.bag j).subtype (fun w => w ≠ v)
  small j := (by rw [Finset.card_subtype]; exact (Finset.card_filter_le _ _).trans (D.small j))
  cover w := by
    obtain ⟨j,hj⟩ := D.cover w.val
    exact ⟨j, Finset.mem_subtype.mpr hj⟩
  edge u w huw := by
    rcases huw.2 with h | h
    · obtain ⟨j,hj,hk⟩ := D.edge u.val w.val h
      exact ⟨j,Finset.mem_subtype.mpr hj,Finset.mem_subtype.mpr hk⟩
    · exact ⟨i, Finset.mem_subtype.mpr (hneigh u.val h.1.symm), Finset.mem_subtype.mpr (hneigh w.val h.2)⟩
  running w := by
    have he : {j | w ∈ (D.bag j).subtype (fun x => x ≠ v)} = {j | w.val ∈ D.bag j} := by
      ext j
      exact Finset.mem_subtype
    rw [he]
    exact D.running w.val

theorem Bags.neighbors_card_le_two [Fintype V] [DecidableRel G.Adj] (D : Bags G I)
    (v : V) (i : I) (hv : v ∈ D.bag i) (hneigh : ∀ w, G.Adj v w → w ∈ D.bag i) :
    G.degree v ≤ 2 := by
  have hsub : G.neighborFinset v ⊆ (D.bag i).erase v := by
    intro w hw
    have h := (G.mem_neighborFinset v w).mp hw
    exact Finset.mem_erase.mpr ⟨h.ne.symm, hneigh w h⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at hc
  have hb := D.small i
  change G.degree v ≤ 2
  change G.degree v ≤ (D.bag i).card - 1 at hc
  omega

/-- A width-two bag decomposition supplies a low-degree step and a decomposition
of the smoothed graph. This is derived from bags, not postulated as treewidth. -/
theorem treewidth_smoothing_step [Fintype V] [Nonempty V] (h : TreewidthAtMostTwo G) :
    ∃ (v : V) (S : Finset V), v ∉ S ∧ S.card ≤ 2 ∧
      (∀ w, G.Adj v w ↔ w ∈ S) ∧ TreewidthAtMostTwo (smooth G v) := by
  classical
  obtain ⟨n, ⟨D⟩⟩ := bags_of_treewidth h
  obtain ⟨v, i, hv, hn⟩ := D.exists_bag_neighborhood
  refine ⟨v, G.neighborFinset v, by simp, D.neighbors_card_le_two v i hv hn, ?_, ?_⟩
  · intro w
    exact (G.mem_neighborFinset v w).symm
  · exact (D.smooth v i hn).treewidth

/-- An actual finite order on successively smoothed graphs. -/
inductive SmoothingOrder : {V : Type} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop where
  | empty {V : Type} [Fintype V] [DecidableEq V] [IsEmpty V] (G : SimpleGraph V) : SmoothingOrder G
  | step {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
      (S : Finset V) (hv : v ∉ S) (hs : S.card ≤ 2) (hn : ∀ w, G.Adj v w ↔ w ∈ S)
      (rest : SmoothingOrder (smooth G v)) : SmoothingOrder G

private theorem smoothing_order_aux (n : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n → TreewidthAtMostTwo G → SmoothingOrder G := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hcard hG
    cases isEmpty_or_nonempty V with
    | inl h =>
      haveI := h
      exact SmoothingOrder.empty G
    | inr h =>
      haveI := h
      obtain ⟨v,S,hv,hs,hn,ht⟩ := treewidth_smoothing_step hG
      refine SmoothingOrder.step G v S hv hs hn ?_
      have hlt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (by simp : ¬ (v ≠ v))
      exact ih _ hlt _ (smooth G v) rfl ht

/-- Full structural elimination order from the unchanged tree-bag definition. -/
theorem treewidth_smoothing_order [Fintype V] (h : TreewidthAtMostTwo G) : SmoothingOrder G :=
  smoothing_order_aux (Fintype.card V) V G rfl h

end
end CoefficientwiseRigidity.Structure
