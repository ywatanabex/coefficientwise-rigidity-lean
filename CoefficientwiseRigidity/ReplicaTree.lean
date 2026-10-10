import CoefficientwiseRigidity.TreeBags
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! A central vertex joined to the root of each of any family of trees.
Acyclicity is proved from actual bridge cuts, not from a tree oracle. -/
namespace CoefficientwiseRigidity.Replica
open scoped Classical
noncomputable section
variable {I J : Type} [DecidableEq I]

def starTree (T : SimpleGraph J) (r : J) (I : Type) : SimpleGraph (Option (I × J)) where
  Adj x y := match x,y with
    | none,none => False
    | none,some y => y.2 = r
    | some x,none => x.2 = r
    | some x,some y => x.1 = y.1 ∧ T.Adj x.2 y.2
  symm := by
    intro x y h
    cases x <;> cases y <;> simp_all [eq_comm,T.adj_comm]
  loopless := by
    intro x
    cases x <;> simp [T.loopless]

def treeHom (T : SimpleGraph J) (r : J) (i : I) : T →g starTree T r I :=
  ⟨fun t => some (i,t),fun h => ⟨rfl,h⟩⟩

def collapse (r : J) (i : I) : Option (I × J) → J
  | none => r
  | some jt => if jt.1 = i then jt.2 else r

private theorem collapse_deleted (T : SimpleGraph J) (r : J) (i : I) (u v : J)
    {x y : Option (I × J)}
    (h : (starTree T r I \ SimpleGraph.edge (some (i,u)) (some (i,v))).Adj x y) :
    collapse r i x = collapse r i y ∨
      (T \ SimpleGraph.edge u v).Adj (collapse r i x) (collapse r i y) := by
  cases x with
  | none =>
    cases y with
    | none => exact False.elim h.1
    | some jt =>
      have hj : jt.2 = r := h.1
      left
      simp [collapse,hj]
  | some is =>
    cases y with
    | none =>
      have hi : is.2 = r := h.1
      left
      simp [collapse,hi]
    | some jt =>
      rcases is with ⟨j,s⟩
      rcases jt with ⟨k,t⟩
      have hjk : j = k := h.1.1
      subst k
      by_cases hj : j = i
      · subst j
        right
        simp only [collapse,if_pos rfl]
        change (T \ SimpleGraph.edge u v).Adj s t
        refine ⟨h.1.2,?_⟩
        intro he
        apply h.2
        simpa [SimpleGraph.edge_adj] using he
      · left
        simp [collapse,hj]

private theorem internal_bridge (T : SimpleGraph J) (r : J) (hT : T.IsAcyclic)
    (i : I) {u v : J} (huv : T.Adj u v) :
    (starTree T r I).IsBridge (Sym2.mk (some (i,u),some (i,v))) := by
  rw [SimpleGraph.isBridge_iff]
  refine ⟨⟨rfl,huv⟩,?_⟩
  intro h
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT) huv
  have hn := (SimpleGraph.isBridge_iff.mp hb).2
  apply hn
  have hr := Structure.reachable_map_edges (G := starTree T r I \ SimpleGraph.edge (some (i,u)) (some (i,v)))
    (H := T \ SimpleGraph.edge u v) (collapse r i)
    (fun x y hxy => by
      rcases collapse_deleted T r i u v hxy with he | he
      · rw [he]
      · exact he.reachable) h
  simpa [collapse] using hr

def mark (i : I) : Option (I × J) → Bool
  | none => false
  | some jt => if jt.1 = i then true else false

private theorem mark_deleted (T : SimpleGraph J) (r : J) (i : I)
    {x y : Option (I × J)}
    (h : (starTree T r I \ SimpleGraph.edge none (some (i,r))).Adj x y) :
    mark i x = mark i y := by
  cases x with
  | none =>
    cases y with
    | none => exact False.elim h.1
    | some jt =>
      rcases jt with ⟨j,t⟩
      have ht : t = r := h.1
      subst t
      have hj : j ≠ i := by
        intro he
        subst j
        apply h.2
        simp [SimpleGraph.edge_adj]
      simp [mark,hj]
  | some is =>
    cases y with
    | none =>
      rcases is with ⟨j,t⟩
      have ht : t = r := h.1
      subst t
      have hj : j ≠ i := by
        intro he
        subst j
        apply h.2
        simp [SimpleGraph.edge_adj]
      simp [mark,hj]
    | some jt =>
      have hij : is.1 = jt.1 := h.1.1
      simp [mark,hij]

theorem eq_of_reachable {K : Type} {H : SimpleGraph K} {A : Type} (f : K → A)
    (hf : ∀ x y, H.Adj x y → f x = f y) {x y : K} (h : H.Reachable x y) : f x = f y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hf _ _ h).trans ih

private theorem spoke_bridge (T : SimpleGraph J) (r : J) (i : I) :
    (starTree T r I).IsBridge (Sym2.mk (none,some (i,r))) := by
  rw [SimpleGraph.isBridge_iff]
  refine ⟨rfl,?_⟩
  intro h
  have he := eq_of_reachable (H := starTree T r I \ SimpleGraph.edge none (some (i,r)))
    (mark i) (fun _ _ => mark_deleted T r i) h
  simp [mark] at he

theorem starTree_isTree (T : SimpleGraph J) (r : J) (hT : T.IsTree) :
    (starTree T r I).IsTree := by
  refine ⟨?_,SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr ?_⟩
  · apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨none,?_⟩
    intro x
    cases x with
    | none => exact .rfl
    | some it =>
      have hr : (starTree T r I).Adj none (some (it.1,r)) := rfl
      exact hr.reachable.trans ((hT.isConnected r it.2).map (treeHom T r it.1))
  · intro x y h
    cases x with
    | none =>
      cases y with
      | none => exact False.elim h
      | some it =>
        rcases it with ⟨i,t⟩
        have ht : t = r := h
        subst t
        exact spoke_bridge T r i
    | some is =>
      cases y with
      | none =>
        rcases is with ⟨i,s⟩
        have hs : s = r := h
        subst s
        rw [Sym2.eq_swap]
        exact spoke_bridge T r i
      | some jt =>
        rcases is with ⟨i,s⟩
        rcases jt with ⟨j,t⟩
        have hij : i = j := h.1
        subst j
        exact internal_bridge T r hT.IsAcyclic i h.2

end
end CoefficientwiseRigidity.Replica
