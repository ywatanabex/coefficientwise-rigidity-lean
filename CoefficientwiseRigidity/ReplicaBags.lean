import CoefficientwiseRigidity.ReplicaTree
import CoefficientwiseRigidity.BoundaryAmplification
import CoefficientwiseRigidity.CoefficientBoundary

/-! Actual width-two bags for every finite number of boundary-sharing copies. -/
namespace CoefficientwiseRigidity.Replica
open scoped Classical
noncomputable section
variable {V I J : Type} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {G : SimpleGraph V}

def copyBag (S : Finset V) (bag : J → Finset V) : Option (I × J) → Finset (Vertex S I)
  | none => Finset.univ.map ⟨Sum.inl,Sum.inl_injective⟩
  | some it => (bag it.2).map (embedding S it.1)

omit [Fintype V] [DecidableEq I] in
@[simp] theorem inl_mem_copyBag (S : Finset V) (bag : J → Finset V) (u : S)
    (i : I) (t : J) : Sum.inl u ∈ copyBag S bag (some (i,t)) ↔ u.val ∈ bag t := by
  constructor
  · rintro h
    obtain ⟨v,hv,he⟩ := Finset.mem_map.mp h
    have hh : v = u.val := by simpa [embedding] using congrArg (base S) he
    exact hh ▸ hv
  · intro h
    exact Finset.mem_map.mpr ⟨u.val,h,embed_mem S i u⟩

omit [Fintype V] [DecidableEq I] in
@[simp] theorem inr_mem_copyBag (S : Finset V) (bag : J → Finset V)
    (iv : I × {v : V // v ∉ S}) (j : I) (t : J) :
    Sum.inr iv ∈ copyBag S bag (some (j,t)) ↔ iv.1 = j ∧ iv.2.val ∈ bag t := by
  rcases iv with ⟨i,v⟩
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_map.mp h
    have hb : w = v.val := by simpa [embedding] using congrArg (base S) he
    subst w
    change embed S j v.val = Sum.inr (i,v) at he
    rw [embed_not_mem] at he
    exact ⟨(Prod.mk.inj (Sum.inr.inj he)).1.symm,hw⟩
  · rintro ⟨rfl,h⟩
    exact Finset.mem_map.mpr ⟨v.val,h,embed_not_mem S i v⟩

omit [Fintype V] [DecidableEq I] in
@[simp] theorem inl_mem_central (S : Finset V) (bag : J → Finset V) (u : S) :
    Sum.inl u ∈ copyBag (I := I) S bag none := by simp [copyBag]

omit [Fintype V] [DecidableEq I] in
@[simp] theorem inr_not_mem_central (S : Finset V) (bag : J → Finset V)
    (i : I) (u : {v : V // v ∉ S}) : Sum.inr (i,u) ∉ copyBag S bag none := by
  simp [copyBag]

def bags (D : Structure.Bags G J) (S : Finset V) (r : J)
    (hS : S ⊆ D.bag r) (hs : S.card ≤ 3) :
    Structure.Bags (graph G S I) (Option (I × J)) where
  tree := starTree D.tree r I
  isTree := starTree_isTree D.tree r D.isTree
  bag := copyBag S D.bag
  small t := by
    cases t with
    | none => simpa [copyBag] using hs
    | some it => simpa [copyBag] using D.small it.2
  cover x := by
    cases x with
    | inl v => exact ⟨none,inl_mem_central S D.bag v⟩
    | inr iv =>
      obtain ⟨t,ht⟩ := D.cover iv.2.val
      exact ⟨some (iv.1,t),by simp [ht]⟩
  edge x y he := by
    cases x with
    | inl u =>
      cases y with
      | inl v => exact ⟨none,by simp,by simp⟩
      | inr iv =>
        obtain ⟨t,hu,hv⟩ := D.edge u.val iv.2.val he.1
        exact ⟨some (iv.1,t),by simp [hu],by simp [hv]⟩
    | inr iu =>
      cases y with
      | inl v =>
        obtain ⟨t,hu,hv⟩ := D.edge iu.2.val v.val he.1
        exact ⟨some (iu.1,t),by simp [hu],by simp [hv]⟩
      | inr iv =>
        obtain ⟨t,hu,hv⟩ := D.edge iu.2.val iv.2.val he.1
        have hi : iu.1 = iv.1 := he.2
        exact ⟨some (iu.1,t),by simp [hu],by simp [hv,hi]⟩
  running x := by
    cases x with
    | inl v =>
      let H := (starTree D.tree r I).induce {t | Sum.inl v ∈ copyBag S D.bag t}
      let centre : {t // Sum.inl v ∈ copyBag (I := I) S D.bag t} := ⟨none,by simp⟩
      have reach (t : {t // Sum.inl v ∈ copyBag (I := I) S D.bag t}) : H.Reachable centre t := by
        rcases t with ⟨t,ht⟩
        cases t with
        | none => exact .rfl
        | some it =>
          have hv : v.val ∈ D.bag r := hS v.property
          let f : (D.tree.induce {j | v.val ∈ D.bag j}) →g H :=
            ⟨fun j => ⟨some (it.1,j.val),(inl_mem_copyBag S D.bag v it.1 j.val).mpr j.property⟩,fun h => ⟨rfl,h⟩⟩
          have hr : H.Adj centre (f ⟨r,hv⟩) := rfl
          exact hr.reachable.trans ((D.running v.val ⟨r,hv⟩
            ⟨it.2,(inl_mem_copyBag S D.bag v it.1 it.2).mp ht⟩).map f)
      intro s t
      exact (reach s).symm.trans (reach t)
    | inr iv =>
      let H := (starTree D.tree r I).induce {t | Sum.inr iv ∈ copyBag S D.bag t}
      let f : (D.tree.induce {j | iv.2.val ∈ D.bag j}) →g H :=
        ⟨fun j => ⟨some (iv.1,j.val),(inr_mem_copyBag S D.bag iv iv.1 j.val).mpr ⟨rfl,j.property⟩⟩,fun h => ⟨rfl,h⟩⟩
      have lift (t : {t // Sum.inr iv ∈ copyBag S D.bag t}) : ∃ j, f j = t := by
        rcases t with ⟨t,ht⟩
        cases t with
        | none => exact (inr_not_mem_central S D.bag iv.1 iv.2 ht).elim
        | some jt =>
          have hh := (inr_mem_copyBag S D.bag iv jt.1 jt.2).mp ht
          refine ⟨⟨jt.2,hh.2⟩,?_⟩
          apply Subtype.ext
          change some (iv.1,jt.2) = some jt
          rw [hh.1]
      intro s t
      obtain ⟨j,rfl⟩ := lift s
      obtain ⟨k,rfl⟩ := lift t
      exact (D.running iv.2.val j k).map f

omit [Fintype V] in
theorem boundary_in_bag (D : Structure.Bags G J) {S : Finset V}
    (hS : BoundaryShape G S) : ∃ r, S ⊆ D.bag r := by
  rcases hS with rfl | ⟨u,rfl⟩ | ⟨u,v,rfl,he⟩
  · obtain ⟨r⟩ := D.isTree.isConnected.nonempty
    exact ⟨r,Finset.empty_subset _⟩
  · obtain ⟨r,hr⟩ := D.cover u
    exact ⟨r,by simpa⟩
  · obtain ⟨r,hu,hv⟩ := D.edge u v he
    exact ⟨r,Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)⟩

omit [Fintype V] in
theorem boundary_card_le_three {S : Finset V} (hS : BoundaryShape G S) : S.card ≤ 3 := by
  rcases hS with rfl | ⟨u,rfl⟩ | ⟨u,v,rfl,_⟩
  · simp
  · simp
  · exact (Finset.card_insert_le _ _).trans (by simp)

theorem treewidth [Fintype I] (hw : TreewidthAtMostTwo G) {S : Finset V}
    (hS : BoundaryShape G S) : TreewidthAtMostTwo (graph G S I) := by
  obtain ⟨n,⟨D⟩⟩ := Structure.bags_of_treewidth hw
  obtain ⟨r,hr⟩ := boundary_in_bag D hS
  exact (bags (I := I) D S r hr (boundary_card_le_three hS)).treewidth

end
end CoefficientwiseRigidity.Replica
