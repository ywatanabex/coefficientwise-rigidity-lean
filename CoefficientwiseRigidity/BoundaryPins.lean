import CoefficientwiseRigidity.BoundaryAmplification

/-! Exact bridges from induced boundary configurations to the original root/edge pins. -/
namespace CoefficientwiseRigidity.Replica
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def rootBoundaryEquiv (X : Cover G M) (a : V → ℕ) (u : V) :
    BoundaryConfiguration X a {u} ≃ Kernel.Slice M (a u) where
  toFun b := ⟨b.val ⟨u,by simp⟩,b.property.1 _⟩
  invFun A := ⟨fun _ => A.val,⟨fun v => by
    have hv : v.val = u := by simpa using v.property
    simpa [hv] using A.property,by
    intro x y he
    have hx : x.val = u := by simpa using x.property
    have hy : y.val = u := by simpa using y.property
    have hh : G.Adj x.val y.val := he
    simp [hx,hy] at hh⟩⟩
  left_inv b := by
    apply Subtype.ext
    funext v
    have hv : v = ⟨u,by simp⟩ := Subtype.ext (by simpa using v.property)
    subst v
    rfl
  right_inv _ := rfl

def rootBoundaryFibreEquiv (X : Cover G M) (a : V → ℕ) (u : V)
    (b : BoundaryConfiguration X a {u}) :
    Fibre X a {u} b ≃ {C : Configuration X a // C.val u = (rootBoundaryEquiv X a u b).val} where
  toFun C := ⟨C.val,congrFun (congrArg Subtype.val C.property) ⟨u,by simp⟩⟩
  invFun C := ⟨C.val,by
    apply Subtype.ext
    funext v
    have hv : v = ⟨u,by simp⟩ := Subtype.ext (by simpa using v.property)
    subst v
    exact C.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem card_rootBoundary (X : Cover G M) (a : V → ℕ) (u : V) :
    Fintype.card (BoundaryConfiguration X a {u}) = M.choose (a u) := by
  rw [Fintype.card_congr (rootBoundaryEquiv X a u),Kernel.slice_card]

theorem card_rootBoundaryFibre (X : Cover G M) (a : V → ℕ) (u : V)
    (b : BoundaryConfiguration X a {u}) :
    Fintype.card (Fibre X a {u} b) = rootFibre X a u (rootBoundaryEquiv X a u b).val :=
  Fintype.card_congr (rootBoundaryFibreEquiv X a u b)

def edgeBoundaryEquiv (X : Cover G M) (a : V → ℕ) (u v : V) (huv : G.Adj u v) :
    BoundaryConfiguration X a {u,v} ≃ Gluing.TransportedEdgePin (X.transport u v) (a u) (a v) where
  toFun b := Gluing.coverEdgePin (restrictCover X {u,v} G le_rfl) (fun w => a w.val)
    ⟨u,by simp⟩ ⟨v,by simp⟩ huv b
  invFun AB := by
    have hne : u ≠ v := huv.ne
    let s : Assignment (↑({u,v} : Finset V) : Set V) M :=
      fun w => if w.val = u then AB.val.1 else AB.val.2
    have hu : s ⟨u,by simp⟩ = AB.val.1 := by simp [s]
    have hv : s ⟨v,by simp⟩ = AB.val.2 := by simp [s,hne.symm]
    refine ⟨s,⟨?_,?_⟩⟩
    · intro w
      have hw : w.val = u ∨ w.val = v := by simpa using w.property
      rcases hw with hw | hw
      · simpa [s,hw] using AB.property.1
      · simpa [s,hw,hne.symm] using AB.property.2.1
    · intro x y he i hi hj
      have hx : x.val = u ∨ x.val = v := by simpa using x.property
      have hy : y.val = u ∨ y.val = v := by simpa using y.property
      have hedge : G.Adj x.val y.val := he
      change X.transport x.val y.val i ∈ s y at hj
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · simp [hx,hy] at hedge
      · have hi' : i ∈ AB.val.1 := by simpa [s,hx] using hi
        have hj' : X.transport u v i ∈ AB.val.2 := by simpa [s,hx,hy,hne.symm] using hj
        exact Finset.disjoint_left.mp AB.property.2.2 (Finset.mem_map.mpr ⟨i,hi',rfl⟩) hj'
      · have hi' : i ∈ AB.val.2 := by simpa [s,hx,hne.symm] using hi
        have hj' : (X.transport u v).symm i ∈ AB.val.1 := by
          simpa [s,hx,hy,X.reverse huv] using hj
        exact Finset.disjoint_left.mp AB.property.2.2
          (Finset.mem_map.mpr ⟨_,hj',by simp⟩) hi'
      · simp [hx,hy] at hedge
  left_inv b := by
    apply Subtype.ext
    funext w
    have hw : w.val = u ∨ w.val = v := by simpa using w.property
    rcases hw with hw | hw
    · have he : w = ⟨u,by simp⟩ := Subtype.ext hw
      subst w
      simp [Gluing.coverEdgePin]
    · have he : w = ⟨v,by simp⟩ := Subtype.ext hw
      subst w
      simp [Gluing.coverEdgePin,huv.ne.symm]
  right_inv AB := by
    apply Subtype.ext
    simp [Gluing.coverEdgePin,huv.ne.symm]

def edgeBoundaryFibreEquiv (X : Cover G M) (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (b : BoundaryConfiguration X a {u,v}) :
    Fibre X a {u,v} b ≃ {C : Configuration X a //
      C.val u = (edgeBoundaryEquiv X a u v huv b).val.1 ∧
      C.val v = (edgeBoundaryEquiv X a u v huv b).val.2} where
  toFun C := ⟨C.val,congrFun (congrArg Subtype.val C.property) ⟨u,by simp⟩,
    congrFun (congrArg Subtype.val C.property) ⟨v,by simp⟩⟩
  invFun C := ⟨C.val,by
    apply Subtype.ext
    funext w
    have hw : w.val = u ∨ w.val = v := by simpa using w.property
    rcases hw with hw | hw
    · have he : w = ⟨u,by simp⟩ := Subtype.ext hw
      subst w
      exact C.property.1
    · have he : w = ⟨v,by simp⟩ := Subtype.ext hw
      subst w
      exact C.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem card_edgeBoundary (X : Cover G M) (a : V → ℕ) (u v : V) (huv : G.Adj u v) :
    Fintype.card (BoundaryConfiguration X a {u,v}) =
      M.choose (a u) * (M - a u).choose (a v) := by
  rw [Fintype.card_congr (edgeBoundaryEquiv X a u v huv),Gluing.card_transportedEdgePin]

theorem card_edgeBoundaryFibre (X : Cover G M) (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (b : BoundaryConfiguration X a {u,v}) :
    Fintype.card (Fibre X a {u,v} b) = edgeFibre X a u v
      (edgeBoundaryEquiv X a u v huv b).val.1 (edgeBoundaryEquiv X a u v huv b).val.2 :=
  Fintype.card_congr (edgeBoundaryFibreEquiv X a u v huv b)

end
end CoefficientwiseRigidity.Replica
