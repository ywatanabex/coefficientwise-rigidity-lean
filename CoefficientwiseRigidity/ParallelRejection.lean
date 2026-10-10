import CoefficientwiseRigidity.RepresentativeCover
import CoefficientwiseRigidity.OrdinaryWitness

/-! A flat simple representative misses a global configuration whenever the full labelled cover is nonflat. -/
namespace CoefficientwiseRigidity.LabelledCover
open scoped Classical
noncomputable section
variable {V E : Type*} {M : ℕ}

theorem exists_rejected (X : LabelledCover V E M) (a : V → ℕ)
    (ha : Feasible X.graph M a) (hp : Positive a)
    (hr : CoefficientwiseRigidity.Flat X.representative) (hn : ¬ X.Flat) :
    ∃ S : CoefficientwiseRigidity.Configuration X.representative a, ¬ X.Admissible a S.val := by
  obtain ⟨γ,hγ⟩ := hr
  have hbad : ¬ ∀ e i, X.transport e (γ (X.left e) i) = γ (X.right e) i :=
    fun h => hn ⟨γ,h⟩
  push_neg at hbad
  obtain ⟨e,i,hi⟩ := hbad
  let j := (γ (X.right e)).symm (X.transport e (γ (X.left e) i))
  have hij : i ≠ j := by
    intro h
    apply hi
    have hh := congrArg (γ (X.right e)) h
    simpa [j] using hh.symm
  obtain ⟨S,hleft,hright⟩ := exists_ordinary_edge_labels X.bipartition a ha
    (show X.graph.Adj (X.left e) (X.right e) from ⟨e,Or.inl ⟨rfl,rfl⟩⟩)
    (X.left_side e) (hp _) (hp _) hij
  have hS : CoefficientwiseRigidity.Admissible X.representative a (relabel γ S.val) :=
    relabel_admissible _ _ a γ (fun u v he _ _ k => hγ u v he k) S.property
  refine ⟨⟨_,hS⟩,?_⟩
  intro hfull
  apply hfull.2 e (γ (X.left e) i)
  · exact Finset.mem_map.mpr ⟨i,hleft,rfl⟩
  · exact Finset.mem_map.mpr ⟨j,hright,by simp [j]⟩

variable [Fintype V] [DecidableEq V]

theorem coefficient_lt_representative (X : LabelledCover V E M) (a : V → ℕ)
    (ha : Feasible X.graph M a) (hp : Positive a)
    (hr : CoefficientwiseRigidity.Flat X.representative) (hn : ¬ X.Flat) :
    X.coefficient a < CoefficientwiseRigidity.coefficient X.representative a := by
  obtain ⟨S,hS⟩ := X.exists_rejected a ha hp hr hn
  apply Fintype.card_lt_of_injective_of_not_mem (X.toRepresentative a) (X.toRepresentative_injective a)
    (b := S)
  rintro ⟨T,hT⟩
  have hv := congrArg (fun Z : CoefficientwiseRigidity.Configuration X.representative a => Z.val) hT
  change T.val = S.val at hv
  exact hS (hv ▸ T.property)

theorem flat_of_representative_flat_of_eq (X : LabelledCover V E M) (a : V → ℕ)
    (ha : Feasible X.graph M a) (hp : Positive a)
    (hr : CoefficientwiseRigidity.Flat X.representative)
    (he : X.coefficient a = CoefficientwiseRigidity.coefficient X.representative a) : X.Flat := by
  by_contra hn
  have hh := X.coefficient_lt_representative a ha hp hr hn
  omega

/-- The exact C6 signed difference, with the omitted-edge term a natural count difference. -/
theorem deficit_decomposition (X : LabelledCover V E M) (a : V → ℕ) :
    (X.ordinary.coefficient a : ℤ) - X.coefficient a =
      CoefficientwiseRigidity.deficit X.representative a +
        (CoefficientwiseRigidity.coefficient X.representative a - X.coefficient a : ℕ) := by
  have hh := X.coefficient_le_representative a
  rw [Nat.cast_sub hh,X.ordinary_coefficient_eq, CoefficientwiseRigidity.deficit]
  ring

end
end CoefficientwiseRigidity.LabelledCover
