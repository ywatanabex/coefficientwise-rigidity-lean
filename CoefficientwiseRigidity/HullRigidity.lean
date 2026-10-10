import CoefficientwiseRigidity.SeamScalars
import CoefficientwiseRigidity.MainA

/-! Equality propagates to both children, and their active gauges glue. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {U : Finset V}

omit [Fintype V] in
theorem StructuralHull.equality_activeFlat (h : StructuralHull U G) :
    ∀ (M : ℕ), 1 ≤ M → ∀ (_b : Bipartition G) (X : Cover G M) (a : V → ℕ),
      Feasible (G.induce (↑U : Set V)) M (fun v => a v.val) →
      coefficient (restrictCover X U G le_rfl) (fun v => a v.val) =
        ordinary (G.induce (↑U : Set V)) M (fun v => a v.val) → ActiveFlat X a := by
  induction h with
  | atom U G hs hg =>
    intro M hM b X a ha he
    let b' : Bipartition (G.induce (↑U : Set V)) := ⟨fun v => b.side v.val, fun he => b.opposite he⟩
    have hsupp : StructuralAtom (supportGraph (G.induce (↑U : Set V)) (fun v => a v.val)) := by
      rcases hg with hw | hc
      · exact Or.inl (treewidth_induce hw _)
      · exact Or.inr (chordalBipartite_induce hc _)
    have hf := ((paperMainA b' M hM (restrictCover X U G le_rfl) _ ha hsupp).2).mp he
    exact (Gluing.activeFlat_restrict_iff X a U G le_rfl hs).mp hf
  | @glue U₁ U₂ G₁ G₂ h₁ h₂ hs ih₁ ih₂ =>
    intro M hM b X a ha he
    let b₁ : Bipartition G₁ := ⟨b.side, fun he => b.opposite (Or.inl he)⟩
    let b₂ : Bipartition G₂ := ⟨b.side, fun he => b.opposite (Or.inr he)⟩
    let bu : Bipartition ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) :=
      ⟨fun v => b.side v.val, fun he => b.opposite he⟩
    let O : Gluing.UnionConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ :=
      ⟨nestedAssignment bu M (fun v => a v.val), nestedAssignment_admissible bu _ ha⟩
    have hb₁ := h₁.boundary_comparison M b₁ (Gluing.subCover X G₁ le_sup_left) a
    have hb₂ := h₂.boundary_comparison M b₂ (Gluing.subCover X G₂ le_sup_right) a
    obtain ⟨he₁, he₂⟩ := Gluing.equality_forces_children X a h₁.supported h₂.supported hs hb₁ hb₂ O he
    have ha₁ : Feasible (G₁.induce (↑U₁ : Set V)) M (fun v => a v.val) :=
      ⟨fun v => ha.1 ⟨v.val, Finset.mem_union_left _ v.property⟩,
        fun u v huv => ha.2 ⟨u.val, Finset.mem_union_left _ u.property⟩
          ⟨v.val, Finset.mem_union_left _ v.property⟩ (Or.inl huv)⟩
    have ha₂ : Feasible (G₂.induce (↑U₂ : Set V)) M (fun v => a v.val) :=
      ⟨fun v => ha.1 ⟨v.val, Finset.mem_union_right _ v.property⟩,
        fun u v huv => ha.2 ⟨u.val, Finset.mem_union_right _ u.property⟩
          ⟨v.val, Finset.mem_union_right _ v.property⟩ (Or.inr huv)⟩
    exact (Gluing.activeFlat_sup_iff X a h₁.supported h₂.supported hs).mpr
      ⟨ih₁ M hM b₁ (Gluing.subCover X G₁ le_sup_left) a ha₁ he₁,
        ih₂ M hM b₂ (Gluing.subCover X G₂ le_sup_right) a ha₂ he₂⟩

theorem coefficient_restrict_univ {M : ℕ} (X : Cover G M) (a : V → ℕ) :
    coefficient (restrictCover X Finset.univ G le_rfl) (fun v => a v.val) = coefficient X a :=
  (Fintype.card_congr (Gluing.univConfigurationEquiv X a)).symm

/-- An inhabitant of the original, unchanged MainCComparisonRigidity proposition. -/
theorem paperMainCComparisonRigidity (b : Bipartition G) : MainCComparisonRigidity G := by
  intro h M hM X a
  refine ⟨h.coefficient_le b X a, ?_⟩
  intro ha
  constructor
  · intro he
    apply h.equality_activeFlat M hM b X a
    · exact ⟨fun v => ha.1 v.val, fun u v huv => ha.2 u.val v.val huv⟩
    · have ho := coefficient_restrict_univ (trivialCover G M) a
      change ordinary (G.induce (↑(Finset.univ : Finset V) : Set V)) M (fun v => a v.val) =
        ordinary G M a at ho
      rw [coefficient_restrict_univ, ho]
      exact he
  · exact activeFlat_coefficient_eq X a

end
end CoefficientwiseRigidity
