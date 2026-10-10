import CoefficientwiseRigidity.HullQuantitative

/-! Theorem C(ii): every atom and intermediate occurrence retains its relative deficit. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- An occurrence in a finite construction, including an intermediate subtree. -/
inductive ConstructionPiece (W : Finset V) (H : SimpleGraph V) :
    Finset V → SimpleGraph V → Prop
  | here (h : StructuralHull W H) : ConstructionPiece W H W H
  | left {U₁ U₂ : Finset V} {G₁ G₂ : SimpleGraph V}
      (h₁ : ConstructionPiece W H U₁ G₁) (h₂ : StructuralHull U₂ G₂)
      (hs : LegalSeam U₁ U₂ G₁ G₂) : ConstructionPiece W H (U₁ ∪ U₂) (G₁ ⊔ G₂)
  | right {U₁ U₂ : Finset V} {G₁ G₂ : SimpleGraph V}
      (h₁ : StructuralHull U₁ G₁) (h₂ : ConstructionPiece W H U₂ G₂)
      (hs : LegalSeam U₁ U₂ G₁ G₂) : ConstructionPiece W H (U₁ ∪ U₂) (G₁ ⊔ G₂)

variable {W U : Finset V} {H G : SimpleGraph V}

omit [Fintype V] in
theorem ConstructionPiece.toStructuralHull (h : ConstructionPiece W H U G) : StructuralHull U G := by
  induction h with
  | here h => exact h
  | left _ h₂ hs ih => exact .glue ih h₂ hs
  | right h₁ _ hs ih => exact .glue h₁ ih hs

omit [Fintype V] in
theorem ConstructionPiece.subgraph (h : ConstructionPiece W H U G) : H ≤ G := by
  induction h with
  | here _ => exact le_rfl
  | left _ _ _ ih => exact le_trans ih le_sup_left
  | right _ _ _ ih => exact le_trans ih le_sup_right

def relativeDeficit {M : ℕ} (X : Cover G M) (a : V → ℕ) : ℚ :=
  ((ordinary G M a : ℚ) - coefficient X a) / ordinary G M a

theorem relativeDeficit_of_factors (Z P Z₁ P₁ c : ℕ)
    (hZ : Z ≤ c * Z₁) (hP : P = c * P₁) (hc : 0 < c) (hP₁ : 0 < P₁) :
    ((P₁ : ℚ) - Z₁) / P₁ ≤ ((P : ℚ) - Z) / P := by
  have hp : 0 < (P : ℚ) := by rw [hP]; positivity
  have hp₁ : 0 < (P₁ : ℚ) := by exact_mod_cast hP₁
  have hz : (Z : ℚ) ≤ (c : ℚ) * Z₁ := by exact_mod_cast hZ
  have he : (P : ℚ) = (c : ℚ) * P₁ := by exact_mod_cast hP
  apply (div_le_div_iff₀ hp₁ hp).mpr
  rw [he]
  nlinarith

omit [Fintype V] in
theorem ConstructionPiece.relative_deficit (h : ConstructionPiece W H U G) :
    ∀ (M : ℕ) (_b : Bipartition G) (X : Cover G M) (a : V → ℕ),
      Feasible (G.induce (↑U : Set V)) M (fun v => a v.val) →
      relativeDeficit (restrictCover X W H h.subgraph) (fun v => a v.val) ≤
        relativeDeficit (restrictCover X U G le_rfl) (fun v => a v.val) := by
  induction h with
  | here _ => intro M _b X a ha; exact le_rfl
  | @left U₁ U₂ G₁ G₂ h₁ h₂ hs ih =>
    intro M b X a ha
    let b₁ : Bipartition G₁ := ⟨b.side, fun he => b.opposite (Or.inl he)⟩
    let b₂ : Bipartition G₂ := ⟨b.side, fun he => b.opposite (Or.inr he)⟩
    let bu : Bipartition ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) :=
      ⟨fun v => b.side v.val, fun he => b.opposite he⟩
    let O : Gluing.UnionConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ :=
      ⟨nestedAssignment bu M (fun v => a v.val), nestedAssignment_admissible bu _ ha⟩
    let O₂ := Gluing.rightPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ O
    have ha₁ : Feasible (G₁.induce (↑U₁ : Set V)) M (fun v => a v.val) :=
      ⟨fun v => ha.1 ⟨v.val, Finset.mem_union_left _ v.property⟩,
        fun u v he => ha.2 ⟨u.val, Finset.mem_union_left _ u.property⟩
          ⟨v.val, Finset.mem_union_left _ v.property⟩ (Or.inl he)⟩
    have hp₁ := (ordinary_pos_iff_feasible
      (⟨fun v => b₁.side v.val, fun he => b₁.opposite he⟩ : Bipartition (G₁.induce (↑U₁ : Set V)))
      (fun v => a v.val)).mpr ha₁
    exact (ih M b₁ (Gluing.subCover X G₁ le_sup_left) a ha₁).trans
      (relativeDeficit_of_factors _ _ _ _ _
        (Gluing.coefficient_glue_le_left X a h₁.toStructuralHull.supported h₂.supported hs
          (h₂.boundary_comparison M b₂ (Gluing.subCover X G₂ le_sup_right) a) O₂)
        (Gluing.ordinary_glue_left a h₁.toStructuralHull.supported h₂.supported hs O₂)
        (Gluing.seamConstant_pos a O₂) hp₁)
  | @right U₁ U₂ G₁ G₂ h₁ h₂ hs ih =>
    intro M b X a ha
    let b₁ : Bipartition G₁ := ⟨b.side, fun he => b.opposite (Or.inl he)⟩
    let b₂ : Bipartition G₂ := ⟨b.side, fun he => b.opposite (Or.inr he)⟩
    let bu : Bipartition ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) :=
      ⟨fun v => b.side v.val, fun he => b.opposite he⟩
    let O : Gluing.UnionConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ :=
      ⟨nestedAssignment bu M (fun v => a v.val), nestedAssignment_admissible bu _ ha⟩
    let O₁ := Gluing.leftPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ O
    have ha₂ : Feasible (G₂.induce (↑U₂ : Set V)) M (fun v => a v.val) :=
      ⟨fun v => ha.1 ⟨v.val, Finset.mem_union_right _ v.property⟩,
        fun u v he => ha.2 ⟨u.val, Finset.mem_union_right _ u.property⟩
          ⟨v.val, Finset.mem_union_right _ v.property⟩ (Or.inr he)⟩
    have hp₂ := (ordinary_pos_iff_feasible
      (⟨fun v => b₂.side v.val, fun he => b₂.opposite he⟩ : Bipartition (G₂.induce (↑U₂ : Set V)))
      (fun v => a v.val)).mpr ha₂
    exact (ih M b₂ (Gluing.subCover X G₂ le_sup_right) a ha₂).trans
      (relativeDeficit_of_factors _ _ _ _ _
        (Gluing.coefficient_glue_le_right X a h₁.supported h₂.toStructuralHull.supported hs
          (h₁.boundary_comparison M b₁ (Gluing.subCover X G₁ le_sup_left) a) O₁)
        (Gluing.ordinary_glue_right a h₁.supported h₂.toStructuralHull.supported hs O₁)
        (Gluing.leftSeamConstant_pos a O₁) hp₂)

theorem relativeDeficit_bounds (h : StructuralHull Finset.univ G) (b : Bipartition G)
    {M : ℕ} (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a) :
    0 ≤ relativeDeficit X a ∧ relativeDeficit X a ≤ 1 := by
  have hp : 0 < (ordinary G M a : ℚ) := by
    exact_mod_cast (ordinary_pos_iff_feasible b a).mpr ha
  have hz : (coefficient X a : ℚ) ≤ ordinary G M a := by exact_mod_cast h.coefficient_le b X a
  constructor
  · exact div_nonneg (sub_nonneg.mpr hz) hp.le
  · apply (div_le_iff₀ hp).mpr
    dsimp only
    have : 0 ≤ (coefficient X a : ℚ) := Nat.cast_nonneg _
    linarith

end
end CoefficientwiseRigidity
