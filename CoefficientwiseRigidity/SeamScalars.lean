import CoefficientwiseRigidity.HullComparison

/-! Exact scalar factorization and equality transfer on the actual two pieces. -/
namespace CoefficientwiseRigidity.Gluing
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V} {M : ℕ} {U₁ U₂ : Finset V}

omit [Fintype V] in
theorem coefficient_glue_le_left (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₂ : BoundaryComparison (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val))
    (O₂ : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂) :
    coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => a v.val) ≤
      seamConstant a U₁ U₂ O₂ * coefficient (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val) := by
  simpa only [Fintype.card_subtype_true] using left_predicate_le X a hU₁ hU₂ hs h₂ O₂ (fun _ => True)

omit [Fintype V] in
theorem ordinary_glue_left (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (O₂ : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂) :
    ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) M (fun v => a v.val) =
      seamConstant a U₁ U₂ O₂ * ordinary (G₁.induce (↑U₁ : Set V)) M (fun v => a v.val) := by
  simpa only [Fintype.card_subtype_true] using ordinary_left_predicate_eq a hU₁ hU₂ hs O₂ (fun _ => True)

omit [Fintype V] in
theorem coefficient_glue_le_right (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₁ : BoundaryComparison (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val))
    (O₁ : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁) :
    coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => a v.val) ≤
      leftSeamConstant a U₁ U₂ O₁ * coefficient (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val) := by
  simpa only [Fintype.card_subtype_true] using right_predicate_le X a hU₂ hU₁ hs h₁ O₁ (fun _ => True)

omit [Fintype V] in
theorem ordinary_glue_right (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (O₁ : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁) :
    ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) M (fun v => a v.val) =
      leftSeamConstant a U₁ U₂ O₁ * ordinary (G₂.induce (↑U₂ : Set V)) M (fun v => a v.val) := by
  simpa only [Fintype.card_subtype_true] using ordinary_right_predicate_eq a hU₂ hU₁ hs O₁ (fun _ => True)

omit [Fintype V] in
theorem equality_forces_children (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₁ : BoundaryComparison (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val))
    (h₂ : BoundaryComparison (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val))
    (O : UnionConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂)
    (he : coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => a v.val) =
      ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) M (fun v => a v.val)) :
    coefficient (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val) =
      ordinary (G₁.induce (↑U₁ : Set V)) M (fun v => a v.val) ∧
    coefficient (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val) =
      ordinary (G₂.induce (↑U₂ : Set V)) M (fun v => a v.val) := by
  let O₁ := leftPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ O
  let O₂ := rightPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ O
  have hl := coefficient_glue_le_left X a hU₁ hU₂ hs h₂ O₂
  have hr := coefficient_glue_le_right X a hU₁ hU₂ hs h₁ O₁
  rw [he, ordinary_glue_left a hU₁ hU₂ hs O₂] at hl
  rw [he, ordinary_glue_right a hU₁ hU₂ hs O₁] at hr
  exact ⟨Nat.le_antisymm (h₁.coefficient_le _ _ O₁) ((mul_le_mul_left (seamConstant_pos a O₂)).mp hl),
    Nat.le_antisymm (h₂.coefficient_le _ _ O₂) ((mul_le_mul_left (leftSeamConstant_pos a O₁)).mp hr)⟩

end
end CoefficientwiseRigidity.Gluing
