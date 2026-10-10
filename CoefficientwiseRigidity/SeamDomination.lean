import CoefficientwiseRigidity.PinnedComparison

/-! A legal seam contracts to a single ordinary fibre, with arbitrary left predicates retained. -/
namespace CoefficientwiseRigidity.Gluing
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V} {M : ℕ} {U₁ U₂ : Finset V}

def leftIndex (U₁ U₂ : Finset V) (v : (↑(U₁ ∩ U₂) : Set V)) : (↑U₁ : Set V) :=
  ⟨v.val, (Finset.mem_inter.mp v.property).1⟩
def rightIndex (U₁ U₂ : Finset V) (v : (↑(U₁ ∩ U₂) : Set V)) : (↑U₂ : Set V) :=
  ⟨v.val, (Finset.mem_inter.mp v.property).2⟩

omit [Fintype V] in
theorem smallBoundary_right (hs : LegalSeam U₁ U₂ G₁ G₂) :
    SmallBoundary (G₂.induce (↑U₂ : Set V)) (rightIndex U₁ U₂) := by
  rcases hs with he | ⟨v, he⟩ | ⟨u, v, he, _, huv⟩
  · exact Or.inl ⟨fun v => by have := v.property; simp [he] at this⟩
  · let i : (↑(U₁ ∩ U₂) : Set V) := ⟨v, by simp [he]⟩
    exact Or.inr (Or.inl ⟨i, fun j => Subtype.ext (by simpa [he] using j.property)⟩)
  · let i : (↑(U₁ ∩ U₂) : Set V) := ⟨u, by simp [he]⟩
    let j : (↑(U₁ ∩ U₂) : Set V) := ⟨v, by simp [he]⟩
    refine Or.inr (Or.inr ⟨i, j, huv, ?_⟩)
    intro k
    have hk : k.val = u ∨ k.val = v := by simpa [he] using k.property
    exact hk.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)

omit [Fintype V] in
theorem left_pin_on_right (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hs : LegalSeam U₁ U₂ G₁ G₂) (L : LeftConfiguration X a U₁) :
    PinAdmissible (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val)
      (rightIndex U₁ U₂) (leftBoundary X a U₁ U₂ L) := by
  refine ⟨fun i => L.property.1 (leftIndex U₁ U₂ i), ?_⟩
  intro i j hij
  change G₂.Adj i.val j.val at hij
  have hne : i.val ≠ j.val := by
    intro h
    rw [h] at hij
    exact G₂.loopless _ hij
  have hleft := seam_clique_left hs i.property j.property hne
  exact (coverEdgePin (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val)
    (leftIndex U₁ U₂ i) (leftIndex U₁ U₂ j) hleft L).property.2.2

/-- Pullback counted by the left configuration, rather than by all assignments on the seam. -/
def matchingByLeft {A B C : Type} (f : A → C) (g : B → C) :
    {p : A × B // f p.1 = g p.2} ≃ Σ a : A, {b : B // g b = f a} where
  toFun p := ⟨p.val.1, p.val.2, p.property.symm⟩
  invFun p := ⟨(p.1, p.2.val), p.2.property.symm⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

omit [Fintype V] in
theorem left_predicate_sum (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (P : LeftConfiguration X a U₁ → Prop) :
    Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (leftPart X a U₁ U₂ S)} =
      ∑ L : {T : LeftConfiguration X a U₁ // P T},
        pinnedCount (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val)
          (rightIndex U₁ U₂) (leftBoundary X a U₁ U₂ L.val) := by
  let e := configurationPullbackEquiv X a U₁ U₂ hU₁ hU₂
  let e₁ := predicateEquiv e (fun p => P p.val.1)
  let e₂ := matchingPairPredicateEquiv (leftBoundary X a U₁ U₂)
    (rightBoundary X a U₁ U₂) P
  let e₃ := matchingByLeft (fun L : {T : LeftConfiguration X a U₁ // P T} =>
    leftBoundary X a U₁ U₂ L.val) (rightBoundary X a U₁ U₂)
  change Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (e S).val.1} = _
  rw [Fintype.card_congr ((e₁.trans e₂).trans e₃), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro L _
  simp only [pinnedCount, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro R
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

def seamConstant (a : V → ℕ) (U₁ U₂ : Finset V)
    (O₂ : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂) : ℕ :=
  pinnedCount (trivialCover (G₂.induce (↑U₂ : Set V)) M) (fun v => a v.val)
    (rightIndex U₁ U₂) (fun i => O₂.val (rightIndex U₁ U₂ i))

omit [Fintype V] in
theorem seamConstant_pos (a : V → ℕ)
    (O₂ : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂) :
    0 < seamConstant a U₁ U₂ O₂ := by
  simp only [seamConstant, pinnedCount, ← Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨O₂, fun _ => rfl⟩⟩

omit [Fintype V] in
theorem left_predicate_le (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₂ : BoundaryComparison (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val))
    (O₂ : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂)
    (P : LeftConfiguration X a U₁ → Prop) :
    Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (leftPart X a U₁ U₂ S)} ≤
      seamConstant a U₁ U₂ O₂ * Fintype.card {L : LeftConfiguration X a U₁ // P L} := by
  rw [left_predicate_sum X a hU₁ hU₂ P]
  calc
    _ ≤ ∑ _L : {T : LeftConfiguration X a U₁ // P T}, seamConstant a U₁ U₂ O₂ := by
      apply Finset.sum_le_sum
      intro L _
      exact h₂ _ _ (smallBoundary_right hs) _ (left_pin_on_right X a hs L.val) O₂
    _ = _ := by simp [mul_comm]

omit [Fintype V] in
theorem ordinary_left_predicate_eq (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (O₂ : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂)
    (P : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ → Prop) :
    Fintype.card {S : UnionConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ //
      P (leftPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ S)} =
      seamConstant a U₁ U₂ O₂ *
        Fintype.card {L : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ // P L} := by
  rw [left_predicate_sum _ a hU₁ hU₂ P]
  calc
    _ = ∑ _L : {T : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ // P T},
        seamConstant a U₁ U₂ O₂ := by
      apply Finset.sum_congr rfl
      intro L _
      exact ordinary_pinned_constant (M := M) (G := G₂.induce (↑U₂ : Set V))
        (fun v => a v.val) _ (smallBoundary_right hs)
        (leftBoundary (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ L.val)
        (left_pin_on_right (trivialCover (G₁ ⊔ G₂) M) a hs L.val) O₂
    _ = _ := by simp [mul_comm]

end
end CoefficientwiseRigidity.Gluing
