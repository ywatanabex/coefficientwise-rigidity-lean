import CoefficientwiseRigidity.SeamDomination

/-! The same contraction with the right piece retained. -/
namespace CoefficientwiseRigidity.Gluing
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V} {M : ℕ} {U₁ U₂ : Finset V}

def matchingSwap {A B C : Type} (f : A → C) (g : B → C) :
    {p : A × B // f p.1 = g p.2} ≃ {p : B × A // g p.1 = f p.2} where
  toFun p := ⟨(p.val.2, p.val.1), p.property.symm⟩
  invFun p := ⟨(p.val.2, p.val.1), p.property.symm⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

omit [Fintype V] in
theorem smallBoundary_left (hs : LegalSeam U₁ U₂ G₁ G₂) :
    SmallBoundary (G₁.induce (↑U₁ : Set V)) (leftIndex U₁ U₂) := by
  rcases hs with he | ⟨v, he⟩ | ⟨u, v, he, huv, _⟩
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
theorem right_pin_on_left (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hs : LegalSeam U₁ U₂ G₁ G₂) (L : RightConfiguration X a U₂) :
    PinAdmissible (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val)
      (leftIndex U₁ U₂) (rightBoundary X a U₁ U₂ L) := by
  refine ⟨fun i => L.property.1 (rightIndex U₁ U₂ i), ?_⟩
  intro i j hij
  change G₁.Adj i.val j.val at hij
  have hne : i.val ≠ j.val := by
    intro h
    rw [h] at hij
    exact G₁.loopless _ hij
  have hleft := seam_clique_left (seam_symm hs)
    (by simp [Finset.inter_comm, i.property])
    (by simp [Finset.inter_comm, j.property]) hne
  exact (coverEdgePin (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val)
    (rightIndex U₁ U₂ i) (rightIndex U₁ U₂ j) hleft L).property.2.2

omit [Fintype V] in
theorem right_predicate_sum (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₂ : SupportedOn G₂ U₂) (hU₁ : SupportedOn G₁ U₁)
    (P : RightConfiguration X a U₂ → Prop) :
    Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (rightPart X a U₁ U₂ S)} =
      ∑ L : {T : RightConfiguration X a U₂ // P T},
        pinnedCount (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val)
          (leftIndex U₁ U₂) (rightBoundary X a U₁ U₂ L.val) := by
  let e := (configurationPullbackEquiv X a U₁ U₂ hU₁ hU₂).trans
    (matchingSwap (leftBoundary X a U₁ U₂) (rightBoundary X a U₁ U₂))
  let e₁ := predicateEquiv e (fun p => P p.val.1)
  let e₂ := matchingPairPredicateEquiv (rightBoundary X a U₁ U₂)
    (leftBoundary X a U₁ U₂) P
  let e₃ := matchingByLeft (fun L : {T : RightConfiguration X a U₂ // P T} =>
    rightBoundary X a U₁ U₂ L.val) (leftBoundary X a U₁ U₂)
  change Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (e S).val.1} = _
  rw [Fintype.card_congr ((e₁.trans e₂).trans e₃), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro L _
  simp only [pinnedCount, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro R
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

def leftSeamConstant (a : V → ℕ) (U₁ U₂ : Finset V)
    (O₂ : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁) : ℕ :=
  pinnedCount (trivialCover (G₁.induce (↑U₁ : Set V)) M) (fun v => a v.val)
    (leftIndex U₁ U₂) (fun i => O₂.val (leftIndex U₁ U₂ i))

omit [Fintype V] in
theorem leftSeamConstant_pos (a : V → ℕ)
    (O₂ : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁) :
    0 < leftSeamConstant a U₁ U₂ O₂ := by
  simp only [leftSeamConstant, pinnedCount, ← Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨O₂, fun _ => rfl⟩⟩

omit [Fintype V] in
theorem right_predicate_le (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₂ : SupportedOn G₂ U₂) (hU₁ : SupportedOn G₁ U₁)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₂ : BoundaryComparison (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val))
    (O₂ : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁)
    (P : RightConfiguration X a U₂ → Prop) :
    Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (rightPart X a U₁ U₂ S)} ≤
      leftSeamConstant a U₁ U₂ O₂ * Fintype.card {L : RightConfiguration X a U₂ // P L} := by
  rw [right_predicate_sum X a hU₂ hU₁ P]
  calc
    _ ≤ ∑ _L : {T : RightConfiguration X a U₂ // P T}, leftSeamConstant a U₁ U₂ O₂ := by
      apply Finset.sum_le_sum
      intro L _
      exact h₂ _ _ (smallBoundary_left hs) _ (right_pin_on_left X a hs L.val) O₂
    _ = _ := by simp [mul_comm]

omit [Fintype V] in
theorem ordinary_right_predicate_eq (a : V → ℕ)
    (hU₂ : SupportedOn G₂ U₂) (hU₁ : SupportedOn G₁ U₁)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (O₂ : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁)
    (P : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂ → Prop) :
    Fintype.card {S : UnionConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ //
      P (rightPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ S)} =
      leftSeamConstant a U₁ U₂ O₂ *
        Fintype.card {L : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂ // P L} := by
  rw [right_predicate_sum _ a hU₂ hU₁ P]
  calc
    _ = ∑ _L : {T : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) a U₂ // P T},
        leftSeamConstant a U₁ U₂ O₂ := by
      apply Finset.sum_congr rfl
      intro L _
      exact ordinary_pinned_constant (M := M) (G := G₁.induce (↑U₁ : Set V))
        (fun v => a v.val) _ (smallBoundary_left hs)
        (rightBoundary (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ L.val)
        (right_pin_on_left (trivialCover (G₁ ⊔ G₂) M) a hs L.val) O₂
    _ = _ := by simp [mul_comm]


end
end CoefficientwiseRigidity.Gluing
