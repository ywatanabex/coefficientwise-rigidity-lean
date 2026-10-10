import CoefficientwiseRigidity.SeamFlatness

/-!
Actual configuration gluing and exact fibre counts.  The overlap is arbitrary:
no graph-class, comparison, positivity, or nonempty-boundary hypothesis is used.

Adapted from the user-supplied PRO handoff and checked locally.
These counting identities alone do not complete Main C.
-/

namespace CoefficientwiseRigidity.Gluing
open scoped BigOperators Classical
noncomputable section

section FiniteFibres
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- The actual pullback of two maps is the disjoint union of their fibre products. -/
def matchingPairEquiv (f : A → B) (g : C → B) :
    {p : A × C // f p.1 = g p.2} ≃
      Σ b : B, {x : A // f x = b} × {y : C // g y = b} where
  toFun p := ⟨f p.val.1, ⟨p.val.1, rfl⟩, ⟨p.val.2, p.property.symm⟩⟩
  invFun p := ⟨(p.2.1.val, p.2.2.val), p.2.1.property.trans p.2.2.property.symm⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv := by
    rintro ⟨b, ⟨x, hx⟩, ⟨y, hy⟩⟩
    cases hx
    rfl

theorem card_matchingPair (f : A → B) (g : C → B) :
    Fintype.card {p : A × C // f p.1 = g p.2} =
      ∑ b : B, Fintype.card {x : A // f x = b} *
        Fintype.card {y : C // g y = b} := by
  classical
  rw [Fintype.card_congr (matchingPairEquiv f g), Fintype.card_sigma]
  simp only [Fintype.card_prod]

/-- A predicate can be retained while transporting a finite configuration space. -/
def predicateEquiv (e : A ≃ C) (P : C → Prop) :
    {x : A // P (e x)} ≃ {y : C // P y} where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by simpa using y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

/-- Pinning or any other predicate on the left factor can be kept in the pullback. -/
def matchingPairPredicateEquiv (f : A → B) (g : C → B) (P : A → Prop) :
    {p : {q : A × C // f q.1 = g q.2} // P p.val.1} ≃
      {p : {x : A // P x} × C // f p.1.val = g p.2} where
  toFun p := ⟨(⟨p.val.val.1, p.property⟩, p.val.val.2), p.val.property⟩
  invFun p := ⟨⟨(p.val.1.val, p.val.2), p.property⟩, p.val.1.property⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

end FiniteFibres

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G G₁ G₂ : SimpleGraph V} {M : ℕ}

/-- This is the pre-existing configuration type on the pre-existing restricted cover. -/
abbrev PieceConfiguration (X : Cover G M) (a : V → ℕ)
    (U : Finset V) (H : SimpleGraph V) (hle : H ≤ G) :=
  Configuration (restrictCover X U H hle) (fun v => a v.val)

/-- All assignments on the intersection; impossible assignments have zero fibres. -/
abbrev SeamAssignment (U₁ U₂ : Finset V) (M : ℕ) :=
  Assignment (↑(U₁ ∩ U₂) : Set V) M

variable (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ) (U₁ U₂ : Finset V)

abbrev LeftConfiguration := PieceConfiguration X a U₁ G₁ le_sup_left
abbrev RightConfiguration := PieceConfiguration X a U₂ G₂ le_sup_right
abbrev UnionConfiguration := PieceConfiguration X a (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl

/-- Restriction to the left piece, with the original transports and occupations. -/
def leftPart (S : UnionConfiguration X a U₁ U₂) : LeftConfiguration X a U₁ :=
  ⟨fun v => S.val ⟨v.val, Finset.mem_union_left U₂ v.property⟩,
    ⟨fun v => S.property.1 ⟨v.val, Finset.mem_union_left U₂ v.property⟩, fun u v huv i hi =>
      S.property.2 ⟨u.val, Finset.mem_union_left U₂ u.property⟩
        ⟨v.val, Finset.mem_union_left U₂ v.property⟩ (Or.inl huv) i hi⟩⟩

/-- Restriction to the right piece. -/
def rightPart (S : UnionConfiguration X a U₁ U₂) : RightConfiguration X a U₂ :=
  ⟨fun v => S.val ⟨v.val, Finset.mem_union_right U₁ v.property⟩,
    ⟨fun v => S.property.1 ⟨v.val, Finset.mem_union_right U₁ v.property⟩, fun u v huv i hi =>
      S.property.2 ⟨u.val, Finset.mem_union_right U₁ u.property⟩
        ⟨v.val, Finset.mem_union_right U₁ v.property⟩ (Or.inr huv) i hi⟩⟩

def leftBoundary (S : LeftConfiguration X a U₁) : SeamAssignment U₁ U₂ M :=
  fun v => S.val ⟨v.val, (Finset.mem_inter.mp v.property).1⟩

def rightBoundary (S : RightConfiguration X a U₂) : SeamAssignment U₁ U₂ M :=
  fun v => S.val ⟨v.val, (Finset.mem_inter.mp v.property).2⟩

omit [Fintype V] in
@[simp] theorem parts_agree (S : UnionConfiguration X a U₁ U₂) :
    leftBoundary X a U₁ U₂ (leftPart X a U₁ U₂ S) =
      rightBoundary X a U₁ U₂ (rightPart X a U₁ U₂ S) := rfl

/-- A literal assignment: use the left value where possible, the right value elsewhere. -/
def glueAssignment (S₁ : LeftConfiguration X a U₁) (S₂ : RightConfiguration X a U₂) :
    Assignment (↑(U₁ ∪ U₂) : Set V) M := by
  classical
  exact fun v => if h : v.val ∈ U₁ then S₁.val ⟨v.val, h⟩
    else S₂.val ⟨v.val, (Finset.mem_union.mp v.property).resolve_left h⟩

omit [Fintype V] in
@[simp] theorem glueAssignment_left
    (S₁ : LeftConfiguration X a U₁) (S₂ : RightConfiguration X a U₂)
    (v : (↑(U₁ ∪ U₂) : Set V)) (hv : v.val ∈ U₁) :
    glueAssignment X a U₁ U₂ S₁ S₂ v = S₁.val ⟨v.val, hv⟩ := by
  classical
  simp [glueAssignment, hv]

omit [Fintype V] in
theorem glueAssignment_right
    (S₁ : LeftConfiguration X a U₁) (S₂ : RightConfiguration X a U₂)
    (hc : leftBoundary X a U₁ U₂ S₁ = rightBoundary X a U₁ U₂ S₂)
    (v : (↑(U₁ ∪ U₂) : Set V)) (hv : v.val ∈ U₂) :
    glueAssignment X a U₁ U₂ S₁ S₂ v = S₂.val ⟨v.val, hv⟩ := by
  classical
  by_cases h : v.val ∈ U₁
  · rw [glueAssignment_left X a U₁ U₂ S₁ S₂ v h]
    exact congrFun hc ⟨v.val, Finset.mem_inter.mpr ⟨h, hv⟩⟩
  · simp [glueAssignment, h]

/-- Compatible actual configurations glue to an actual configuration, not merely a bound. -/
def glueConfiguration (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (S₁ : LeftConfiguration X a U₁) (S₂ : RightConfiguration X a U₂)
    (hc : leftBoundary X a U₁ U₂ S₁ = rightBoundary X a U₁ U₂ S₂) :
    UnionConfiguration X a U₁ U₂ := by
  refine ⟨glueAssignment X a U₁ U₂ S₁ S₂, ⟨?_, ?_⟩⟩
  · intro v
    rcases Finset.mem_union.mp v.property with hv | hv
    · rw [glueAssignment_left X a U₁ U₂ S₁ S₂ v hv]
      exact S₁.property.1 _
    · rw [glueAssignment_right X a U₁ U₂ S₁ S₂ hc v hv]
      exact S₂.property.1 _
  · intro u v huv i hi hj
    change G₁.Adj u.val v.val ∨ G₂.Adj u.val v.val at huv
    change i ∈ glueAssignment X a U₁ U₂ S₁ S₂ u at hi
    change X.transport u.val v.val i ∈ glueAssignment X a U₁ U₂ S₁ S₂ v at hj
    rcases huv with huv | huv
    · obtain ⟨hu, hv⟩ := hU₁ u.val v.val huv
      rw [glueAssignment_left X a U₁ U₂ S₁ S₂ u hu] at hi
      rw [glueAssignment_left X a U₁ U₂ S₁ S₂ v hv] at hj
      exact S₁.property.2 ⟨u.val, hu⟩ ⟨v.val, hv⟩ huv i hi hj
    · obtain ⟨hu, hv⟩ := hU₂ u.val v.val huv
      rw [glueAssignment_right X a U₁ U₂ S₁ S₂ hc u hu] at hi
      rw [glueAssignment_right X a U₁ U₂ S₁ S₂ hc v hv] at hj
      exact S₂.property.2 ⟨u.val, hu⟩ ⟨v.val, hv⟩ huv i hi hj

/-- Exact fibre product over the common assignment. No seam-size hypothesis is needed. -/
def configurationPullbackEquiv
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂) :
    UnionConfiguration X a U₁ U₂ ≃
      {p : LeftConfiguration X a U₁ × RightConfiguration X a U₂ //
        leftBoundary X a U₁ U₂ p.1 = rightBoundary X a U₁ U₂ p.2} where
  toFun S := ⟨(leftPart X a U₁ U₂ S, rightPart X a U₁ U₂ S), rfl⟩
  invFun p := glueConfiguration X a U₁ U₂ hU₁ hU₂ p.val.1 p.val.2 p.property
  left_inv S := by
    apply Subtype.ext
    funext v
    classical
    by_cases h : v.val ∈ U₁
    · simp [glueConfiguration, glueAssignment, leftPart, h]
    · simp [glueConfiguration, glueAssignment, rightPart, h]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      funext v
      change glueAssignment X a U₁ U₂ p.val.1 p.val.2
        ⟨v.val, Finset.mem_union_left U₂ v.property⟩ = p.val.1.val v
      exact glueAssignment_left X a U₁ U₂ p.val.1 p.val.2
        ⟨v.val, Finset.mem_union_left U₂ v.property⟩ v.property
    · apply Subtype.ext
      funext v
      change glueAssignment X a U₁ U₂ p.val.1 p.val.2
        ⟨v.val, Finset.mem_union_right U₁ v.property⟩ = p.val.2.val v
      exact glueAssignment_right X a U₁ U₂ p.val.1 p.val.2 p.property
        ⟨v.val, Finset.mem_union_right U₁ v.property⟩ v.property

/-- Full dependent-sum version, with one copy of each compatible pair. -/
def configurationFibreEquiv
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂) :
    UnionConfiguration X a U₁ U₂ ≃
      Σ b : SeamAssignment U₁ U₂ M,
        {S : LeftConfiguration X a U₁ // leftBoundary X a U₁ U₂ S = b} ×
        {S : RightConfiguration X a U₂ // rightBoundary X a U₁ U₂ S = b} :=
  (configurationPullbackEquiv X a U₁ U₂ hU₁ hU₂).trans
    (matchingPairEquiv (leftBoundary X a U₁ U₂) (rightBoundary X a U₁ U₂))

omit [Fintype V] in
/-- G2: the actual union coefficient is exactly the sum of actual fibre products. -/
theorem coefficient_glue
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂) :
    coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => a v.val) =
      ∑ b : SeamAssignment U₁ U₂ M,
        Fintype.card {S : LeftConfiguration X a U₁ // leftBoundary X a U₁ U₂ S = b} *
        Fintype.card {S : RightConfiguration X a U₂ // rightBoundary X a U₁ U₂ S = b} := by
  classical
  change Fintype.card (UnionConfiguration X a U₁ U₂) = _
  rw [Fintype.card_congr (configurationFibreEquiv X a U₁ U₂ hU₁ hU₂)]
  simp only [Fintype.card_sigma, Fintype.card_prod]

omit [Fintype V] in
/-- Retain any condition on the left piece, including a root pin or an actual-edge pin. -/
theorem coefficient_glue_with_left_predicate
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (P : LeftConfiguration X a U₁ → Prop) :
    Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (leftPart X a U₁ U₂ S)} =
      ∑ b : SeamAssignment U₁ U₂ M,
        Fintype.card {S : {T : LeftConfiguration X a U₁ // P T} //
          leftBoundary X a U₁ U₂ S.val = b} *
        Fintype.card {S : RightConfiguration X a U₂ // rightBoundary X a U₁ U₂ S = b} := by
  classical
  let e := configurationPullbackEquiv X a U₁ U₂ hU₁ hU₂
  let e₁ := predicateEquiv e (fun p => P p.val.1)
  let e₂ := matchingPairPredicateEquiv (leftBoundary X a U₁ U₂)
    (rightBoundary X a U₁ U₂) P
  change Fintype.card {S : UnionConfiguration X a U₁ U₂ // P (e S).val.1} = _
  let e₃ := matchingPairEquiv (fun S : {T : LeftConfiguration X a U₁ // P T} =>
    leftBoundary X a U₁ U₂ S.val) (rightBoundary X a U₁ U₂)
  rw [Fintype.card_congr ((e₁.trans e₂).trans e₃), Fintype.card_sigma]
  simp only [Fintype.card_prod]

omit [Fintype V] in
/-- An impossible boundary occupation contributes exactly zero, even without feasibility. -/
theorem leftFibre_zero_of_wrong_card
    (b : SeamAssignment U₁ U₂ M) (v : (↑(U₁ ∩ U₂) : Set V))
    (hv : (b v).card ≠ a v.val) :
    Fintype.card {S : LeftConfiguration X a U₁ // leftBoundary X a U₁ U₂ S = b} = 0 := by
  classical
  letI : IsEmpty {S : LeftConfiguration X a U₁ // leftBoundary X a U₁ U₂ S = b} := ⟨by
    intro S
    apply hv
    rw [← S.property]
    exact S.val.property.1 ⟨v.val, (Finset.mem_inter.mp v.property).1⟩⟩
  exact Fintype.card_eq_zero

omit [Fintype V] in
/-- An impossible left seam edge also contributes zero; transports are not normalized away. -/
theorem leftFibre_zero_of_conflict
    (b : SeamAssignment U₁ U₂ M) (u v : (↑(U₁ ∩ U₂) : Set V))
    (huv : G₁.Adj u.val v.val) (i : Fin M)
    (hi : i ∈ b u) (hj : X.transport u.val v.val i ∈ b v) :
    Fintype.card {S : LeftConfiguration X a U₁ // leftBoundary X a U₁ U₂ S = b} = 0 := by
  classical
  letI : IsEmpty {S : LeftConfiguration X a U₁ // leftBoundary X a U₁ U₂ S = b} := ⟨by
    intro S
    have hi' := hi
    have hj' := hj
    rw [← S.property] at hi' hj'
    exact S.val.property.2
      ⟨u.val, (Finset.mem_inter.mp u.property).1⟩
      ⟨v.val, (Finset.mem_inter.mp v.property).1⟩ huv i hi' hj'⟩
  exact Fintype.card_eq_zero

end
end CoefficientwiseRigidity.Gluing

namespace CoefficientwiseRigidity.Gluing
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G G₁ G₂ : SimpleGraph V} {M : ℕ}

/-- Remove the harmless induced-universe wrapper without changing any count. -/
def univConfigurationEquiv (X : Cover G M) (a : V → ℕ) :
    Configuration X a ≃ PieceConfiguration X a Finset.univ G le_rfl where
  toFun S := ⟨fun v => S.val v.val,
    ⟨fun v => S.property.1 v.val, fun u v huv => S.property.2 u.val v.val huv⟩⟩
  invFun S := ⟨fun v => S.val ⟨v, Finset.mem_univ v⟩,
    ⟨fun v => S.property.1 _, fun u v huv => S.property.2 _ _ huv⟩⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

theorem coefficient_glue_univ (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (U₁ U₂ : Finset V) (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hU : U₁ ∪ U₂ = Finset.univ) :
    coefficient X a = ∑ b : SeamAssignment U₁ U₂ M,
      Fintype.card {S : LeftConfiguration X a U₁ // leftBoundary X a U₁ U₂ S = b} *
      Fintype.card {S : RightConfiguration X a U₂ // rightBoundary X a U₁ U₂ S = b} := by
  have h := coefficient_glue X a U₁ U₂ hU₁ hU₂
  have he : coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl)
      (fun v => a v.val) = coefficient X a := by
    rw [hU]
    exact (Fintype.card_congr (univConfigurationEquiv X a)).symm
  exact he.symm.trans h

/-- The reduced coefficient uses the same graph, with exactly M-2 labels and a-1. -/
theorem reserve_glue_univ (a : V → ℕ) (U₁ U₂ : Finset V)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hU : U₁ ∪ U₂ = Finset.univ) :
    reserve (G₁ ⊔ G₂) M a =
      ∑ b : SeamAssignment U₁ U₂ (M - 2),
        Fintype.card {S : LeftConfiguration (trivialCover (G₁ ⊔ G₂) (M - 2))
          (fun v => a v - 1) U₁ //
          leftBoundary (trivialCover (G₁ ⊔ G₂) (M - 2)) (fun v => a v - 1) U₁ U₂ S = b} *
        Fintype.card {S : RightConfiguration (trivialCover (G₁ ⊔ G₂) (M - 2))
          (fun v => a v - 1) U₂ //
          rightBoundary (trivialCover (G₁ ⊔ G₂) (M - 2)) (fun v => a v - 1) U₁ U₂ S = b} := by
  exact coefficient_glue_univ (trivialCover (G₁ ⊔ G₂) (M - 2))
    (fun v => a v - 1) U₁ U₂ hU₁ hU₂ hU

end
end CoefficientwiseRigidity.Gluing
