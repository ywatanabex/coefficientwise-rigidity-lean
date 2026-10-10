import CoefficientwiseRigidity.Elimination

/-!
Exact bridge from the paper's independent-set coefficients to the actual
gain-list network. Bipartiteness and feasible ranks are explicit assumptions.
No graph comparison is assumed in this construction.
-/
namespace CoefficientwiseRigidity
open Kernel Network Finset
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ} {a : V → ℕ}

def StateLegal (X : Cover G M) (S : State M a) : Prop :=
  ∀ u v, G.Adj u v → ∀ i ∈ (S u).val, X.transport u v i ∉ (S v).val

def configurationStateEquiv (X : Cover G M) (a : V → ℕ) :
    Configuration X a ≃ {S : State M a // StateLegal X S} where
  toFun S := ⟨fun v => ⟨S.val v, S.property.1 v⟩, S.property.2⟩
  invFun S := ⟨fun v => (S.val v).val, ⟨fun v => (S.val v).property, S.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coefficient_eq_state_sum (X : Cover G M) (a : V → ℕ) :
    (coefficient X a : ℚ) = ∑ S : State M a, if StateLegal X S then 1 else 0 := by
  classical
  unfold coefficient
  rw [Fintype.card_congr (configurationStateEquiv X a), Fintype.card_subtype, Finset.card_filter]
  push_cast
  rfl

def inclusionRanks (b : Bipartition G) (M : ℕ) (a : V → ℕ) (v : V) : ℕ :=
  if b.side v then a v else M - a v

def sliceComplementEquiv {k : ℕ} (hk : k ≤ M) : Slice M k ≃ Slice M (M - k) where
  toFun := complementSlice
  invFun B := ⟨B.valᶜ, by
    rw [Finset.card_compl, Fintype.card_fin, B.property]
    omega⟩
  left_inv A := by apply Subtype.ext; exact compl_compl _
  right_inv B := by apply Subtype.ext; exact compl_compl _

def sideSliceEquiv {k : ℕ} (hk : k ≤ M) (side : Bool) :
    Slice M k ≃ Slice M (if side then k else M - k) :=
  match side with
  | true => Equiv.refl _
  | false => sliceComplementEquiv hk

def inclusionStateEquiv (b : Bipartition G) (ha : ∀ v, a v ≤ M) :
    State M a ≃ State M (inclusionRanks b M a) :=
  Equiv.piCongrRight fun v => sideSliceEquiv (ha v) (b.side v)

theorem sideSliceEquiv_val {k : ℕ} (hk : k ≤ M) (side : Bool) (S : Slice M k) :
    (sideSliceEquiv hk side S).val = if side then S.val else S.valᶜ := by
  cases side <;> rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem inclusionState_val (b : Bipartition G) (ha : ∀ v, a v ≤ M)
    (S : State M a) (v : V) :
    (inclusionStateEquiv b ha S v).val = if b.side v then (S v).val else (S v).valᶜ := by
  exact sideSliceEquiv_val (ha v) (b.side v) (S v)

/-- Every undirected edge occurs once, from the true side to the false side. -/
abbrev LeftEdge (b : Bipartition G) := {uv : V × V // G.Adj uv.1 uv.2 ∧ b.side uv.1 = true}

omit [Fintype V] [DecidableEq V] in
theorem leftEdge_right (b : Bipartition G) (e : LeftEdge b) : b.side e.val.2 = false := by
  have h := b.opposite e.property.1
  rw [e.property.2] at h
  cases he : b.side e.val.2 <;> simp_all

omit [Fintype V] [DecidableEq V] in
theorem leftEdge_ranks (b : Bipartition G) (ha : Feasible G M a) (e : LeftEdge b) :
    inclusionRanks b M a e.val.1 ≤ inclusionRanks b M a e.val.2 := by
  have h := ha.2 _ _ e.property.1
  simp only [inclusionRanks, e.property.2, leftEdge_right b e, Bool.false_eq_true, if_true, if_false]
  omega

def inclusionEntry (b : Bipartition G) (X : Cover G M) (e : LeftEdge b) :
    GainEntry M (inclusionRanks b M a e.val.1) (inclusionRanks b M a e.val.2) where
  profile z := (z.choose (overlapRank M (inclusionRanks b M a e.val.1) (inclusionRanks b M a e.val.2)) : ℚ)
  cone := newtonCone_choose _ _
  gain := (X.transport e.val.1 e.val.2).symm

def inclusionEdge (b : Bipartition G) (X : Cover G M) (e : LeftEdge b) : Edge M (inclusionRanks b M a) :=
  ⟨e.val.1, e.val.2, e.property.1.ne, [inclusionEntry b X e]⟩

def inclusionNetwork (b : Bipartition G) (X : Cover G M) (a : V → ℕ) : Net M (inclusionRanks b M a) := by
  classical
  exact ⟨1, zero_le_one, (Finset.univ : Finset (LeftEdge b)).toList.map (inclusionEdge b X)⟩

omit [Fintype V] [DecidableEq V] in
theorem inclusionEdge_value (b : Bipartition G) (X : Cover G M) (ha : Feasible G M a)
    (e : LeftEdge b) (S : State M a) :
    (inclusionEdge b X e).eval false (inclusionStateEquiv b ha.1 S) =
      if ∀ i ∈ (S e.val.1).val, X.transport e.val.1 e.val.2 i ∉ (S e.val.2).val then 1 else 0 := by
  classical
  simp only [inclusionEdge, Edge.eval, kernel, Bool.false_eq_true, if_false, listValue_cons,
    listValue_nil, add_zero, GainEntry.value, inclusionEntry]
  rw [top_basis_inclusion _ _ (leftEdge_ranks b ha e)]
  congr 1
  simp [permuteSlice, inclusionState_val, e.property.2, leftEdge_right b e, Finset.subset_iff]

omit [Fintype V] [DecidableEq V] in
theorem stateLegal_iff_leftEdges (b : Bipartition G) (X : Cover G M) (S : State M a) :
    StateLegal X S ↔ ∀ e : LeftEdge b,
      ∀ i ∈ (S e.val.1).val, X.transport e.val.1 e.val.2 i ∉ (S e.val.2).val := by
  constructor
  · intro h e
    exact h _ _ e.property.1
  · intro h u v huv i hi hj
    cases hsu : b.side u with
    | true => exact h ⟨(u,v),huv,hsu⟩ i hi hj
    | false =>
      have hsv : b.side v = true := by
        have hne := b.opposite huv
        cases hv : b.side v <;> simp_all
      have hrev := X.reverse huv
      have hbad := h ⟨(v,u),G.symm huv,hsv⟩ (X.transport u v i) hj
      rw [hrev, Equiv.symm_apply_apply] at hbad
      exact hbad hi

omit [DecidableEq V] in
theorem inclusionNetwork_weight (b : Bipartition G) (X : Cover G M) (ha : Feasible G M a)
    (S : State M a) :
    weight (inclusionNetwork b X a).edges false (inclusionStateEquiv b ha.1 S) =
      if StateLegal X S then 1 else 0 := by
  classical
  simp only [weight, inclusionNetwork, List.map_map, Function.comp_def]
  rw [Finset.prod_to_list]
  simp_rw [inclusionEdge_value b X ha, Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one, ← stateLegal_iff_leftEdges b X S]

/-- Exact coefficient normalization, not an inequality or a scaled surrogate. -/
theorem inclusionNetwork_value (b : Bipartition G) (X : Cover G M) (ha : Feasible G M a) :
    (inclusionNetwork b X a).value false = (coefficient X a : ℚ) := by
  classical
  rw [coefficient_eq_state_sum]
  change 1 * (∑ A, weight (inclusionNetwork b X a).edges false A) = _
  rw [one_mul]
  symm
  apply Fintype.sum_equiv (inclusionStateEquiv b ha.1)
  intro S
  exact (inclusionNetwork_weight b X ha S).symm

omit [Fintype V] [DecidableEq V] in
theorem inclusionEntry_ordinary (b : Bipartition G) (X : Cover G M) (e : LeftEdge b)
    (A : Slice M (inclusionRanks b M a e.val.1)) (B : Slice M (inclusionRanks b M a e.val.2)) :
    (inclusionEntry b X e).ordinary A B = (inclusionEntry b (trivialCover G M) e).value A B := by
  simp [GainEntry.ordinary, GainEntry.value, inclusionEntry, trivialCover]

theorem inclusionNetwork_ordinary (b : Bipartition G) (X : Cover G M) (ha : Feasible G M a) :
    (inclusionNetwork b X a).value true = (ordinary G M a : ℚ) := by
  unfold ordinary
  rw [← inclusionNetwork_value b (trivialCover G M) ha]
  unfold Net.value
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  simp only [weight, inclusionNetwork, List.map_map, Function.comp_def]
  congr 2
  funext e
  simp [inclusionEdge, Edge.eval, kernel, inclusionEntry_ordinary]

/-- A verified elimination derivation for this concrete graph network suffices.
The structural treewidth-to-derivation theorem is NOT a premise hidden in its definition. -/
theorem coefficient_le_of_eliminates (b : Bipartition G) (X : Cover G M) (ha : Feasible G M a)
    (h : Eliminates M (inclusionNetwork b X a)) : coefficient X a ≤ ordinary G M a := by
  have hle := h.comparison
  rw [inclusionNetwork_value b X ha, inclusionNetwork_ordinary b X ha] at hle
  exact_mod_cast hle

end
end CoefficientwiseRigidity
