import CoefficientwiseRigidity.Gauge
import Mathlib.Order.Interval.Finset.Fin

/-! F2, infeasible zero counts, and positivity of the original reduced reserve. -/
namespace CoefficientwiseRigidity
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem feasible_of_admissible (X : Cover G M) (a : V → ℕ)
    {S : Assignment V M} (hS : Admissible X a S) : Feasible G M a := by
  constructor
  · intro v
    rw [← hS.1 v]
    simpa using (S v).card_le_univ
  · intro u v huv
    have hd : Disjoint ((S u).map (X.transport u v).toEmbedding) (S v) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      obtain ⟨j, hj', rfl⟩ := Finset.mem_map.mp hi
      exact hS.2 u v huv j hj' hj
    have hc : (((S u).map (X.transport u v).toEmbedding) ∪ S v).card ≤ M := by
      simpa using (((S u).map (X.transport u v).toEmbedding) ∪ S v).card_le_univ
    rw [Finset.card_union_of_disjoint hd, Finset.card_map, hS.1 u, hS.1 v] at hc
    exact hc

theorem coefficient_zero_of_not_feasible (X : Cover G M) (a : V → ℕ)
    (h : ¬ Feasible G M a) : coefficient X a = 0 := by
  haveI : IsEmpty (Configuration X a) := ⟨fun S => h (feasible_of_admissible X a S.property)⟩
  exact Fintype.card_eq_zero

def initialSegment (M k : ℕ) : Finset (Fin M) := Finset.univ.filter (fun i => i.val < k)

@[simp] theorem mem_prefix (M k : ℕ) (i : Fin M) : i ∈ initialSegment M k ↔ i.val < k := by
  simp [initialSegment]

theorem card_prefix (M k : ℕ) (hk : k ≤ M) : (initialSegment M k).card = k := by
  by_cases h : k < M
  · have he : initialSegment M k = Finset.Iio (⟨k, h⟩ : Fin M) := by
      ext i
      simp [Fin.lt_def]
    rw [he, Fin.card_Iio]
  · have he : k = M := by omega
    subst k
    have hp : initialSegment M M = Finset.univ := by ext i; simp [i.isLt]
    simp [hp]

def nestedAssignment (b : Bipartition G) (M : ℕ) (a : V → ℕ) : Assignment V M :=
  fun v => if b.side v then initialSegment M (a v) else Finset.univ \ initialSegment M (M - a v)

omit [Fintype V] [DecidableEq V] in
theorem nestedAssignment_admissible (b : Bipartition G) (a : V → ℕ)
    (ha : Feasible G M a) : Admissible (trivialCover G M) a (nestedAssignment b M a) := by
  constructor
  · intro v
    unfold nestedAssignment
    split_ifs
    · exact card_prefix M (a v) (ha.1 v)
    · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, card_prefix M (M - a v) (Nat.sub_le _ _)]
      have := ha.1 v
      omega
  · intro u v huv i hi hj
    have he := ha.2 u v huv
    have hs := b.opposite huv
    change i ∈ nestedAssignment b M a v at hj
    cases hsu : b.side u <;> cases hsv : b.side v <;>
      simp_all [nestedAssignment] <;> omega

theorem ordinary_pos_iff_feasible (b : Bipartition G) (a : V → ℕ) :
    0 < ordinary G M a ↔ Feasible G M a := by
  change 0 < Fintype.card (Configuration (trivialCover G M) a) ↔ _
  rw [Fintype.card_pos_iff]
  constructor
  · rintro ⟨S⟩
    exact feasible_of_admissible _ _ S.property
  · intro ha
    exact ⟨⟨nestedAssignment b M a, nestedAssignment_admissible b a ha⟩⟩

/-- Positivity includes M = 2; full occupations at isolated vertices are excluded. -/
theorem reserve_pos (b : Bipartition G) (a : V → ℕ) (hM : 2 ≤ M)
    (ha : Feasible G M a) (hp : Positive a) (hi : ∀ v, a v ≤ M - 1) :
    0 < reserve G M a := by
  apply (ordinary_pos_iff_feasible b (fun v => a v - 1)).mpr
  constructor
  · intro v
    dsimp only
    have := hp v
    have := hi v
    omega
  · intro u v huv
    dsimp only
    have := hp u
    have := hp v
    have := ha.2 u v huv
    omega

omit [Fintype V] [DecidableEq V] in
theorem interior_of_incident (a : V → ℕ) (ha : Feasible G M a) (hp : Positive a)
    (he : ∀ v, ∃ u, G.Adj v u) : ∀ v, a v ≤ M - 1 := by
  intro v
  obtain ⟨u, hu⟩ := he v
  have := ha.2 v u hu
  have := hp u
  omega

end CoefficientwiseRigidity
