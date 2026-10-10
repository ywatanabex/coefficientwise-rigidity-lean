import CoefficientwiseRigidity.NetworkQuantitativeInduction
import CoefficientwiseRigidity.CoefficientFlatness

/-!
The actual independent-set reserve equals the inclusion-network difference
reserve. W3 consequently supplies the original sharp 2R coefficient bound.
-/
namespace CoefficientwiseRigidity
open Kernel Network Finset
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ} {a : V → ℕ}

omit [Fintype V] [DecidableEq V] in
theorem inclusionRanks_interior (b : Bipartition G)
    (ha : ∀ v, 0 < a v ∧ a v < M + 2) :
    ∀ v, 0 < inclusionRanks b (M + 2) a v ∧ inclusionRanks b (M + 2) a v < M + 2 := by
  intro v
  have := ha v
  unfold inclusionRanks
  split <;> omega

omit [Fintype V] [DecidableEq V] in
theorem inclusionRanks_reduce (b : Bipartition G)
    (ha : ∀ v, 0 < a v ∧ a v < M + 2) (v : V) :
    inclusionRanks b (M + 2) a v = inclusionRanks b M (fun w => a w - 1) v + 1 := by
  have := ha v
  unfold inclusionRanks
  split <;> dsimp only <;> omega

omit [DecidableEq V] in
theorem inclusionNetwork_simple (b : Bipartition G) (X : Cover G M) (a : V → ℕ) :
    (inclusionNetwork b X a).Simple := by
  change (((univ : Finset (LeftEdge b)).toList.map (inclusionEdge b X)).map Edge.key).Nodup
  rw [List.map_map]
  apply List.Nodup.map _ (Finset.nodup_toList _)
  intro e f h
  change s(e.val.1,e.val.2) = s(f.val.1,f.val.2) at h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have hh := e.property.2
    rw [h.1, leftEdge_right b f] at hh
    cases hh

omit [Fintype V] [DecidableEq V] in
theorem inclusionEntry_nonconstant (b : Bipartition G) (X : Cover G (M + 2))
    (ha : ∀ v, 0 < a v ∧ a v < M + 2) (e : LeftEdge b) :
    (inclusionEntry (a := a) b X e).Nonconstant := by
  have hl := inclusionRanks_interior b ha e.val.1
  have hr := inclusionRanks_interior b ha e.val.2
  have hpos : 0 < overlapRank (M + 2) (inclusionRanks b (M + 2) a e.val.1)
      (inclusionRanks b (M + 2) a e.val.2) := by
    unfold overlapRank overlapShift
    omega
  refine ⟨_,le_rfl,?_⟩
  change (Nat.choose _ _ : ℚ) ≠ (Nat.choose 0 _ : ℚ)
  rw [Nat.choose_self, Nat.choose_eq_zero_of_lt hpos]
  norm_num

omit [DecidableEq V] in
theorem inclusionNetwork_rigid (b : Bipartition G) (X : Cover G (M + 2))
    (ha : ∀ v, 0 < a v ∧ a v < M + 2) :
    (inclusionNetwork b X a).Rigid ⊤ := by
  intro f hf
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hf
  exact ⟨inclusionEntry b X e,rfl,inclusionEntry_nonconstant b X ha e,Subgroup.mem_top _⟩

/-- No extra binomial multiplier: this is exactly the original reserve. -/
theorem inclusionNetwork_reserveValue (b : Bipartition G) (X : Cover G (M + 2))
    (hf : Feasible G (M + 2) a) (ha : ∀ v, 0 < a v ∧ a v < M + 2) :
    (inclusionNetwork b X a).reserveValue = (reserve G (M + 2) a : ℚ) := by
  let a' := fun v => a v - 1
  have hf' : Feasible G M a' := by
    constructor
    · intro v
      dsimp [a']
      have := ha v
      omega
    · intro u v huv
      dsimp [a']
      have := hf.2 u v huv
      have := (ha u).1
      have := (ha v).1
      omega
  have hp (v : V) : inclusionRanks b M a' v ≤ M := by
    unfold inclusionRanks
    split
    · exact hf'.1 v
    · exact Nat.sub_le _ _
  have hrank (e : LeftEdge b) :
      overlapRank (M + 2) (inclusionRanks b (M + 2) a e.val.1)
        (inclusionRanks b (M + 2) a e.val.2) =
      overlapRank M (inclusionRanks b M a' e.val.1) (inclusionRanks b M a' e.val.2) + 1 := by
    rw [inclusionRanks_reduce b ha e.val.1, inclusionRanks_reduce b ha e.val.2]
    exact overlapRank_reduce (hp e.val.1) (hp e.val.2)
  have hpred : (fun v => inclusionRanks b (M + 2) a v - 1) = inclusionRanks b M a' := by
    funext v
    rw [inclusionRanks_reduce b ha v]
    exact Nat.add_sub_cancel _ _
  change _ = (ordinary G M a' : ℚ)
  rw [← inclusionNetwork_ordinary b (trivialCover G M) hf']
  unfold Net.reserveValue Net.value
  rw [hpred]
  change 1 * _ = 1 * _
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  simp only [differenceWeight, weight, inclusionNetwork, List.map_map, Function.comp_def]
  congr 2
  funext e
  simp only [inclusionEdge, differenceKernel, Edge.eval, kernel, if_true, listOrdinary_cons,
    listOrdinary_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    GainEntry.ordinary, inclusionEntry, hrank, delta_choose]

theorem coefficient_two_of_interior_treewidth (b : Bipartition G) (X : Cover G (M + 2))
    (ha : ∀ v, 0 < a v ∧ a v < M + 2) (hf : Feasible G (M + 2) a)
    (hw : TreewidthAtMostTwo G) (hn : ¬ Flat X) :
    coefficient X a + 2 * reserve G (M + 2) a ≤ ordinary G (M + 2) a := by
  have h := (inclusionNetwork b X a).two_of_treewidth (inclusionRanks_interior b ha) ⊤
    (inclusionNetwork_rigid b X ha) (inclusionNetwork_simple b X a)
    (by rwa [inclusionNetwork_graph]) (fun h => hn ((inclusionNetwork_flat_iff b X a).mp h))
  rw [inclusionNetwork_reserveValue b X hf ha, inclusionNetwork_value b X hf,
    inclusionNetwork_ordinary b X hf] at h
  have h' : (coefficient X a : ℚ) + 2 * reserve G (M + 2) a ≤ ordinary G (M + 2) a := by linarith
  exact_mod_cast h'

omit [Fintype V] [DecidableEq V] in
theorem connected_has_neighbor (hc : G.Connected) (he : ∃ u v, G.Adj u v) :
    ∀ v, ∃ u, G.Adj v u := by
  obtain ⟨s,t,hst⟩ := he
  intro v
  rcases Structure.reachable_first (hc v s) with rfl | h
  · exact ⟨t,hst⟩
  · exact h

/-- An inhabitant of the unchanged paper proposition MainBTwo. -/
theorem mainBTwo (b : Bipartition G) : MainBTwo G := by
  intro M hM X a hc he hw hp hf hn
  have hi := interior_of_incident a hf hp (connected_has_neighbor hc he)
  have hpos := reserve_pos b a hM hf hp hi
  refine ⟨?_,hpos⟩
  obtain ⟨m,rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  apply coefficient_two_of_interior_treewidth b X _ hf hw hn
  intro v
  exact ⟨hp v, by have := hi v; omega⟩

omit [DecidableEq V] in
theorem inclusionNetwork_rigid_of_gains (b : Bipartition G) (X : Cover G (M + 2))
    (ha : ∀ v, 0 < a v ∧ a v < M + 2) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hg : ∀ u v, G.Adj u v → X.transport u v ∈ Γ) :
    (inclusionNetwork b X a).Rigid Γ := by
  intro f hf
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hf
  exact ⟨inclusionEntry b X e,rfl,inclusionEntry_nonconstant b X ha e,
    Γ.inv_mem (hg e.val.1 e.val.2 e.property.1)⟩

theorem coefficient_kappa_of_interior_treewidth (b : Bipartition G) (X : Cover G (M + 2))
    (ha : ∀ v, 0 < a v ∧ a v < M + 2) (hf : Feasible G (M + 2) a)
    (hw : TreewidthAtMostTwo G) (hn : ¬ Flat X) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hg : ∀ u v, G.Adj u v → X.transport u v ∈ Γ) :
    (coefficient X a : ℚ) + kappa (M + 2) Γ * reserve G (M + 2) a ≤ ordinary G (M + 2) a := by
  have h := (inclusionNetwork b X a).kappa_of_treewidth (inclusionRanks_interior b ha) Γ
    (inclusionNetwork_rigid_of_gains b X ha Γ hg) (inclusionNetwork_simple b X a)
    (by rwa [inclusionNetwork_graph]) (fun h => hn ((inclusionNetwork_flat_iff b X a).mp h))
  rw [inclusionNetwork_reserveValue b X hf ha, inclusionNetwork_value b X hf,
    inclusionNetwork_ordinary b X hf] at h
  linarith

theorem coefficient_eq_iff_flat_of_interior_treewidth (b : Bipartition G)
    (X : Cover G (M + 2)) (ha : ∀ v, 0 < a v ∧ a v < M + 2)
    (hf : Feasible G (M + 2) a) (hw : TreewidthAtMostTwo G) :
    coefficient X a = ordinary G (M + 2) a ↔ Flat X := by
  have h := (inclusionNetwork b X a).value_eq_iff_flat_of_treewidth
    (inclusionRanks_interior b ha) ⊤ (inclusionNetwork_rigid b X ha) (by norm_num [inclusionNetwork])
    (inclusionNetwork_simple b X a) (by rwa [inclusionNetwork_graph])
  rw [inclusionNetwork_value b X hf, inclusionNetwork_ordinary b X hf,
    inclusionNetwork_flat_iff b X a] at h
  constructor
  · intro he
    apply h.mp
    exact_mod_cast he
  · intro hf
    have := h.mpr hf
    exact_mod_cast this

end
end CoefficientwiseRigidity
