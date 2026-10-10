import CoefficientwiseRigidity.SaturationRanks
import CoefficientwiseRigidity.SaturationExpansion
import CoefficientwiseRigidity.RootIntersections

/-! C4 for the original graph coefficients, with an explicit proper-subset surplus. -/
namespace CoefficientwiseRigidity.Saturation
open Finset Structure Intersections
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

abbrev rowRanks (b : Bipartition G) (a : V → ℕ) : LeftRows b → ℕ := fun u => a u.val
abbrev rowCaps (b : Bipartition G) (M : ℕ) (a : V → ℕ) : LeftRows b → ℕ :=
  fun u => capacity b M a u.val

theorem coefficient_eq_capped_sum (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : ∀ v, a v ≤ M) :
    (coefficient X a : ℚ) = sumSet (columnRanks M a) (columnSet b)
      (fun Q => ∏ u : LeftRows b,
        capped (a u.val) (capacity b M a u.val) (ranks (graphRows b) (coverGains b X) Q u))
      (fun _ => ∅) := by
  rw [coefficient_eq_intersection_sum b X a ha]
  apply sumSet_congr_valid
  intro Q hQ
  apply Finset.prod_congr rfl
  intro u _
  exact (capped_eq_choose _ (rank_le_capacity b a ha (coverGains b X) _ Q hQ u)).symm

theorem saturated_coefficient_eq_threshold_sum (b : Bipartition G) (X : Cover G M)
    (a : V → ℕ) (ha : Feasible G M a) :
    (coefficient X (occupation b M a) : ℚ) = sumSet (columnRanks M a) (columnSet b)
      (fun Q => mixedCost (rowRanks b a) (rowCaps b M a) univ
        (ranks (graphRows b) (coverGains b X) Q)) (fun _ => ∅) := by
  rw [coefficient_eq_intersection_sum b X _ (occupation_feasible b ha).1]
  rw [sumSet_congr_ranks (columnRanks M (occupation b M a)) (columnRanks M a)
    (columnSet b) (fun v hv => by simp only [columnRanks,occupation_column b a hv])]
  apply sumSet_congr_valid
  intro Q hQ
  rw [mixedCost_univ]
  apply Finset.prod_congr rfl
  intro u _
  simp only [occupation,u.property,if_true]
  exact (threshold_eq_choose (rank_le_capacity b a ha.1 (coverGains b X) _ Q hQ u)).symm

theorem deficit_eq_capped_coneDeficit (b : Bipartition G) (X : Cover G M)
    (a : V → ℕ) (ha : ∀ v, a v ≤ M) :
    (deficit X a : ℚ) = coneDeficit b (coverGains b X) (columnRanks M a)
      (fun d => ∏ u, capped (a u.val) (capacity b M a u.val) (d u)) := by
  simp only [deficit,Int.cast_sub,Int.cast_natCast,ordinary]
  rw [coefficient_eq_capped_sum b X a ha,coefficient_eq_capped_sum b (trivialCover G M) a ha]
  rfl

theorem saturated_deficit_eq_coneDeficit (b : Bipartition G) (X : Cover G M)
    (a : V → ℕ) (ha : Feasible G M a) :
    (deficit X (occupation b M a) : ℚ) = coneDeficit b (coverGains b X) (columnRanks M a)
      (mixedCost (rowRanks b a) (rowCaps b M a) univ) := by
  simp only [deficit,Int.cast_sub,Int.cast_natCast,ordinary]
  rw [saturated_coefficient_eq_threshold_sum b X a ha,
    saturated_coefficient_eq_threshold_sum b (trivialCover G M) a ha]
  rfl

/-- Integer multiplier; the product over an empty side equals one. -/
def multiplier (b : Bipartition G) (M : ℕ) (a : V → ℕ) : ℕ :=
  ∏ u : LeftRows b, (capacity b M a u.val - 1).choose (a u.val - 1)

omit [DecidableEq V] in
theorem multiplier_cast (b : Bipartition G) (a : V → ℕ) :
    (multiplier b M a : ℚ) = weight (rowRanks b a) (rowCaps b M a) univ := by
  simp [multiplier,weight,pascalWeight,rowRanks,rowCaps]

omit [DecidableEq V] in
theorem multiplier_pos (b : Bipartition G) {a : V → ℕ} (ha : Feasible G M a) :
    0 < multiplier b M a := by
  unfold multiplier
  apply Finset.prod_pos
  intro u _
  exact Nat.choose_pos (Nat.sub_le_sub_right (le_capacity b ha u.val) 1)

def surplus (b : Bipartition G) (X : Cover G M) (a : V → ℕ) : ℚ :=
  ∑ T ∈ (univ : Finset (Finset (LeftRows b))).erase univ,
    weight (rowRanks b a) (rowCaps b M a) T *
      coneDeficit b (coverGains b X) (columnRanks M a) (mixedCost (rowRanks b a) (rowCaps b M a) T)

theorem saturation_identity (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : Feasible G M a) (hp : Positive a) :
    (deficit X a : ℚ) = (multiplier b M a : ℚ) * deficit X (occupation b M a) + surplus b X a := by
  rw [deficit_eq_capped_coneDeficit b X a ha.1]
  rw [coneDeficit_expansion b (coverGains b X) (columnRanks M a) (rowRanks b a) (rowCaps b M a)
    (fun u => hp u.val) (fun u => le_capacity b ha u.val)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (univ : Finset (LeftRows b)))]
  rw [← saturated_deficit_eq_coneDeficit b X a ha,← multiplier_cast]
  exact add_comm _ _

theorem surplus_nonneg (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) : 0 ≤ surplus b X a := by
  apply Finset.sum_nonneg
  intro T _
  exact mul_nonneg (weight_nonneg _ _ _) (coneDeficit_nonneg b hg _ _ (mixedCost_cone _ _ _))

/-- The signed original deficit dominates the saturated deficit with its positive multiplier. -/
theorem saturation_le (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a) (hp : Positive a) :
    (multiplier b M a : ℤ) * deficit X (occupation b M a) ≤ deficit X a := by
  have h := saturation_identity b X a ha hp
  have hn := surplus_nonneg b hg X a
  have hq : (multiplier b M a : ℚ) * (deficit X (occupation b M a) : ℚ) ≤ (deficit X a : ℚ) := by
    linarith
  exact_mod_cast hq

theorem saturated_deficit_nonneg (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) : 0 ≤ deficit X (occupation b M a) := by
  unfold deficit
  exact sub_nonneg.mpr (Int.ofNat_le.mpr (CoefficientwiseRigidity.coefficient_le_of_chordalBipartite X _ hg))

theorem saturated_deficit_zero (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a) (hp : Positive a)
    (hz : deficit X a = 0) : deficit X (occupation b M a) = 0 := by
  have h := saturation_le b hg X a ha hp
  have hn := saturated_deficit_nonneg b hg X a
  have hc : (0 : ℤ) < multiplier b M a := Int.ofNat_pos.mpr (multiplier_pos b ha)
  rw [hz] at h
  nlinarith

/-- The paper's orientation: saturate the original right side, preserving left ranks. -/
def rightOccupation (b : Bipartition G) (M : ℕ) (a : V → ℕ) : V → ℕ :=
  occupation b.flip M a

omit [DecidableEq V] in
theorem rightOccupation_left (b : Bipartition G) (a : V → ℕ) {u : V}
    (hu : b.side u = true) : rightOccupation b M a u = a u := by
  simp [rightOccupation,occupation,Bipartition.flip,hu]

omit [DecidableEq V] in
theorem rightOccupation_right (b : Bipartition G) (a : V → ℕ) {v : V}
    (hv : b.side v = false) :
    rightOccupation b M a v = M - (univ.filter (G.Adj v)).sup a := by
  have hv' : b.flip.side v = true := by simp [Bipartition.flip,hv]
  simp only [rightOccupation,occupation,hv',if_true,capacity,
    rowNeighborhood_eq_neighbors b.flip hv']

theorem right_saturation_le (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a) (hp : Positive a) :
    (multiplier b.flip M a : ℤ) * deficit X (rightOccupation b M a) ≤ deficit X a :=
  saturation_le b.flip hg X a ha hp

theorem right_saturated_deficit_zero (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a) (hp : Positive a)
    (hz : deficit X a = 0) : deficit X (rightOccupation b M a) = 0 :=
  saturated_deficit_zero b.flip hg X a ha hp hz

end
end CoefficientwiseRigidity.Saturation
