import CoefficientwiseRigidity.StarReduction
import CoefficientwiseRigidity.StarChordal

/-! C4-to-C5: actual saturated coefficient, smaller chordal graph and full parallel-edge gauge. -/
namespace CoefficientwiseRigidity.Star
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem cover_chordalBipartite (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (hg : ChordalBipartite G) : ChordalBipartite (cover b u hu X).graph := by
  rw [cover_graph]
  exact chordalBipartite b u hu hg

def saturatedConfigurationEquiv (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a)
    (hmax : ∀ v, b.side v = true → a v ≤ a u) :
    Configuration X (Saturation.rightOccupation b M a) ≃
      (cover b u hu (gaugeCover X (starGauge X u))).Configuration
        (occupation u M (Saturation.rightOccupation b M a)) :=
  gaugedConfigurationEquiv b u hu X _
    (by rw [Saturation.rightOccupation_left b a hu]; exact ha.1 u)
    (saturated_tight b u hu a hmax)

theorem saturated_coefficient_eq (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a)
    (hmax : ∀ v, b.side v = true → a v ≤ a u) :
    coefficient X (Saturation.rightOccupation b M a) =
      (cover b u hu (gaugeCover X (starGauge X u))).coefficient
        (occupation u M (Saturation.rightOccupation b M a)) :=
  Fintype.card_congr (saturatedConfigurationEquiv b u hu X a ha hmax)

theorem saturated_ordinary_eq (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a)
    (hmax : ∀ v, b.side v = true → a v ≤ a u) :
    ordinary G M (Saturation.rightOccupation b M a) =
      (cover b u hu (gaugeCover X (starGauge X u))).ordinary.coefficient
        (occupation u M (Saturation.rightOccupation b M a)) :=
  ordinary_eq b u hu _ _
    (by rw [Saturation.rightOccupation_left b a hu]; exact ha.1 u)
    (saturated_tight b u hu a hmax)

omit [DecidableEq V] in
theorem saturated_feasible (b : Bipartition G) (u : V) (hu : b.side u = true)
    (a : V → ℕ) (ha : Feasible G M a)
    (hmax : ∀ v, b.side v = true → a v ≤ a u) :
    Feasible (graph G u) M (occupation u M (Saturation.rightOccupation b M a)) :=
  occupation_feasible b u (Saturation.occupation_feasible b.flip ha) (saturated_tight b u hu a hmax)

omit [DecidableEq V] in
theorem saturated_positive (b : Bipartition G) (u : V) (hu : b.side u = true)
    (a : V → ℕ) (ha : Feasible G M a) (hp : Positive a) (hne : ∃ v, G.Adj u v) :
    Positive (occupation (G := G) u M (Saturation.rightOccupation b M a)) := by
  apply occupation_positive (G := G) u (Saturation.occupation_positive b.flip ha hp)
  change Saturation.rightOccupation b M a u < M
  rw [Saturation.rightOccupation_left b a hu]
  obtain ⟨v,hv⟩ := hne
  have hh := ha.2 u v hv
  have hvp := hp v
  omega

/-- Equality in the original coefficient forces equality for the full labelled
contraction. C6 must still recover flatness from its simple representative. -/
theorem saturated_zero_transfer (b : Bipartition G) (u : V) (hu : b.side u = true)
    (hg : ChordalBipartite G) (X : Cover G M) (a : V → ℕ) (ha : Feasible G M a)
    (hp : Positive a) (hmax : ∀ v, b.side v = true → a v ≤ a u) (hz : deficit X a = 0) :
    (cover b u hu (gaugeCover X (starGauge X u))).coefficient
        (occupation u M (Saturation.rightOccupation b M a)) =
      (cover b u hu (gaugeCover X (starGauge X u))).ordinary.coefficient
        (occupation u M (Saturation.rightOccupation b M a)) := by
  rw [← saturated_coefficient_eq b u hu X a ha hmax,← saturated_ordinary_eq b u hu X a ha hmax]
  have hh := Saturation.right_saturated_deficit_zero b hg X a ha hp hz
  unfold deficit at hh
  exact Int.ofNat_inj.mp (sub_eq_zero.mp hh).symm

end
end CoefficientwiseRigidity.Star
