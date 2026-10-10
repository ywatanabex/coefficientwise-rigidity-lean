import CoefficientwiseRigidity.IncidentStar
import CoefficientwiseRigidity.ParallelRejection

/-! Positive-rank chordal rigidity by actual decreasing-vertex contraction and parallel rejection. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section

private theorem chordal_flat_aux (n : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ (G : SimpleGraph V) (_b : Bipartition G) (M : ℕ) (X : Cover G M) (a : V → ℕ),
        ChordalBipartite G → Feasible G M a → Positive a →
          coefficient X a = ordinary G M a → Flat X := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ hcard G b M X a hg ha hp heq
    by_cases hedge : ∃ x y, G.Adj x y
    · obtain ⟨u,hu,hun,hmax⟩ := Star.exists_incident_max b a hedge
      let ap := Saturation.rightOccupation b M a
      have hpa : Feasible G M ap := Saturation.occupation_feasible b.flip ha
      have ht : Star.Tight (G := G) ap u M := Star.saturated_tight_of_incident_max b u hu a hmax
      let H := Star.cover b u hu (gaugeCover X (Star.starGauge X u))
      let r := Star.occupation (G := G) u M ap
      have hhg : ChordalBipartite H.graph := Star.cover_chordalBipartite b u hu _ hg
      have hrf : Feasible H.graph M r := by
        rw [Star.cover_graph]
        exact Star.occupation_feasible b u hpa ht
      have hrp : Positive r := Star.saturated_positive b u hu a ha hp hun
      have hlt : Fintype.card (Star.Vertex G u) < n := by
        rw [← hcard]
        obtain ⟨v,hv⟩ := hun
        have hc := Star.card_vertices_lt hv
        simpa only [Fintype.card_eq_nat_card] using hc
      have hz : deficit X a = 0 := by simp [deficit,heq]
      have hzp := Saturation.right_saturated_deficit_zero b hg X a ha hp hz
      have hep : coefficient X ap = ordinary G M ap :=
        Int.ofNat_inj.mp (sub_eq_zero.mp hzp).symm
      have hfull : H.coefficient r = ordinary H.graph M r := by
        calc
          H.coefficient r = coefficient X ap := (Star.gauged_coefficient_eq b u hu X ap (hpa.1 u) ht).symm
          _ = ordinary G M ap := hep
          _ = H.ordinary.coefficient r := Star.ordinary_eq b u hu _ ap (hpa.1 u) ht
          _ = ordinary H.graph M r := H.ordinary_coefficient_eq r
      have hle := H.coefficient_le_representative r
      have hcomp := coefficient_le_of_chordalBipartite H.representative r hhg
      have hre : coefficient H.representative r = ordinary H.graph M r := by omega
      have hflat := ih (Fintype.card (Star.Vertex G u)) hlt (Star.Vertex G u) rfl
        H.graph H.bipartition M H.representative r hhg hrf hrp hre
      have hH : H.Flat := H.flat_of_representative_flat_of_eq r hrf hrp hflat (by omega)
      exact (Star.gauged_flat_iff b u hu X).mp hH
    · refine ⟨fun _ => Equiv.refl _,?_⟩
      intro u v he
      exact (hedge ⟨u,v,he⟩).elim

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

/-- Positive feasible ranks, including isolated full ranks, arbitrary components and small M. -/
theorem coefficient_eq_iff_flat_of_positive_chordalBipartite (b : Bipartition G) (X : Cover G M)
    (a : V → ℕ) (ha : Feasible G M a) (hp : Positive a) (hg : ChordalBipartite G) :
    coefficient X a = ordinary G M a ↔ Flat X :=
  ⟨chordal_flat_aux (Fintype.card V) V rfl G b M X a hg ha hp,
    fun h => activeFlat_coefficient_eq X a (flat_activeFlat X a h)⟩

end
end CoefficientwiseRigidity
