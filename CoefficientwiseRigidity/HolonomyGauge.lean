import CoefficientwiseRigidity.CoefficientQuantitative

/-!
Gauge along actual root-to-vertex walks. Every resulting edge transport is an
original root holonomy, so W3 uses the original group and the original kappa.
-/
namespace CoefficientwiseRigidity
open Kernel Network
noncomputable section
variable {V : Type} {G : SimpleGraph V} {M : ℕ}

def gaugeCover (X : Cover G M) (γ : V → Equiv.Perm (Fin M)) : Cover G M where
  transport u v := ((γ u).trans (X.transport u v)).trans (γ v).symm
  reverse h := by
    ext i
    simp [X.reverse h]

theorem gaugeCover_flat_iff (X : Cover G M) (γ : V → Equiv.Perm (Fin M)) :
    Flat (gaugeCover X γ) ↔ Flat X := by
  constructor
  · rintro ⟨δ,hδ⟩
    refine ⟨fun v => (δ v).trans (γ v), ?_⟩
    intro u v huv i
    have h := congrArg (γ v) (hδ u v huv i)
    simpa [gaugeCover] using h
  · rintro ⟨δ,hδ⟩
    refine ⟨fun v => (δ v).trans (γ v).symm, ?_⟩
    intro u v huv i
    simp only [gaugeCover, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [hδ u v huv i]

theorem gaugeCover_coefficient [Fintype V] [DecidableEq V]
    (X : Cover G M) (γ : V → Equiv.Perm (Fin M)) (a : V → ℕ) :
    coefficient (gaugeCover X γ) a = coefficient X a := by
  apply coefficient_eq_of_gauge
  refine ⟨γ, ?_⟩
  intro u v _ _ _ i
  simp [gaugeCover]

def rootGauge (X : Cover G M) (hc : G.Connected) (root : V) : V → Equiv.Perm (Fin M) :=
  fun v => walkTransport X (Classical.choice (hc root v))

/-- The transport is the closed walk root→u→v→root, in that order. -/
theorem rootGauge_transport_mem (X : Cover G M) (hc : G.Connected) (root : V)
    (u v : V) (huv : G.Adj u v) :
    (gaugeCover X (rootGauge X hc root)).transport u v ∈ holonomyGroup X root := by
  let pu : G.Walk root u := Classical.choice (hc root u)
  let pv : G.Walk root v := Classical.choice (hc root v)
  apply Subgroup.subset_closure
  refine ⟨(pu.append (.cons huv .nil)).append pv.reverse, ?_⟩
  rw [walkTransport_append, walkTransport_append, walkTransport_reverse]
  ext i
  rfl

variable [Fintype V] [DecidableEq V]

/-- The unchanged holonomy-sensitive quantitative proposition of the paper. -/
theorem mainBKappa (b : Bipartition G) : MainBKappa G := by
  intro M hM X a root hc he hw hp hf hn
  have hk := holonomy_kappa_bounds X hc root hn
  have hi := interior_of_incident a hf hp (connected_has_neighbor hc he)
  have hpos := reserve_pos b a hM hf hp hi
  refine ⟨hk.1,hk.2,?_,hpos⟩
  obtain ⟨m,rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  let Y := gaugeCover X (rootGauge X hc root)
  have hY : ¬ Flat Y := fun h => hn ((gaugeCover_flat_iff X _).mp h)
  have h := coefficient_kappa_of_interior_treewidth b Y
    (fun v => ⟨hp v, by have := hi v; omega⟩) hf hw hY (holonomyGroup X root)
    (rootGauge_transport_mem X hc root)
  rwa [gaugeCover_coefficient] at h

/-- The unchanged odd-holonomy 3R proposition follows with the original reserve. -/
theorem mainBOdd (b : Bipartition G) : MainBOdd G := by
  intro M hM X a root hc he hw hp hf hn hodd
  obtain ⟨_,hk,hbound,_⟩ := mainBKappa b M hM X a root hc he hw hp hf hn
  have hmul := mul_le_mul_of_nonneg_right (hk hodd) (Nat.cast_nonneg (reserve G M a) :
    (0 : ℚ) ≤ _)
  have h : (coefficient X a : ℚ) + 3 * reserve G M a ≤ ordinary G M a := by linarith
  exact_mod_cast h

/-- All three original Main B propositions, at the graph scope of the paper target. -/
theorem paperMainB : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Nonempty (Bipartition G) →
    MainBTwo G ∧ MainBKappa G ∧ MainBOdd G := by
  intro n G hb
  obtain ⟨b⟩ := hb
  exact ⟨mainBTwo b,mainBKappa b,mainBOdd b⟩

end
end CoefficientwiseRigidity
