import CoefficientwiseRigidity.Sharpness
import CoefficientwiseRigidity.HullRelative
import CoefficientwiseRigidity.PaperReserve
import CoefficientwiseRigidity.PolynomialBound

/-!
Publication entry point for the full statements of main Theorems A–C.
The older `PaperMainTheorems` is the core target. This module additionally
includes B's attainment witnesses, C(ii)'s constructed-piece ratios, and
C(iii) for arbitrary positive real constants and the manuscript reserve.
It does not assert that every auxiliary result in the article is formalized.
-/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def MainCRelative (G : SimpleGraph V) : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ (X : Cover G M) (a : V → ℕ), Feasible G M a →
    ∀ (W : Finset V) (H : SimpleGraph V) (h : ConstructionPiece W H Finset.univ G),
      relativeDeficit (restrictCover X W H h.subgraph) (fun v => a v.val) ≤
        relativeDeficit X a

theorem paperMainCRelative (b : Bipartition G) : MainCRelative G := by
  intro M _ X a ha W H h
  have hr := h.relative_deficit M b X a
    ⟨fun v => ha.1 v.val, fun u v he => ha.2 u.val v.val he⟩
  simpa only [relativeDeficit, coefficient_restrict_univ, ordinary_induce_univ] using hr

def MainCQuantitativeReal (G : SimpleGraph V) : Prop :=
  ∀ (M : ℕ), 2 ≤ M → ∀ (X : Cover G M) (a : V → ℕ),
    Positive a → Feasible G M a → ∀ (W : Finset V) (H : SimpleGraph V)
      (hle : H ≤ G), WitnessHull W H Finset.univ G → ∀ (k : ℝ), 0 < k →
      (coefficient (restrictCover X W H hle) (fun v => a v.val) : ℝ) +
        k * paperReserve (H.induce (↑W : Set V)) M (fun v => a v.val) ≤
          ordinary (H.induce (↑W : Set V)) M (fun v => a v.val) →
      (coefficient X a : ℝ) + k * paperReserve G M a ≤ ordinary G M a

theorem paperMainCQuantitativeReal (b : Bipartition G) : MainCQuantitativeReal G := by
  intro M hM X a hp _ W H hle h k hk hh
  rw [paperReserve_eq_reserve (H.induce (↑W : Set V)) M
    (fun v : (↑W : Set V) => a v.val) (fun v => hp v.val)] at hh
  rw [paperReserve_eq_reserve G M a hp]
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : V → ℕ, a = fun v => q v + 1 :=
    ⟨fun v => a v - 1, by funext v; change a v = a v - 1 + 1; have := hp v; omega⟩
  have hq := h.quantitative_succ m b X q k hk.le hh
  rw [coefficient_restrict_univ X (fun v => q v + 1),
    reserve_induce_univ G (m + 2) (fun v => q v + 1),
    ordinary_induce_univ G (m + 2) (fun v => q v + 1)] at hq
  exact hq

/-- Both witnesses satisfy every graph/rank hypothesis of B. The second has odd holonomy. -/
def MainBSharpness : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), Nonempty (Bipartition G) ∧
    G.Connected ∧ (∃ u v, G.Adj u v) ∧ TreewidthAtMostTwo G ∧
    Positive (fun _ : Fin n => 1) ∧
    (∃ X : Cover G 2, Feasible G 2 (fun _ => 1) ∧ ¬ Flat X ∧
      0 < reserve G 2 (fun _ => 1) ∧
      coefficient X (fun _ => 1) + 2 * reserve G 2 (fun _ => 1) = ordinary G 2 (fun _ => 1)) ∧
    (∃ (X : Cover G 3) (root : Fin n), Feasible G 3 (fun _ => 1) ∧ ¬ Flat X ∧
      Odd (Nat.card (holonomyGroup X root)) ∧ 0 < reserve G 3 (fun _ => 1) ∧
      coefficient X (fun _ => 1) + 3 * reserve G 3 (fun _ => 1) = ordinary G 3 (fun _ => 1))

theorem paperMainBSharpness : MainBSharpness := by
  refine ⟨4, Sharpness.cycleFour, ⟨Sharpness.cycleFourBipartition⟩,
    Sharpness.cycleFour_connected, ⟨0, 1, by decide⟩, Sharpness.cycleFour_treewidth,
    (by intro v; norm_num), ?_, ?_⟩
  · refine ⟨Sharpness.twistedCycle 2 Sharpness.swapTwo, ?_,
      Sharpness.twistedCycle_nonflat _ _ (by decide), ?_, ?_⟩
    · exact ⟨fun _ => by norm_num, fun _ _ _ => by norm_num⟩
    · rw [reserve_singleton]; norm_num
    · rw [Sharpness.two_counts.1, Sharpness.two_counts.2, reserve_singleton]
  · refine ⟨Sharpness.twistedCycle 3 Sharpness.rotateThree, 0, ?_,
      Sharpness.twistedCycle_nonflat _ _ (by decide), ?_, ?_, ?_⟩
    · exact ⟨fun _ => by norm_num, fun _ _ _ => by norm_num⟩
    · rw [Sharpness.three_holonomy_order]; decide
    · rw [reserve_singleton]; norm_num
    · rw [Sharpness.three_counts.1, Sharpness.three_counts.2, reserve_singleton]

/-- Main A–C in the current manuscript, including the clauses missing from the old core. -/
def ManuscriptMainTheorems : Prop :=
  PaperMainTheorems ∧ MainBSharpness ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Nonempty (Bipartition G) →
      MainCRelative G ∧ MainCQuantitativeReal G

theorem manuscriptMainTheorems : ManuscriptMainTheorems := by
  refine ⟨paperMainTheorems, paperMainBSharpness, ?_⟩
  intro n G hb
  obtain ⟨b⟩ := hb
  exact ⟨paperMainCRelative b, paperMainCQuantitativeReal b⟩

end
end CoefficientwiseRigidity
