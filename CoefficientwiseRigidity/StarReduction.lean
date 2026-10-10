import CoefficientwiseRigidity.StarGauge
import CoefficientwiseRigidity.StarGraph

/-! Rank feasibility, ordinary counts and explicit saturation-to-contraction data. -/
namespace CoefficientwiseRigidity.Star
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem occupation_feasible (b : Bipartition G) (u : V) {a : V → ℕ}
    (ha : Feasible G M a) (ht : Tight (G := G) a u M) :
    Feasible (graph G u) M (occupation u M a) := by
  constructor
  · intro v
    cases v with
    | none => exact Nat.sub_le _ _
    | some v => exact ha.1 v.val
  · intro x y he
    obtain ⟨e,h | h⟩ := graph_edge_label b he
    · rw [← h.1,← h.2,occupation_project u a ht e.property.2.2.1,
        occupation_project u a ht e.property.2.2.2]
      exact ha.2 _ _ e.property.2.1
    · rw [← h.1,← h.2,occupation_project u a ht e.property.2.2.1,
        occupation_project u a ht e.property.2.2.2]
      exact ha.2 _ _ (G.symm e.property.2.1)

omit [Fintype V] [DecidableEq V] in
theorem occupation_positive (u : V) {a : V → ℕ} (hp : Positive a) (hu : a u < M) :
    Positive (occupation (G := G) u M a) := by
  intro v
  cases v with
  | none => exact Nat.sub_pos_of_lt hu
  | some v => exact hp v.val

omit [Fintype V] [DecidableEq V] in
theorem cover_ordinary (b : Bipartition G) (u : V) (hu : b.side u = true) (X : Cover G M) :
    (cover b u hu X).ordinary = cover b u hu (trivialCover G M) := rfl

theorem ordinary_eq (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : a u ≤ M) (ht : Tight (G := G) a u M) :
    ordinary G M a = (cover b u hu X).ordinary.coefficient (occupation u M a) := by
  rw [cover_ordinary]
  exact coefficient_eq b u hu (trivialCover G M) a ha (fun _ _ => rfl) ht

theorem gauged_deficit_eq (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : a u ≤ M) (ht : Tight (G := G) a u M) :
    deficit X a =
      ((cover b u hu (gaugeCover X (starGauge X u))).ordinary.coefficient (occupation u M a) : ℤ) -
      (cover b u hu (gaugeCover X (starGauge X u))).coefficient (occupation u M a) := by
  rw [deficit,ordinary_eq b u hu (gaugeCover X (starGauge X u)) a ha ht,
    gauged_coefficient_eq b u hu X a ha ht]

omit [DecidableEq V] in
theorem exists_maximal_left (b : Bipartition G) (a : V → ℕ)
    (hl : ∃ v, b.side v = true) : ∃ u, b.side u = true ∧ ∀ v, b.side v = true → a v ≤ a u := by
  obtain ⟨v,hv⟩ := hl
  obtain ⟨u,hu,hm⟩ := Finset.exists_max_image (univ.filter (fun w => b.side w = true)) a ⟨v,by simp [hv]⟩
  exact ⟨u,(mem_filter.mp hu).2,fun w hw => hm w (by simp [hw])⟩

end
end CoefficientwiseRigidity.Star
