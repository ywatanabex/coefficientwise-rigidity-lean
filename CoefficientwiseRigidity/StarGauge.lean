import CoefficientwiseRigidity.TightStar
import CoefficientwiseRigidity.HolonomyGauge
import CoefficientwiseRigidity.GraphSaturation

/-! Construct the identity-star gauge and transport flatness through the actual contraction. -/
namespace CoefficientwiseRigidity.Star
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V} {M : ℕ}

def starGauge (X : Cover G M) (u : V) (v : V) : Equiv.Perm (Fin M) :=
  if G.Adj u v then X.transport u v else Equiv.refl _

theorem starGauge_normalized (X : Cover G M) (u : V) :
    Normalized (gaugeCover X (starGauge X u)) u := by
  intro v he
  ext i
  simp [gaugeCover,starGauge,he]

def contractGauge (u : V) (γ : V → Equiv.Perm (Fin M)) : Vertex G u → Equiv.Perm (Fin M)
  | none => γ u
  | some v => γ v.val

theorem contractGauge_project (X : Cover G M) {u : V} (hn : Normalized X u)
    (γ : V → Equiv.Perm (Fin M))
    (hγ : ∀ x y, G.Adj x y → ∀ i, X.transport x y (γ x i) = γ y i) (v : V) :
    contractGauge u γ (project G u v) = γ v := by
  by_cases hv : v = u
  · subst v; simp [contractGauge]
  by_cases he : G.Adj u v
  · rw [project_neighbor he]
    apply Equiv.ext
    intro i
    have h := hγ u v he i
    rw [hn v he] at h
    exact h
  · simp [project,hv,he,contractGauge]

theorem flat_iff (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (hn : Normalized X u) : (cover b u hu X).Flat ↔ Flat X := by
  constructor
  · rintro ⟨δ,hδ⟩
    refine ⟨fun v => δ (project G u v),?_⟩
    intro x y he i
    change X.transport x y (δ (project G u x) i) = δ (project G u y) i
    by_cases hx : x = u
    · subst x; rw [hn y he,project_self,project_neighbor he]; rfl
    by_cases hy : y = u
    · subst y
      rw [X.reverse (G.symm he),hn x (G.symm he),project_self,project_neighbor (G.symm he)]
      rfl
    cases hside : b.side x with
    | true => exact hδ ⟨(x,y),hside,he,hx,hy⟩ i
    | false =>
      have hsy : b.side y = true := by
        have hh := b.opposite he
        rw [hside] at hh
        cases h : b.side y <;> simp_all
      have h := hδ ⟨(y,x),hsy,G.symm he,hy,hx⟩ i
      change X.transport y x (δ (project G u y) i) = δ (project G u x) i at h
      rw [X.reverse he] at h
      exact (Equiv.eq_symm_apply _).mp h.symm
  · rintro ⟨γ,hγ⟩
    refine ⟨contractGauge u γ,?_⟩
    intro e i
    change X.transport e.val.1 e.val.2 (contractGauge u γ (project G u e.val.1) i) =
      contractGauge u γ (project G u e.val.2) i
    rw [contractGauge_project X hn γ hγ,contractGauge_project X hn γ hγ]
    exact hγ _ _ e.property.2.1 i

theorem gauged_flat_iff (b : Bipartition G) (u : V) (hu : b.side u = true) (X : Cover G M) :
    (cover b u hu (gaugeCover X (starGauge X u))).Flat ↔ Flat X :=
  (flat_iff b u hu _ (starGauge_normalized X u)).trans (gaugeCover_flat_iff X _)

variable [Fintype V] [DecidableEq V]

/-- The original ungauged cover is included in the configuration bijection. -/
def gaugedConfigurationEquiv (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : a u ≤ M) (ht : Tight (G := G) a u M) :
    Configuration X a ≃
      (cover b u hu (gaugeCover X (starGauge X u))).Configuration (occupation u M a) :=
  (gaugeConfigurationEquiv X (gaugeCover X (starGauge X u)) a
    (fun v => (starGauge X u v).symm) (by
      intro x y _ _ _ i
      simp [gaugeCover])).trans
    (configurationEquiv b u hu _ a ha (starGauge_normalized X u) ht)

theorem gauged_coefficient_eq (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : a u ≤ M) (ht : Tight (G := G) a u M) :
    coefficient X a = (cover b u hu (gaugeCover X (starGauge X u))).coefficient (occupation u M a) := by
  exact Fintype.card_congr (gaugedConfigurationEquiv b u hu X a ha ht)

omit [DecidableEq V] in
theorem saturated_tight (b : Bipartition G) (u : V) (hu : b.side u = true)
    (a : V → ℕ) (hmax : ∀ v, b.side v = true → a v ≤ a u) :
    Tight (G := G) (Saturation.rightOccupation b M a) u M := by
  intro v he
  have hv : b.side v = false := by
    have hn := b.opposite he
    rw [hu] at hn
    cases h : b.side v <;> simp_all
  rw [Saturation.rightOccupation_right b a hv,Saturation.rightOccupation_left b a hu]
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro w hw
    have hwedge := (Finset.mem_filter.mp hw).2
    have hwside : b.side w = true := by
      have hn := b.opposite hwedge
      rw [hv] at hn
      cases h : b.side w <;> simp_all
    exact hmax w hwside
  · exact Finset.le_sup (f := a) (by simp [G.symm he])

end
end CoefficientwiseRigidity.Star
