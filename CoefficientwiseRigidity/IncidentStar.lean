import CoefficientwiseRigidity.SaturatedStar

/-! Maximise only among incident left vertices, retaining all isolated factors in the induction. -/
namespace CoefficientwiseRigidity.Star
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] {G : SimpleGraph V} {M : ℕ}

theorem exists_incident_max (b : Bipartition G) (a : V → ℕ) (he : ∃ x y, G.Adj x y) :
    ∃ u, b.side u = true ∧ (∃ v, G.Adj u v) ∧
      ∀ w, b.side w = true → (∃ v, G.Adj w v) → a w ≤ a u := by
  obtain ⟨x,y,hxy⟩ := he
  have hleft : ∃ v, b.side v = true ∧ ∃ w, G.Adj v w := by
    cases hx : b.side x with
    | true => exact ⟨x,hx,y,hxy⟩
    | false =>
      have hy : b.side y = true := by
        have hn := b.opposite hxy
        rw [hx] at hn
        cases h : b.side y <;> simp_all
      exact ⟨y,hy,x,G.symm hxy⟩
  let U := univ.filter (fun v => b.side v = true ∧ ∃ w, G.Adj v w)
  have hn : U.Nonempty := by
    obtain ⟨v,hv⟩ := hleft
    exact ⟨v,by simp [U,hv]⟩
  obtain ⟨u,hu,hm⟩ := Finset.exists_max_image U a hn
  have hu' := (Finset.mem_filter.mp hu).2
  exact ⟨u,hu'.1,hu'.2,fun w hw hew => hm w (by simp [U,hw,hew])⟩

theorem saturated_tight_of_incident_max (b : Bipartition G) (u : V) (hu : b.side u = true)
    (a : V → ℕ) (hmax : ∀ v, b.side v = true → (∃ w, G.Adj v w) → a v ≤ a u) :
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
    exact hmax w hwside ⟨v,G.symm hwedge⟩
  · exact Finset.le_sup (f := a) (by simp [G.symm he])

end
end CoefficientwiseRigidity.Star
