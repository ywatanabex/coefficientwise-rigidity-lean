import CoefficientwiseRigidity.CoefficientNetwork

/-! The underlying simple graph records actual edge factors, even zero lists. -/
namespace CoefficientwiseRigidity
open Network
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ} {a : V → ℕ}

def Network.Net.graph {p : V → ℕ} (N : Net M p) : SimpleGraph V where
  Adj u v := ∃ e ∈ N.edges, (e.left = u ∧ e.right = v) ∨ (e.left = v ∧ e.right = u)
  symm := by
    intro u v
    rintro ⟨e, he, h | h⟩
    · exact ⟨e, he, Or.inr h⟩
    · exact ⟨e, he, Or.inl h⟩
  loopless := by
    intro u
    rintro ⟨e, _, h | h⟩ <;> exact e.distinct (h.1.trans h.2.symm)

omit [DecidableEq V] in
theorem inclusionNetwork_graph (b : Bipartition G) (X : Cover G M) (a : V → ℕ) :
    (inclusionNetwork b X a).graph = G := by
  classical
  ext u v
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
    rcases h with h | h
    · exact h.1 ▸ h.2 ▸ f.property.1
    · exact h.2 ▸ h.1 ▸ G.symm f.property.1
  · intro huv
    cases hsu : b.side u with
    | true =>
      let e : LeftEdge b := ⟨(u,v), huv, hsu⟩
      refine ⟨inclusionEdge b X e, ?_, Or.inl ⟨rfl,rfl⟩⟩
      simp [inclusionNetwork, List.mem_map, e]
    | false =>
      have hsv : b.side v = true := by
        have hne := b.opposite huv
        cases hv : b.side v <;> simp_all
      let e : LeftEdge b := ⟨(v,u), G.symm huv, hsv⟩
      refine ⟨inclusionEdge b X e, ?_, Or.inr ⟨rfl,rfl⟩⟩
      simp [inclusionNetwork, List.mem_map, e]

end
end CoefficientwiseRigidity
