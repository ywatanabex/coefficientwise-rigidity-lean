import CoefficientwiseRigidity.NetworkFlatOperations
import CoefficientwiseRigidity.CoefficientNetwork

/-!
Exact flatness bridge for the original cover and its inclusion network.
The inverse gain convention is accounted for explicitly in both directions.
No feasibility, comparison or equality-of-counts premise is used.
-/
namespace CoefficientwiseRigidity
open Kernel Network
noncomputable section
variable {V : Type} [Fintype V] {G : SimpleGraph V} {M : ℕ}

theorem inclusionNetwork_gauge_iff (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (γ : V → Equiv.Perm (Fin M)) :
    (inclusionNetwork b X a).Gauge γ ↔
      ∀ u v, G.Adj u v → ∀ i, X.transport u v (γ u i) = γ v i := by
  classical
  constructor
  · intro h u v huv i
    cases hsu : b.side u with
    | true =>
      let e : LeftEdge b := ⟨(u,v),huv,hsu⟩
      have he : inclusionEdge (a := a) b X e ∈ (inclusionNetwork b X a).edges := by
        simp [inclusionNetwork, e]
      have hi := h (inclusionEdge b X e) he (inclusionEntry b X e) (by simp [inclusionEdge]) i
      change (X.transport u v).symm (γ v i) = γ u i at hi
      apply (X.transport u v).symm.injective
      simpa using hi.symm
    | false =>
      have hsv : b.side v = true := by
        have hn := b.opposite huv
        cases hs : b.side v <;> simp_all
      let e : LeftEdge b := ⟨(v,u),G.symm huv,hsv⟩
      have he : inclusionEdge (a := a) b X e ∈ (inclusionNetwork b X a).edges := by
        simp [inclusionNetwork, e]
      have hi := h (inclusionEdge b X e) he (inclusionEntry b X e) (by simp [inclusionEdge]) i
      change (X.transport v u).symm (γ u i) = γ v i at hi
      simpa only [X.reverse huv, Equiv.symm_symm] using hi
  · intro h e he f hf i
    obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
    have hf' : f = inclusionEntry (a := a) b X e' := by simpa [inclusionEdge] using hf
    subst f
    change (X.transport e'.val.1 e'.val.2).symm (γ e'.val.2 i) = γ e'.val.1 i
    apply (X.transport e'.val.1 e'.val.2).injective
    simpa using (h _ _ e'.property.1 i).symm

theorem inclusionNetwork_flat_iff (b : Bipartition G) (X : Cover G M) (a : V → ℕ) :
    (inclusionNetwork b X a).Flat ↔ Flat X := by
  simp only [Network.Net.flat_iff_gauge, inclusionNetwork_gauge_iff, Flat]

end
end CoefficientwiseRigidity
