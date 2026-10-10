import CoefficientwiseRigidity.NetworkExactPacking

/-!
The complete parallel case selection for W3. The smaller simple-network bound
is explicitly an induction hypothesis, not a certificate of the main theorem.
-/
namespace CoefficientwiseRigidity
open Kernel Finset
noncomputable section

theorem kappa_nonneg {M : ℕ} (Γ : Subgroup (Equiv.Perm (Fin M))) : 0 ≤ kappa M Γ := by
  classical
  rw [kappa_eq_min]
  split_ifs with h
  · apply Finset.le_min'
    intro a ha
    obtain ⟨σ,_,_,k,_,_,rfl⟩ := (mem_kappaRatios_iff Γ a).mp ha
    positivity
  · exact le_rfl

namespace Network
variable {M : ℕ} {V : Type} [Fintype V] {p : V → ℕ}

theorem Net.parallel_swap_value (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v)) (b : Bool) :
    ((N.addEdge u v huv [e]).addEdge u v huv [f]).value b =
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).value b := by
  simp only [Net.value, Net.addEdge, weight_cons, mul_left_comm]

omit [Fintype V] in
theorem Net.flat_parallel_swap_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v)) :
    ((N.addEdge u v huv [e]).addEdge u v huv [f]).Flat ↔
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).Flat := by
  simp only [Net.flat_iff_gauge, Net.gauge_addSingle_iff, and_left_comm]

/-- Whichever choice is nonflat supplies the F induction branch. If both are
flat, the previously proved bridge theorem supplies the bound directly. -/
theorem Net.parallel_kappa_step (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (Γ : Subgroup (Equiv.Perm (Fin (M + 2)))) (hN : N.HasEntries)
    (u v : V) (huv : u ≠ v) (e f : GainEntry (M + 2) (p u + 1) (p v + 1))
    (he : e.Nonconstant) (hf : f.Nonconstant) (heΓ : e.gain ∈ Γ) (hfΓ : f.gain ∈ Γ)
    (hwidth : TreewidthAtMostTwo (N.addEdge u v huv [e]).graph)
    (hn : ¬ ((N.addEdge u v huv [f]).addEdge u v huv [e]).Flat)
    (hrec : ∀ g : GainEntry (M + 2) (p u + 1) (p v + 1),
      g.Nonconstant → g.gain ∈ Γ → ¬ (N.addEdge u v huv [g]).Flat →
      kappa (M + 2) Γ * ((N.addEdge u v huv [g]).reduce hp).value true ≤
        (N.addEdge u v huv [g]).value true - (N.addEdge u v huv [g]).value false) :
    kappa (M + 2) Γ * (((N.addEdge u v huv [f]).addEdge u v huv [e]).reduce hp).value true ≤
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).value true -
        ((N.addEdge u v huv [f]).addEdge u v huv [e]).value false := by
  classical
  by_cases hE : (N.addEdge u v huv [e]).Flat
  · by_cases hF : (N.addEdge u v huv [f]).Flat
    · exact N.parallel_kappa_of_flat_choices hp hN u v huv e f hE hF hn Γ heΓ hfΓ
    · have hi := hrec (f.splitLeft e) (f.splitLeft_nonconstant e (hp u) (hp v) hf he) hfΓ
        (fun h => hF ((N.flat_splitLeft_iff u v huv f e).mp h))
      have hw : TreewidthAtMostTwo (N.addEdge u v huv [f]).graph := by
        rwa [Net.graph_addEdge] at hwidth ⊢
      have hb := N.parallel_bound_of_treewidth_splitLeft hp u v huv f e _ (kappa_nonneg Γ) hw hi
      simpa only [Net.reduce_addSingle, N.parallel_swap_value u v huv e f,
        (N.reduce hp).parallel_swap_value u v huv (e.reduce (hp u) (hp v))
          (f.reduce (hp u) (hp v))] using hb
  · apply N.parallel_bound_of_treewidth_splitLeft hp u v huv e f _ (kappa_nonneg Γ) hwidth
    exact hrec (e.splitLeft f) (e.splitLeft_nonconstant f (hp u) (hp v) he hf) heΓ
      (fun h => hE ((N.flat_splitLeft_iff u v huv e f).mp h))

end Network
end
end CoefficientwiseRigidity
