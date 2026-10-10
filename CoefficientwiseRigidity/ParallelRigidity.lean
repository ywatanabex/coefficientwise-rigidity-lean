import CoefficientwiseRigidity.NetworkCut
import CoefficientwiseRigidity.TerminalCollision

/-!
W3's both-flat branch, now on the original network rather than a supplied
two-component presentation. The bridge, cut, pieces and exact reduced reserve
are constructed from the hypotheses. No graph decomposition is assumed.
-/
namespace CoefficientwiseRigidity.Network
open Kernel
open scoped Classical
noncomputable section
variable {M : ℕ} {V : Type} [Fintype V] {p : V → ℕ}

theorem Net.parallel_kappa_of_flat_choices (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (hN : N.HasEntries) (u v : V) (huv : u ≠ v)
    (e f : GainEntry (M + 2) (p u + 1) (p v + 1))
    (he : (N.addEdge u v huv [e]).Flat) (hf : (N.addEdge u v huv [f]).Flat)
    (hn : ¬ ((N.addEdge u v huv [f]).addEdge u v huv [e]).Flat)
    (Γ : Subgroup (Equiv.Perm (Fin (M + 2)))) (heΓ : e.gain ∈ Γ) (hfΓ : f.gain ∈ Γ) :
    kappa (M + 2) Γ * (((N.addEdge u v huv [f]).addEdge u v huv [e]).reduce hp).value true ≤
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).value true -
        ((N.addEdge u v huv [f]).addEdge u v huv [e]).value false := by
  have hne := N.gains_ne_of_nonflat_parallel u v huv e f hn he
  have hnr := N.not_reachable_of_flat_choices hN u v huv e f he hf hne
  obtain ⟨S, hu, hv, hS⟩ := N.exists_cut_of_not_reachable u v hnr
  have hflat : N.Flat := by
    obtain ⟨γ, hγ⟩ := he
    exact ⟨γ, Net.Gauge.of_addEdge hγ⟩
  have hc := (N.onSet S).joinTwo_flat_kappa (N.onSet Sᶜ)
    (fun w => hp w) (fun w => hp w) (Net.onSet_flat hflat S) (Net.onSet_flat hflat Sᶜ)
    ⟨u,hu⟩ ⟨v,hv⟩ e f Γ heΓ hfΓ hne
  have hSr : ∀ g ∈ (N.reduce hp).edges, g.left ∈ S ↔ g.right ∈ S := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact hS g' hg'
  have hr := (N.reduce hp).parallel_value_cut S hSr u v huv hu hv
    (e.reduce (hp u) (hp v)) (f.reduce (hp u) (hp v)) true
  rw [Net.onSet_reduce, Net.onSet_reduce] at hr
  rw [Net.reduce_addSingle, Net.reduce_addSingle, hr,
    N.parallel_value_cut S hS u v huv hu hv e f true,
    N.parallel_value_cut S hS u v huv hu hv e f false]
  have hm := mul_le_mul_of_nonneg_left hc N.scalar_nonneg
  change kappa (M + 2) Γ * (N.scalar * _) ≤ _
  nlinarith only [hm]

theorem Net.parallel_two_of_flat_choices (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (hN : N.HasEntries) (u v : V) (huv : u ≠ v)
    (e f : GainEntry (M + 2) (p u + 1) (p v + 1))
    (he : (N.addEdge u v huv [e]).Flat) (hf : (N.addEdge u v huv [f]).Flat)
    (hn : ¬ ((N.addEdge u v huv [f]).addEdge u v huv [e]).Flat) :
    2 * (((N.addEdge u v huv [f]).addEdge u v huv [e]).reduce hp).value true ≤
      ((N.addEdge u v huv [f]).addEdge u v huv [e]).value true -
        ((N.addEdge u v huv [f]).addEdge u v huv [e]).value false := by
  have hne := N.gains_ne_of_nonflat_parallel u v huv e f hn he
  have hr := relative_gain_ne_one e f hne
  have hk := two_le_kappa (⊤ : Subgroup (Equiv.Perm (Fin (M + 2))))
    ⟨e.gain.trans f.gain.symm, Subgroup.mem_top _, hr⟩
  exact (mul_le_mul_of_nonneg_right hk (Net.value_nonneg _ true)).trans
    (N.parallel_kappa_of_flat_choices hp hN u v huv e f he hf hn ⊤
      (Subgroup.mem_top _) (Subgroup.mem_top _))

end
end CoefficientwiseRigidity.Network
