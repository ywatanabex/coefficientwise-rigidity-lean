import CoefficientwiseRigidity.NetworkFlatOperations
import CoefficientwiseRigidity.NetworkGraph
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
The structural bridge in W3's both-flat case. Every retained factor must
contain an actual gain entry: empty lists do not constrain a gauge.
-/
namespace CoefficientwiseRigidity.Network
open Kernel
noncomputable section
variable {M : ℕ} {V : Type} {p : V → ℕ}

def Net.HasEntries (N : Net M p) : Prop := ∀ e ∈ N.edges, e.kernels ≠ []

theorem Net.HasEntries.of_nonconstant {N : Net M p}
    (hN : ∀ e ∈ N.edges, e.Nonconstant) : N.HasEntries := by
  intro e he hn
  obtain ⟨f, hf, _⟩ := hN e he
  simp [hn] at hf

/-- Two gauges agreeing at one end of a factor agree at the other end. -/
theorem Net.Gauge.eq_at_adj {N : Net M p} (hN : N.HasEntries)
    {γ δ : V → Equiv.Perm (Fin M)} (hγ : N.Gauge γ) (hδ : N.Gauge δ)
    {u v : V} (huv : N.graph.Adj u v) (hu : γ u = δ u) : γ v = δ v := by
  obtain ⟨e, he, h | h⟩ := huv
  · obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ (hN e he)
    rcases h with ⟨rfl, rfl⟩
    apply Equiv.ext
    intro i
    apply f.gain.injective
    rw [hγ e he f hf i, hδ e he f hf i, hu]
  · obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ (hN e he)
    rcases h with ⟨rfl, rfl⟩
    apply Equiv.ext
    intro i
    rw [← hγ e he f hf i, ← hδ e he f hf i, hu]

theorem Net.Gauge.eq_at_walk {N : Net M p} (hN : N.HasEntries)
    {γ δ : V → Equiv.Perm (Fin M)} (hγ : N.Gauge γ) (hδ : N.Gauge δ)
    {u v : V} (P : N.graph.Walk u v) (hu : γ u = δ u) : γ v = δ v := by
  induction P with
  | nil => exact hu
  | cons h P ih => exact ih (hγ.eq_at_adj hN hδ h hu)

/-- Different flat choices cannot be joined by a path avoiding the chosen edge. -/
theorem Net.not_reachable_of_flat_choices (N : Net M p) (hN : N.HasEntries)
    (u v : V) (huv : u ≠ v) (e f : GainEntry M (p u) (p v))
    (he : (N.addEdge u v huv [e]).Flat) (hf : (N.addEdge u v huv [f]).Flat)
    (hne : e.gain ≠ f.gain) : ¬ N.graph.Reachable u v := by
  rintro ⟨P⟩
  obtain ⟨γ, hγ⟩ := he
  obtain ⟨δ, hδ⟩ := hf
  let σ := (γ u).trans (δ u).symm
  let δ' := fun w => σ.trans (δ w)
  have hd' : (N.addEdge u v huv [f]).Gauge δ' := Net.Gauge.trans hδ σ
  obtain ⟨heγ, hγN⟩ := (N.gauge_addSingle_iff u v huv e γ).mp hγ
  obtain ⟨hfδ, hδN⟩ := (N.gauge_addSingle_iff u v huv f δ').mp hd'
  have hu : δ' u = γ u := by ext i; simp [δ', σ]
  have hv : γ v = δ' v := hγN.eq_at_walk hN hδN P hu.symm
  apply hne
  apply Equiv.ext
  intro i
  obtain ⟨j, rfl⟩ := (γ v).surjective i
  rw [heγ j, hv, hfδ j, hu]

theorem Net.graph_addEdge (N : Net M p) (u v : V) (huv : u ≠ v)
    (L : GainList M (p u) (p v)) :
    (N.addEdge u v huv L).graph = N.graph ⊔ SimpleGraph.edge u v := by
  ext x y
  simp [Net.graph, Net.addEdge, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  aesop

theorem Net.isBridge_addEdge_of_not_reachable (N : Net M p)
    (u v : V) (huv : u ≠ v) (L : GainList M (p u) (p v))
    (h : ¬ N.graph.Reachable u v) :
    (N.addEdge u v huv L).graph.IsBridge (Sym2.mk (u,v)) := by
  rw [SimpleGraph.isBridge_iff, N.graph_addEdge]
  refine ⟨Or.inr ?_, ?_⟩
  · exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
  · intro hr
    apply h (hr.mono ?_)
    intro x y hxy
    exact hxy.1.resolve_right hxy.2

/-- The bridge conclusion is derived from the two flat branches, not assumed. -/
theorem Net.isBridge_of_flat_choices (N : Net M p) (hN : N.HasEntries)
    (u v : V) (huv : u ≠ v) (e f : GainEntry M (p u) (p v))
    (he : (N.addEdge u v huv [e]).Flat) (hf : (N.addEdge u v huv [f]).Flat)
    (hne : e.gain ≠ f.gain) :
    (N.addEdge u v huv [e]).graph.IsBridge (Sym2.mk (u,v)) :=
  N.isBridge_addEdge_of_not_reachable u v huv [e]
    (N.not_reachable_of_flat_choices hN u v huv e f he hf hne)

/-- The actual reachability cut separates the two roots and every background edge. -/
theorem Net.exists_cut_of_not_reachable (N : Net M p) (u v : V)
    (h : ¬ N.graph.Reachable u v) :
    ∃ S : Set V, u ∈ S ∧ v ∉ S ∧ ∀ e ∈ N.edges, (e.left ∈ S ↔ e.right ∈ S) := by
  refine ⟨{w | N.graph.Reachable u w}, SimpleGraph.Reachable.refl _, h, ?_⟩
  intro e he
  have hadj : N.graph.Adj e.left e.right := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun hl => hl.trans hadj.reachable, fun hr => hr.trans hadj.symm.reachable⟩

end
end CoefficientwiseRigidity.Network
