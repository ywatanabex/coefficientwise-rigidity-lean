import CoefficientwiseRigidity.NetworkInsertion
import CoefficientwiseRigidity.KernelReserve

/-!
Positive ordinary and reduced sums, including every ordinary root pin.
The same nested-prefix assignment attains all edge-profile endpoints at once.
Empty edge lists and reduced empty/full slices are included.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V : Type*} {p : V → ℕ}

def prefixState (hp : ∀ v, p v ≤ M) : State M p :=
  fun v => prefixSlice M (p v) (hp v)

def Edge.EndpointPositive (e : Edge M p) : Prop :=
  ∃ f ∈ e.kernels, 0 < f.profile (overlapRank M (p e.left) (p e.right))

def Edge.Nonconstant (e : Edge M p) : Prop :=
  ∃ f ∈ e.kernels, f.Nonconstant

theorem Edge.Nonconstant.endpointPositive {e : Edge M p} (he : e.Nonconstant) :
    e.EndpointPositive := by
  obtain ⟨f, hf, hn⟩ := he
  exact ⟨f, hf, f.endpoint_pos hn⟩

theorem Edge.Nonconstant.reduce_endpointPositive
    {e : Edge (M + 2) (fun v => p v + 1)} (he : e.Nonconstant)
    (hp : ∀ v, p v ≤ M) : (e.reduce hp).EndpointPositive := by
  obtain ⟨f, hf, hn⟩ := he
  exact ⟨f.reduce (hp e.left) (hp e.right), List.mem_map.mpr ⟨f, hf, rfl⟩,
    f.reduce_endpoint_pos (hp e.left) (hp e.right) hn⟩

theorem listOrdinary_pos_of_endpoint {a b : ℕ} (L : GainList M a b)
    (A : Slice M a) (B : Slice M b) (hz : overlap A B = overlapRank M a b)
    (hL : ∃ f ∈ L, 0 < f.profile (overlapRank M a b)) : 0 < listOrdinary L A B := by
  induction L with
  | nil => simp at hL
  | cons e L ih =>
    obtain ⟨f, hf, hn⟩ := hL
    rcases List.mem_cons.mp hf with he | hf
    · subst f
      apply add_pos_of_pos_of_nonneg _ (listOrdinary_nonneg L A B)
      simpa [GainEntry.ordinary, hz] using hn
    · exact add_pos_of_nonneg_of_pos (e.ordinary_nonneg A B) (ih ⟨f, hf, hn⟩)

theorem weight_prefix_pos (E : List (Edge M p)) (hp : ∀ v, p v ≤ M)
    (hE : ∀ e ∈ E, e.EndpointPositive) : 0 < weight E true (prefixState hp) := by
  induction E with
  | nil => exact zero_lt_one
  | cons e E ih =>
    apply mul_pos _ (ih fun f hf => hE f (List.mem_cons_of_mem e hf))
    exact listOrdinary_pos_of_endpoint e.kernels _ _
      (overlap_prefixSlice (hp e.left) (hp e.right)) (hE e (List.mem_cons_self _ _))

theorem Net.ordinary_value_pos [Fintype V] (N : Net M p) (hp : ∀ v, p v ≤ M)
    (hs : 0 < N.scalar) (hE : ∀ e ∈ N.edges, e.EndpointPositive) : 0 < N.value true := by
  classical
  apply mul_pos hs
  exact Finset.sum_pos' (fun S _ => weight_nonneg N.edges true S)
    ⟨prefixState hp, mem_univ _, weight_prefix_pos N.edges hp hE⟩

theorem Net.pinnedValue_ordinary_pos [Fintype V] (N : Net M p) (hp : ∀ v, p v ≤ M)
    (hs : 0 < N.scalar) (hE : ∀ e ∈ N.edges, e.EndpointPositive)
    (r : V) (A : Slice M (p r)) : 0 < N.pinnedValue r A true := by
  classical
  rw [← N.pinnedValue_ordinary_constant r (prefixState hp r) A]
  apply mul_pos hs
  apply Finset.sum_pos'
  · intro S _
    split_ifs
    · exact weight_nonneg _ _ _
    · exact le_refl _
  · refine ⟨prefixState hp, mem_univ _, ?_⟩
    simpa only [if_true] using weight_prefix_pos N.edges hp hE

theorem Net.reduce_endpointPositive (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (hE : ∀ e ∈ N.edges, e.Nonconstant) :
    ∀ e ∈ (N.reduce hp).edges, e.EndpointPositive := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  exact (hE f hf).reduce_endpointPositive hp

/-- W3's positive reserve, proved directly for actual reduced state sums. -/
theorem Net.reduce_value_pos [Fintype V] (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (hs : 0 < N.scalar)
    (hE : ∀ e ∈ N.edges, e.Nonconstant) : 0 < (N.reduce hp).value true :=
  (N.reduce hp).ordinary_value_pos hp hs (N.reduce_endpointPositive hp hE)

theorem Net.pinnedValue_reduce_pos [Fintype V] (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (hs : 0 < N.scalar)
    (hE : ∀ e ∈ N.edges, e.Nonconstant) (r : V) (A : Slice M (p r)) :
    0 < (N.reduce hp).pinnedValue r A true :=
  (N.reduce hp).pinnedValue_ordinary_pos hp hs (N.reduce_endpointPositive hp hE) r A

end
end CoefficientwiseRigidity.Network
