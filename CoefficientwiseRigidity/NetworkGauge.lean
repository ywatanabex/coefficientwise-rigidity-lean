import CoefficientwiseRigidity.NetworkReserve

/-!
Flatness and ordinary root constants for the ACTUAL gain-list network.
The gauge equation follows the stored convention: the gain acts on the right set.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V : Type*} {p : V → ℕ}

def gaugeState (γ : V → Equiv.Perm (Fin M)) (A : State M p) : State M p :=
  fun v => permuteSlice (γ v) (A v)

def gaugeStateEquiv (γ : V → Equiv.Perm (Fin M)) : Equiv.Perm (State M p) :=
  Equiv.piCongrRight fun v => slicePerm (γ v)

def Net.Flat (N : Net M p) : Prop :=
  ∃ γ : V → Equiv.Perm (Fin M), ∀ e ∈ N.edges, ∀ f ∈ e.kernels,
    ∀ i, f.gain (γ e.right i) = γ e.left i

theorem entry_value_gauge {a b : ℕ} (f : GainEntry M a b)
    (γ δ : Equiv.Perm (Fin M)) (hf : ∀ i, f.gain (δ i) = γ i)
    (A : Slice M a) (B : Slice M b) :
    f.value (permuteSlice γ A) (permuteSlice δ B) = f.ordinary A B := by
  have he : δ.trans f.gain = γ := Equiv.ext hf
  simp only [GainEntry.value, ← permuteSlice_trans, he, overlap_permute]
  rfl

theorem weight_gauge (E : List (Edge M p)) (γ : V → Equiv.Perm (Fin M))
    (hγ : ∀ e ∈ E, ∀ f ∈ e.kernels, ∀ i, f.gain (γ e.right i) = γ e.left i)
    (A : State M p) : weight E false (gaugeState γ A) = weight E true A := by
  unfold weight
  congr 1
  apply List.map_congr_left
  intro e he
  change listValue e.kernels _ _ = listOrdinary e.kernels _ _
  unfold listValue listOrdinary
  congr 1
  apply List.map_congr_left
  intro f hf
  exact entry_value_gauge f _ _ (hγ e he f hf) _ _

theorem Net.Flat.value_eq [Fintype V] {N : Net M p} (hN : N.Flat) :
    N.value false = N.value true := by
  classical
  obtain ⟨γ, hγ⟩ := hN
  unfold Net.value
  congr 1
  symm
  exact Fintype.sum_equiv (gaugeStateEquiv γ) _ _
    (fun A => (weight_gauge N.edges γ hγ A).symm)

theorem Net.pinnedValue_gauge [Fintype V] (N : Net M p)
    (γ : V → Equiv.Perm (Fin M))
    (hγ : ∀ e ∈ N.edges, ∀ f ∈ e.kernels, ∀ i, f.gain (γ e.right i) = γ e.left i)
    (r : V) (A : Slice M (p r)) :
    N.pinnedValue r (permuteSlice (γ r) A) false = N.pinnedValue r A true := by
  classical
  unfold Net.pinnedValue
  congr 1
  symm
  apply Fintype.sum_equiv (gaugeStateEquiv γ)
  intro S
  have he : gaugeState γ S r = permuteSlice (γ r) A ↔ S r = A :=
    (slicePerm (γ r)).injective.eq_iff
  change (if S r = A then _ else _) =
    (if gaugeState γ S r = permuteSlice (γ r) A then _ else _)
  simp only [he]
  split_ifs
  · exact (weight_gauge N.edges γ hγ S).symm
  · rfl

/-- Every gained pin of a flat component equals its ordinary root constant. -/
theorem Net.Flat.pinnedValue_eq [Fintype V] {N : Net M p} (hN : N.Flat)
    (r : V) (A B : Slice M (p r)) : N.pinnedValue r A false = N.pinnedValue r B true := by
  obtain ⟨γ, hγ⟩ := hN
  let A' := permuteSlice (γ r).symm A
  have he : permuteSlice (γ r) A' = A := by
    simp [A', ← permuteSlice_trans]
  rw [← he, N.pinnedValue_gauge γ hγ r A']
  exact N.pinnedValue_ordinary_constant r A' B

end
end CoefficientwiseRigidity.Network
