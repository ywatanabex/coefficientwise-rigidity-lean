import CoefficientwiseRigidity.Networks

/-! Vertex renaming and orientation changes preserve both actual network values. -/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M : ℕ} {V W : Type*} {p : V → ℕ}

def renameState (e : V ≃ W) (A : State M p) : State M (p ∘ e.symm) := fun w => A (e.symm w)

def stateRenameEquiv (e : V ≃ W) : State M p ≃ State M (p ∘ e.symm) :=
  Equiv.piCongrLeft' (fun v => Slice M (p v)) e

def renameEntry (e : V ≃ W) (u v : V) (f : GainEntry M (p u) (p v)) :
    GainEntry M ((p ∘ e.symm) (e u)) ((p ∘ e.symm) (e v)) where
  profile := f.profile
  cone := by simpa using f.cone
  gain := f.gain

def Edge.rename (e : V ≃ W) (f : Edge M p) : Edge M (p ∘ e.symm) :=
  ⟨e f.left, e f.right, fun h => f.distinct (e.injective h),
    f.kernels.map (renameEntry e f.left f.right)⟩

theorem renameEntry_value (e : V ≃ W) (u v : V) (f : GainEntry M (p u) (p v)) (A : State M p) :
    (renameEntry e u v f).value (renameState e A (e u)) (renameState e A (e v)) = f.value (A u) (A v) := by
  have hA (w : V) : (A (e.symm (e w))).val = (A w).val :=
    congrArg (fun x => (A x).val) (e.symm_apply_apply w)
  simp [renameEntry, GainEntry.value, overlap, permuteSlice, renameState, hA]

theorem renameEntry_ordinary (e : V ≃ W) (u v : V) (f : GainEntry M (p u) (p v)) (A : State M p) :
    (renameEntry e u v f).ordinary (renameState e A (e u)) (renameState e A (e v)) = f.ordinary (A u) (A v) := by
  have hA (w : V) : (A (e.symm (e w))).val = (A w).val :=
    congrArg (fun x => (A x).val) (e.symm_apply_apply w)
  simp [renameEntry, GainEntry.ordinary, overlap, renameState, hA]

theorem Edge.rename_eval (e : V ≃ W) (f : Edge M p) (b : Bool) (A : State M p) :
    (f.rename e).eval b (renameState e A) = f.eval b A := by
  cases b <;> simp [Edge.rename, Edge.eval, kernel, listValue, listOrdinary, Function.comp_def,
    renameEntry_value, renameEntry_ordinary]

def Net.rename (e : V ≃ W) (N : Net M p) : Net M (p ∘ e.symm) :=
  ⟨N.scalar, N.scalar_nonneg, N.edges.map (Edge.rename e)⟩

theorem weight_rename (e : V ≃ W) (E : List (Edge M p)) (b : Bool) (A : State M p) :
    weight (E.map (Edge.rename e)) b (renameState e A) = weight E b A := by
  simp [weight, Function.comp_def, Edge.rename_eval]

theorem Net.rename_value [Fintype V] [Fintype W] (e : V ≃ W) (N : Net M p) (b : Bool) :
    (N.rename e).value b = N.value b := by
  classical
  unfold Net.value
  change N.scalar * (∑ A, weight (N.edges.map (Edge.rename e)) b A) = _
  congr 1
  symm
  apply Fintype.sum_equiv (stateRenameEquiv e)
  intro A
  exact (weight_rename e N.edges b A).symm

end
end CoefficientwiseRigidity.Network
