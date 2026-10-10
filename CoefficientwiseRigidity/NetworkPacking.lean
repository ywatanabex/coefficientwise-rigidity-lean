import CoefficientwiseRigidity.Elimination
import CoefficientwiseRigidity.NetworkGraph

/-!
Collect actual incident factors into gain lists. Every parallel merge raises
the gained value and preserves the ordinary companion exactly. Empty groups
have the constant-one kernel, not the empty (zero) gain list.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M m : ℕ} {V : Type} {p : V → ℕ}

/-- Simultaneous gained bound and exact ordinary companion. -/
def CompanionBound (f g : Bool → ℚ) : Prop := f false ≤ g false ∧ f true = g true

theorem CompanionBound.refl (f : Bool → ℚ) : CompanionBound f f := ⟨le_rfl, rfl⟩

theorem CompanionBound.trans {f g h : Bool → ℚ} (hfg : CompanionBound f g)
    (hgh : CompanionBound g h) : CompanionBound f h :=
  ⟨hfg.1.trans hgh.1, hfg.2.trans hgh.2⟩

theorem CompanionBound.mul_left {f g : Bool → ℚ} (h : CompanionBound f g)
    (k : Bool → ℚ) (hk : 0 ≤ k false) :
    CompanionBound (fun b => k b * f b) (fun b => k b * g b) :=
  ⟨mul_le_mul_of_nonneg_left h.1 hk, congrArg (k true * ·) h.2⟩

theorem CompanionBound.mul_right {f g : Bool → ℚ} (h : CompanionBound f g)
    (k : Bool → ℚ) (hk : 0 ≤ k false) :
    CompanionBound (fun b => f b * k b) (fun b => g b * k b) := by
  simpa only [mul_comm] using h.mul_left k hk

def unitList (M a b : ℕ) : GainList M a b :=
  [⟨fun _ => 1, newtonCone_const _ _ zero_le_one, Equiv.refl _⟩]

@[simp] theorem kernel_unitList {a b : ℕ} (o : Bool) (A : Slice M a) (B : Slice M b) :
    kernel o (unitList M a b) A B = 1 := by
  cases o <;> simp [kernel, unitList, listValue, listOrdinary, GainEntry.value, GainEntry.ordinary]

theorem kernel_parallel_bound {a b : ℕ} (L K : GainList M a b) (A : Slice M a) (B : Slice M b) :
    CompanionBound (fun o => kernel o L A B * kernel o K A B)
      (fun o => kernel o (parallelLists L K) A B) :=
  ⟨parallelLists_bound L K A B, (parallelLists_ordinary L K A B).symm⟩

@[simp] theorem kernel_reverse {a b : ℕ} (L : GainList M a b)
    (o : Bool) (A : Slice M a) (B : Slice M b) :
    kernel o (reverseList L) B A = kernel o L A B := by
  cases o <;> simp [kernel]

/-- One concrete gain list for each chosen neighbour, in a fixed list order. -/
inductive Spokes (M : ℕ) (p : V → ℕ) (m : ℕ) : List V → Type where
  | nil : Spokes M p m []
  | cons {S : List V} (u : V) (L : GainList M (p u) m) (K : Spokes M p m S) :
      Spokes M p m (u :: S)

def Spokes.value {S : List V} (K : Spokes M p m S) (b : Bool)
    (A : State M p) (C : Slice M m) : ℚ :=
  match K with
  | .nil => 1
  | .cons u L K => kernel b L (A u) C * K.value b A C

theorem Spokes.value_nonneg {S : List V} (K : Spokes M p m S)
    (b : Bool) (A : State M p) (C : Slice M m) : 0 ≤ K.value b A C := by
  induction K with
  | nil => exact zero_le_one
  | cons u L K ih => exact mul_nonneg (kernel_nonneg b L _ _) ih

def Spokes.unit (S : List V) : Spokes M p m S :=
  match S with
  | [] => .nil
  | u :: S => .cons u (unitList M (p u) m) (unit S)

@[simp] theorem Spokes.unit_value (S : List V) (b : Bool) (A : State M p) (C : Slice M m) :
    (Spokes.unit S).value b A C = 1 := by
  induction S with
  | nil => rfl
  | cons u S ih => simp [unit, value, ih]

/-- Insert one incident factor into its neighbour's group using K3. -/
theorem Spokes.merge {S : List V} (K : Spokes M p m S) {u : V}
    (hu : u ∈ S) (L : GainList M (p u) m) :
    ∃ K' : Spokes M p m S, ∀ (A : State M p) (C : Slice M m),
      CompanionBound (fun b => kernel b L (A u) C * K.value b A C)
        (fun b => K'.value b A C) := by
  induction K with
  | nil => simp at hu
  | @cons S w J K ih =>
    rcases List.mem_cons.mp hu with he | hu
    · subst w
      refine ⟨.cons u (parallelLists L J) K, ?_⟩
      intro A C
      simpa only [value, mul_assoc] using
        (kernel_parallel_bound L J (A u) C).mul_right
          (fun b => K.value b A C) (K.value_nonneg false A C)
    · obtain ⟨K',hK'⟩ := ih hu
      refine ⟨.cons w J K', ?_⟩
      intro A C
      simpa only [value, mul_left_comm] using
        (hK' A C).mul_left (fun b => kernel b J (A w) C) (kernel_nonneg false J _ _)

/-- Add these actual spoke factors to a residual network. -/
def Net.attachSpokes (N : Net M p) (m : ℕ) {S : List V} (K : Spokes M p m S) :
    Net M (extendRanks m p) :=
  match K with
  | .nil => N.lift m
  | .cons u L K => (N.attachSpokes m K).addEdge (some u) none (by simp) L

@[simp] theorem Net.attachSpokes_scalar (N : Net M p) {S : List V} (K : Spokes M p m S) :
    (N.attachSpokes m K).scalar = N.scalar := by
  induction K with
  | nil => rfl
  | cons u L K ih => exact ih

theorem weight_attachSpokes (N : Net M p) {S : List V} (K : Spokes M p m S)
    (b : Bool) (A : State M p) (C : Slice M m) :
    weight (N.attachSpokes m K).edges b (extendState m A C) =
      weight N.edges b A * K.value b A C := by
  induction K with
  | nil => simp [Net.attachSpokes, Net.lift, Spokes.value]
  | cons u L K ih =>
    simpa [Net.attachSpokes, Net.addEdge, weight_cons, Edge.eval,
      extendState, Spokes.value, mul_left_comm, mul_comm, mul_assoc] using
      congrArg (kernel b L (A u) C * ·) ih

/-- Packing retains all factors away from the removed vertex, with their
original graph support. Incident factors are merged, never discarded. -/
theorem pack_edges (H : SimpleGraph (Option V)) (S : List V)
    (hS : ∀ u, H.Adj none (some u) → u ∈ S)
    (E : List (Edge M (extendRanks m p)))
    (hE : ∀ e ∈ E, H.Adj e.left e.right) :
    ∃ (R : List (Edge M p)) (K : Spokes M p m S),
      (∀ e ∈ R, H.Adj (some e.left) (some e.right)) ∧
      ∀ (A : State M p) (C : Slice M m),
        CompanionBound (fun b => weight E b (extendState m A C))
          (fun b => weight R b A * K.value b A C) := by
  induction E with
  | nil =>
    refine ⟨[], Spokes.unit S, by simp, ?_⟩
    intro A C
    simp only [weight_nil, Spokes.unit_value, mul_one]
    exact CompanionBound.refl _
  | cons e E ih =>
    obtain ⟨R,K,hR,hK⟩ := ih (fun f hf => hE f (List.mem_cons_of_mem e hf))
    have he := hE e (List.mem_cons_self _ _)
    rcases e with ⟨l,r,hd,L⟩
    cases l with
    | none =>
      cases r with
      | none => exact False.elim (hd rfl)
      | some u =>
        obtain ⟨K',hK'⟩ := K.merge (hS u he) (reverseList L)
        refine ⟨R,K',hR,?_⟩
        intro A C
        have h1 := (hK A C).mul_left (fun b => kernel b L C (A u)) (kernel_nonneg false L _ _)
        have h2 := (hK' A C).mul_left (fun b => weight R b A) (weight_nonneg R false A)
        apply h1.trans
        simpa only [kernel_reverse, mul_left_comm] using h2
    | some u =>
      cases r with
      | none =>
        obtain ⟨K',hK'⟩ := K.merge (hS u he.symm) L
        refine ⟨R,K',hR,?_⟩
        intro A C
        have h1 := (hK A C).mul_left (fun b => kernel b L (A u) C) (kernel_nonneg false L _ _)
        have h2 := (hK' A C).mul_left (fun b => weight R b A) (weight_nonneg R false A)
        apply h1.trans
        simpa only [mul_left_comm] using h2
      | some w =>
        let f : Edge M p := ⟨u,w,fun h => hd (congrArg some h),L⟩
        refine ⟨f :: R,K,?_,?_⟩
        · intro e he'
          rcases List.mem_cons.mp he' with rfl | he'
          · exact he
          · exact hR e he'
        · intro A C
          simpa only [weight_cons, Edge.eval, extendState, mul_assoc] using
            (hK A C).mul_left (fun b => f.eval b A) (kernel_nonneg false L _ _)

theorem Net.pack [Fintype V] (N : Net M (extendRanks m p))
    (H : SimpleGraph (Option V)) (S : List V)
    (hS : ∀ u, H.Adj none (some u) → u ∈ S)
    (hE : ∀ e ∈ N.edges, H.Adj e.left e.right) :
    ∃ (R : Net M p) (K : Spokes M p m S),
      (∀ e ∈ R.edges, H.Adj (some e.left) (some e.right)) ∧
      CompanionBound N.value (R.attachSpokes m K).value := by
  classical
  obtain ⟨R,K,hR,hK⟩ := pack_edges H S hS N.edges hE
  refine ⟨⟨N.scalar,N.scalar_nonneg,R⟩,K,hR,?_,?_⟩
  · unfold Net.value
    rw [Net.attachSpokes_scalar]
    rw [sum_extendState, sum_extendState]
    apply mul_le_mul_of_nonneg_left _ N.scalar_nonneg
    apply Finset.sum_le_sum
    intro A _
    apply Finset.sum_le_sum
    intro C _
    simpa only [weight_attachSpokes] using (hK A C).1
  · unfold Net.value
    rw [Net.attachSpokes_scalar]
    rw [sum_extendState, sum_extendState]
    congr 1
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro C _
    simpa only [weight_attachSpokes] using (hK A C).2

end
end CoefficientwiseRigidity.Network
