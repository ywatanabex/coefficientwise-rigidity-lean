import CoefficientwiseRigidity.NetworkLowDegree

/-!
The actual forward-difference sum, written independently of a presentation of
the ranks as successors. This is proved equal to `Net.reduce`'s ordinary value.
It lets the same reserve pass through vertex removal without dependent casts.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
open scoped Classical
noncomputable section
variable {M m : ℕ} {V W : Type} {p q : V → ℕ}

def differenceKernel {a b c d : ℕ} (L : GainList (M + 2) a b)
    (A : Slice M c) (B : Slice M d) : ℚ :=
  (L.map fun f => delta f.profile (overlap A B)).sum

def differenceWeight (E : List (Edge (M + 2) p)) (A : State M q) : ℚ :=
  (E.map fun e => differenceKernel e.kernels (A e.left) (A e.right)).prod

@[simp] theorem differenceWeight_nil (A : State M q) :
    differenceWeight ([] : List (Edge (M + 2) p)) A = 1 := rfl

@[simp] theorem differenceWeight_cons (e : Edge (M + 2) p) (E) (A : State M q) :
    differenceWeight (e :: E) A =
      differenceKernel e.kernels (A e.left) (A e.right) * differenceWeight E A := rfl

theorem differenceKernel_reverse {a b c d : ℕ} (L : GainList (M + 2) a b)
    (A : Slice M c) (B : Slice M d) :
    differenceKernel (reverseList L) B A = differenceKernel L A B := by
  simp [differenceKernel, reverseList, Function.comp_def, GainEntry.reverse, overlap_symm B A]

theorem differenceWeight_reduce (E : List (Edge (M + 2) (fun v => p v + 1)))
    (hp : ∀ v, p v ≤ M) (A : State M p) :
    differenceWeight E A = weight (E.map fun e => e.reduce hp) true A := by
  simp [differenceWeight, differenceKernel, weight, Edge.reduce, Edge.eval, kernel,
    reduceList, listOrdinary, GainEntry.reduce, GainEntry.ordinary, Function.comp_def]

def Net.reserveValue [Fintype V] (N : Net (M + 2) p) : ℚ :=
  N.scalar * ∑ A : State M (fun v => p v - 1), differenceWeight N.edges A

theorem Net.reserveValue_eq_reduce [Fintype V]
    (N : Net (M + 2) (fun v => p v + 1)) (hp : ∀ v, p v ≤ M) :
    N.reserveValue = (N.reduce hp).value true := by
  simp only [Net.reserveValue, Nat.add_sub_cancel, Net.value, Net.reduce]
  congr 1
  exact Finset.sum_congr rfl (fun A _ => differenceWeight_reduce N.edges hp A)

theorem EdgeListEquiv.differenceWeight_eq {E F : List (Edge (M + 2) p)}
    (h : EdgeListEquiv E F) (A : State M q) : differenceWeight E A = differenceWeight F A := by
  exact (h.map_perm (fun e => differenceKernel e.kernels (A e.left) (A e.right))
    (fun e => differenceKernel_reverse e.kernels _ _)).prod_eq

theorem Net.reserveValue_exact [Fintype V] (N R : Net (M + 2) p)
    (hc : N.scalar = R.scalar) (he : EdgeListEquiv N.edges R.edges) :
    N.reserveValue = R.reserveValue := by
  unfold Net.reserveValue
  rw [hc]
  congr 1
  exact Finset.sum_congr rfl (fun A _ => he.differenceWeight_eq A)

theorem Net.value_exact [Fintype V] (N R : Net M p) (hc : N.scalar = R.scalar)
    (he : EdgeListEquiv N.edges R.edges) (b : Bool) : N.value b = R.value b := by
  unfold Net.value
  rw [hc]
  congr 1
  exact Finset.sum_congr rfl (fun A _ => he.weight_eq b A)

theorem Net.flat_exact (N R : Net M p) (he : EdgeListEquiv N.edges R.edges) :
    N.Flat ↔ R.Flat := exists_congr (fun γ => he.gauge_iff γ)

theorem Net.reserveValue_changeRanks [Fintype V] (N : Net (M + 2) p) (h : p = q) :
    (N.changeRanks h).reserveValue = N.reserveValue := by cases h; rfl

theorem Net.reserveValue_rename [Fintype V] [Fintype W]
    (N : Net (M + 2) p) (e : V ≃ W) : (N.rename e).reserveValue = N.reserveValue := by
  unfold Net.reserveValue
  change N.scalar * _ = N.scalar * _
  congr 1
  symm
  apply Fintype.sum_equiv (stateRenameEquiv e)
  intro A
  have ha (v : V) : (A (e.symm (e v))).val = (A v).val :=
    congrArg (fun x => (A x).val) (e.symm_apply_apply v)
  simp [differenceWeight, differenceKernel, Net.rename, Edge.rename, renameEntry,
    Function.comp_def, stateRenameEquiv, Equiv.piCongrLeft', overlap, ha]

theorem Net.reserveValue_atVertex [Fintype V] (N : Net (M + 2) p) (v : V) :
    (N.atVertex v).reserveValue = N.reserveValue := by
  rw [Net.atVertex, Net.reserveValue_changeRanks, Net.reserveValue_rename]

theorem ranks_pred_extend (m : ℕ) (p : V → ℕ) :
    (fun w => extendRanks m p w - 1) = extendRanks (m - 1) (fun v => p v - 1) := by
  funext w
  cases w <;> rfl

theorem differenceWeight_lift (E : List (Edge (M + 2) p)) (A : State M q)
    {k : ℕ} (C : Slice M k) :
    differenceWeight (E.map (liftEdge m)) (extendState k A C) = differenceWeight E A := by
  simp [differenceWeight, liftEdge, extendState, Function.comp_def]

theorem Net.reserveValue_lift [Fintype V] (N : Net (M + 2) p) (m : ℕ) :
    (N.lift m).reserveValue = (M.choose (m - 1) : ℚ) * N.reserveValue := by
  unfold Net.reserveValue
  rw [ranks_pred_extend, sum_extendState]
  simp only [Net.lift, differenceWeight_lift, Finset.sum_const, Finset.card_univ,
    slice_card, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem exists_successor_ranks (hp : ∀ v, 0 < p v) : ∃ q : V → ℕ, p = fun v => q v + 1 := by
  refine ⟨fun v => p v - 1, ?_⟩
  funext v
  dsimp only
  have := hp v
  omega

theorem Net.reserveValue_nonneg [Fintype V] (N : Net (M + 2) p)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) : 0 ≤ N.reserveValue := by
  obtain ⟨q,rfl⟩ := exists_successor_ranks (fun v => (hp v).1)
  dsimp only at hp
  rw [N.reserveValue_eq_reduce (fun v => by have := (hp v).2; omega)]
  exact Net.value_nonneg _ true

theorem differenceKernel_reduce {a b : ℕ} (L : GainList (M + 2) (a + 1) (b + 1))
    (ha : a ≤ M) (hb : b ≤ M) (A : Slice M a) (B : Slice M b) :
    differenceKernel L A B = listOrdinary (reduceList L ha hb) A B := by
  simp [differenceKernel, listOrdinary, reduceList, GainEntry.reduce,
    GainEntry.ordinary, Function.comp_def]

/-- The reduced leaf scalar is at most the original scalar. -/
theorem Net.reserveValue_leaf [Fintype V] (N : Net (M + 2) p) (m : ℕ) (u : V)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (hm : 0 < m ∧ m < M + 2)
    (e : GainEntry (M + 2) (p u) m) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ rowMass (Nat.le_of_lt (hp u).2) [e] ∧
      (N.attachLeaf m u [e]).reserveValue = c * N.reserveValue := by
  obtain ⟨q,rfl⟩ := exists_successor_ranks (fun v => (hp v).1)
  dsimp only at hp e
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm.1)
  have hq (v : V) : q v ≤ M := by have := (hp v).2; omega
  have hk : k ≤ M := by omega
  refine ⟨rowMass (hq u) (reduceList [e] (hq u) hk), rowMass_nonneg _ _,
    rowMass_reduce_le [e] (hq u) hk, ?_⟩
  unfold Net.reserveValue
  rw [ranks_pred_extend, sum_extendState]
  simp only [Nat.add_sub_cancel, Nat.succ_sub_one, Net.attachLeaf, Net.addEdge,
    Net.lift, differenceWeight_cons, differenceWeight_lift, extendState]
  simp_rw [differenceKernel_reduce [e] (hq u) hk, ← Finset.sum_mul,
    list_ordinary_rowMass (hq u)]
  rw [← Finset.mul_sum]
  ring

/-- W1 preserves the literal full-network reserve in a serial elimination. -/
theorem Net.reserveValue_series [Fintype V] (N : Net (M + 2) p) (m : ℕ)
    (u v : V) (huv : u ≠ v) (hp : ∀ w, 0 < p w ∧ p w < M + 2)
    (hm : 0 < m ∧ m < M + 2) (e : GainEntry (M + 2) (p u) m)
    (f : GainEntry (M + 2) m (p v)) :
    (N.attachSeries m u v [e] [f]).reserveValue =
      (N.addEdge u v huv [e.compose (Nat.le_of_lt (hp u).2)
        (Nat.le_of_lt hm.2) (Nat.le_of_lt (hp v).2) f]).reserveValue := by
  obtain ⟨q,rfl⟩ := exists_successor_ranks (fun w => (hp w).1)
  dsimp only at hp e f
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm.1)
  have hq (w : V) : q w ≤ M := by have := (hp w).2; omega
  have hk : k ≤ M := by omega
  have he (A : Slice M (q u)) (B : Slice M (q v)) :
      differenceKernel [e.compose (Nat.le_of_lt (hp u).2) (Nat.le_of_lt hm.2)
        (Nat.le_of_lt (hp v).2) f] A B =
        ∑ C : Slice M k, differenceKernel [e] A C * differenceKernel [f] C B := by
    simpa only [differenceKernel, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, GainEntry.reduce, GainEntry.ordinary] using
      e.compose_reduce_ordinary f (hq u) hk (hq v) A B
  unfold Net.reserveValue
  rw [ranks_pred_extend, sum_extendState]
  simp only [Nat.add_sub_cancel, Nat.succ_sub_one, Net.attachSeries, Net.addEdge,
    Net.lift, differenceWeight_cons, differenceWeight_lift, extendState]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← he]

theorem Net.twoSpokes_exact (N : Net M p) (m : ℕ) (u v : V)
    (e : GainEntry M (p u) m) (f : GainEntry M (p v) m) :
    EdgeListEquiv (N.attachSpokes m (.cons u [e] (.cons v [f] .nil))).edges
      (N.attachSeries m u v [e] [f.reverse]).edges :=
  .cons _ (.reverse _ _)

end
end CoefficientwiseRigidity.Network
