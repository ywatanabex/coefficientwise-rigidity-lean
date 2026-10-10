import CoefficientwiseRigidity.SerialClosure
import CoefficientwiseRigidity.NewtonSplit

/-!
Concrete K4 data: finite lists of cone functions with label permutations.
The ordinary companion is computed from the chosen list, not inferred from
the gained matrix. Local operations below have kernel-checked proofs.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset
variable {M p m q : ℕ}

def permuteSlice (σ : Equiv.Perm (Fin M)) (A : Slice M p) : Slice M p :=
  ⟨A.val.map σ.toEmbedding, by simp [A.property]⟩

@[simp] theorem permuteSlice_refl (A : Slice M p) :
    permuteSlice (Equiv.refl _) A = A := by
  apply Subtype.ext
  simp [permuteSlice]

@[simp] theorem permuteSlice_trans (σ τ : Equiv.Perm (Fin M)) (A : Slice M p) :
    permuteSlice (σ.trans τ) A = permuteSlice τ (permuteSlice σ A) := by
  apply Subtype.ext
  simp [permuteSlice, Finset.map_map]

def slicePerm (σ : Equiv.Perm (Fin M)) : Equiv.Perm (Slice M p) where
  toFun := permuteSlice σ
  invFun := permuteSlice σ.symm
  left_inv A := by rw [← permuteSlice_trans]; simp
  right_inv A := by rw [← permuteSlice_trans]; simp

theorem overlap_permute (σ : Equiv.Perm (Fin M)) (A : Slice M p) (B : Slice M q) :
    overlap (permuteSlice σ A) (permuteSlice σ B) = overlap A B := by
  simp only [overlap, permuteSlice, ← Finset.map_inter, Finset.card_map]

theorem overlap_permute_right (σ : Equiv.Perm (Fin M)) (A : Slice M p) (B : Slice M q) :
    overlap A (permuteSlice σ B) = overlap B (permuteSlice σ.symm A) := by
  rw [← overlap_permute σ.symm A (permuteSlice σ B), ← permuteSlice_trans]
  simp only [Equiv.self_trans_symm, permuteSlice_refl]
  exact overlap_symm _ _

theorem overlapRank_symm (M p q : ℕ) : overlapRank M p q = overlapRank M q p := by
  simp only [overlapRank, overlapShift, min_comm, Nat.add_comm]

/-- A list entry retains its cone certificate and its actual gain. -/
structure GainEntry (M p q : ℕ) where
  profile : ℕ → ℚ
  cone : NewtonCone (overlapRank M p q) profile
  gain : Equiv.Perm (Fin M)

def GainEntry.value (e : GainEntry M p q) (A : Slice M p) (B : Slice M q) : ℚ :=
  e.profile (overlap A (permuteSlice e.gain B))

def GainEntry.ordinary (e : GainEntry M p q) (A : Slice M p) (B : Slice M q) : ℚ :=
  e.profile (overlap A B)

theorem GainEntry.value_nonneg (e : GainEntry M p q) (A : Slice M p) (B : Slice M q) :
    0 ≤ e.value A B := newtonCone_nonneg e.cone (overlap_le_rank _ _)

theorem GainEntry.ordinary_nonneg (e : GainEntry M p q) (A : Slice M p) (B : Slice M q) :
    0 ≤ e.ordinary A B := newtonCone_nonneg e.cone (overlap_le_rank _ _)

def GainEntry.reverse (e : GainEntry M p q) : GainEntry M q p where
  profile := e.profile
  cone := by rw [← overlapRank_symm]; exact e.cone
  gain := e.gain.symm

@[simp] theorem GainEntry.reverse_value (e : GainEntry M p q) (A : Slice M p) (B : Slice M q) :
    e.reverse.value B A = e.value A B := by
  exact congrArg e.profile (overlap_permute_right e.gain A B).symm

@[simp] theorem GainEntry.reverse_ordinary (e : GainEntry M p q) (A : Slice M p) (B : Slice M q) :
    e.reverse.ordinary B A = e.ordinary A B := congrArg e.profile (overlap_symm B A)

noncomputable def GainEntry.compose (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (e : GainEntry M p m) (f : GainEntry M m q) : GainEntry M p q where
  profile := Classical.choose (serial_newton_closure M p m q hp hm hq e.profile f.profile e.cone f.cone)
  cone := (Classical.choose_spec (serial_newton_closure M p m q hp hm hq e.profile f.profile e.cone f.cone)).1
  gain := f.gain.trans e.gain

theorem GainEntry.compose_ordinary (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (e : GainEntry M p m) (f : GainEntry M m q) (A : Slice M p) (B : Slice M q) :
    (e.compose hp hm hq f).ordinary A B = ∑ C : Slice M m, e.ordinary A C * f.ordinary C B := by
  exact ((Classical.choose_spec (serial_newton_closure M p m q hp hm hq
    e.profile f.profile e.cone f.cone)).2 A B).symm

theorem GainEntry.compose_value (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (e : GainEntry M p m) (f : GainEntry M m q) (A : Slice M p) (B : Slice M q) :
    (e.compose hp hm hq f).value A B = ∑ C : Slice M m, e.value A C * f.value C B := by
  change (e.compose hp hm hq f).ordinary A (permuteSlice (f.gain.trans e.gain) B) = _
  rw [e.compose_ordinary hp hm hq, permuteSlice_trans]
  symm
  apply Fintype.sum_equiv (slicePerm e.gain)
  intro C
  simp only [GainEntry.value, GainEntry.ordinary, slicePerm, Equiv.coe_fn_mk, overlap_permute]

def GainEntry.splitLeft (e f : GainEntry M p q) : GainEntry M p q where
  profile := splitF e.profile f.profile
  cone := newtonCone_splitF e.cone f.cone
  gain := e.gain

def GainEntry.splitRight (e f : GainEntry M p q) : GainEntry M p q where
  profile := splitG e.profile f.profile
  cone := newtonCone_splitG e.cone f.cone
  gain := f.gain

theorem GainEntry.parallel_bound (e f : GainEntry M p q) (A : Slice M p) (B : Slice M q) :
    e.value A B * f.value A B ≤ (e.splitLeft f).value A B + (e.splitRight f).value A B :=
  newton_split_bound e.cone f.cone (overlap_le_rank _ _) (overlap_le_rank _ _)

theorem GainEntry.parallel_ordinary (e f : GainEntry M p q) (A : Slice M p) (B : Slice M q) :
    (e.splitLeft f).ordinary A B + (e.splitRight f).ordinary A B = e.ordinary A B * f.ordinary A B :=
  split_diagonal e.profile f.profile _

abbrev GainList (M p q : ℕ) := List (GainEntry M p q)

def listValue (L : GainList M p q) (A : Slice M p) (B : Slice M q) : ℚ :=
  (L.map fun e => e.value A B).sum

def listOrdinary (L : GainList M p q) (A : Slice M p) (B : Slice M q) : ℚ :=
  (L.map fun e => e.ordinary A B).sum

@[simp] theorem listValue_nil (A : Slice M p) (B : Slice M q) : listValue [] A B = 0 := rfl
@[simp] theorem listOrdinary_nil (A : Slice M p) (B : Slice M q) : listOrdinary [] A B = 0 := rfl
@[simp] theorem listValue_cons (e : GainEntry M p q) (L : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listValue (e :: L) A B = e.value A B + listValue L A B := rfl
@[simp] theorem listOrdinary_cons (e : GainEntry M p q) (L : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listOrdinary (e :: L) A B = e.ordinary A B + listOrdinary L A B := rfl

@[simp] theorem listValue_append (L K : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listValue (L ++ K) A B = listValue L A B + listValue K A B := by simp [listValue]
@[simp] theorem listOrdinary_append (L K : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listOrdinary (L ++ K) A B = listOrdinary L A B + listOrdinary K A B := by simp [listOrdinary]

theorem listValue_nonneg (L : GainList M p q) (A : Slice M p) (B : Slice M q) : 0 ≤ listValue L A B := by
  induction L with
  | nil => exact le_refl 0
  | cons e L ih => exact add_nonneg (e.value_nonneg A B) ih

theorem listOrdinary_nonneg (L : GainList M p q) (A : Slice M p) (B : Slice M q) : 0 ≤ listOrdinary L A B := by
  induction L with
  | nil => exact le_refl 0
  | cons e L ih => exact add_nonneg (e.ordinary_nonneg A B) ih

noncomputable def serialLists (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (L : GainList M p m) (K : GainList M m q) : GainList M p q :=
  L.flatMap fun e => K.map fun f => e.compose hp hm hq f

def parallelLists (L K : GainList M p q) : GainList M p q :=
  L.flatMap fun e => K.flatMap fun f => [e.splitLeft f, e.splitRight f]

theorem serialLists_value (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (L : GainList M p m) (K : GainList M m q) (A : Slice M p) (B : Slice M q) :
    listValue (serialLists hp hm hq L K) A B =
      ∑ C : Slice M m, listValue L A C * listValue K C B := by
  induction L with
  | nil => simp [serialLists]
  | cons e L ih =>
    simp only [serialLists, List.flatMap_cons, listValue_append, listValue_cons,
      add_mul, Finset.sum_add_distrib] at *
    rw [ih]
    congr 1
    clear ih
    induction K with
    | nil => simp
    | cons f K ihK =>
      simp only [List.map_cons, listValue_cons, mul_add, Finset.sum_add_distrib]
      rw [e.compose_value hp hm hq, ihK]

theorem serialLists_ordinary (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (L : GainList M p m) (K : GainList M m q) (A : Slice M p) (B : Slice M q) :
    listOrdinary (serialLists hp hm hq L K) A B =
      ∑ C : Slice M m, listOrdinary L A C * listOrdinary K C B := by
  induction L with
  | nil => simp [serialLists]
  | cons e L ih =>
    simp only [serialLists, List.flatMap_cons, listOrdinary_append, listOrdinary_cons,
      add_mul, Finset.sum_add_distrib] at *
    rw [ih]
    congr 1
    clear ih
    induction K with
    | nil => simp
    | cons f K ihK =>
      simp only [List.map_cons, listOrdinary_cons, mul_add, Finset.sum_add_distrib]
      rw [e.compose_ordinary hp hm hq, ihK]

theorem parallelLists_bound (L K : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listValue L A B * listValue K A B ≤ listValue (parallelLists L K) A B := by
  induction L with
  | nil => simp [parallelLists]
  | cons e L ih =>
    simp only [parallelLists, List.flatMap_cons, listValue_append, listValue_cons, add_mul] at *
    apply add_le_add _ ih
    clear ih
    induction K with
    | nil => simp
    | cons f K ihK =>
      simp only [List.flatMap_cons, listValue_append, listValue_cons, listValue_nil, add_zero, mul_add]
      exact add_le_add (e.parallel_bound f A B) ihK

theorem parallelLists_ordinary (L K : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listOrdinary (parallelLists L K) A B = listOrdinary L A B * listOrdinary K A B := by
  induction L with
  | nil => simp [parallelLists]
  | cons e L ih =>
    simp only [parallelLists, List.flatMap_cons, listOrdinary_append, listOrdinary_cons, add_mul] at *
    rw [ih]
    congr 1
    clear ih
    induction K with
    | nil => simp
    | cons f K ihK =>
      simp only [List.flatMap_cons, listOrdinary_append, listOrdinary_cons, listOrdinary_nil, add_zero, mul_add]
      rw [e.parallel_ordinary f, ihK]

def reverseList (L : GainList M p q) : GainList M q p := L.map GainEntry.reverse

@[simp] theorem reverseList_value (L : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listValue (reverseList L) B A = listValue L A B := by
  simp [reverseList, listValue, Function.comp_def]

@[simp] theorem reverseList_ordinary (L : GainList M p q) (A : Slice M p) (B : Slice M q) :
    listOrdinary (reverseList L) B A = listOrdinary L A B := by
  simp [reverseList, listOrdinary, Function.comp_def]

theorem GainEntry.row_sum (e : GainEntry M p q) (A : Slice M p) :
    (∑ B : Slice M q, e.value A B) = ∑ B : Slice M q, e.ordinary A B := by
  apply Fintype.sum_equiv (slicePerm e.gain)
  intro B
  rfl

theorem GainEntry.ordinary_row_constant (e : GainEntry M p q) (A A' : Slice M p) :
    (∑ B : Slice M q, e.ordinary A B) = ∑ B : Slice M q, e.ordinary A' B := by
  let E : Slice M 0 := ⟨∅, rfl⟩
  have h := serial_radial (m := q) e.profile (fun _ => 1) A A' E E
    (by simp [overlap_zero_right])
  simpa [serial, GainEntry.ordinary] using h

theorem list_row_sum (L : GainList M p q) (A : Slice M p) :
    (∑ B : Slice M q, listValue L A B) = ∑ B : Slice M q, listOrdinary L A B := by
  induction L with
  | nil => simp
  | cons e L ih => simp only [listValue_cons, listOrdinary_cons, Finset.sum_add_distrib, e.row_sum, ih]

theorem list_ordinary_row_constant (L : GainList M p q) (A A' : Slice M p) :
    (∑ B : Slice M q, listOrdinary L A B) = ∑ B : Slice M q, listOrdinary L A' B := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [listOrdinary_cons, Finset.sum_add_distrib, e.ordinary_row_constant A A', ih]

def rowMass (hp : p ≤ M) (L : GainList M p q) : ℚ :=
  ∑ B : Slice M q, listOrdinary L ⟨initialSegment M p, card_prefix M p hp⟩ B

theorem rowMass_nonneg (hp : p ≤ M) (L : GainList M p q) : 0 ≤ rowMass hp L :=
  Finset.sum_nonneg fun B _ => listOrdinary_nonneg L _ B

theorem list_value_rowMass (hp : p ≤ M) (L : GainList M p q) (A : Slice M p) :
    (∑ B : Slice M q, listValue L A B) = rowMass hp L := by
  rw [list_row_sum]
  exact list_ordinary_row_constant L A _

theorem list_ordinary_rowMass (hp : p ≤ M) (L : GainList M p q) (A : Slice M p) :
    (∑ B : Slice M q, listOrdinary L A B) = rowMass hp L :=
  list_ordinary_row_constant L A _

end CoefficientwiseRigidity.Kernel
