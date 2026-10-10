import CoefficientwiseRigidity.BoundaryAmplification
import CoefficientwiseRigidity.StarChordal

/-! Induced cycles in copies sharing a clique stay within one original copy. -/
namespace CoefficientwiseRigidity.Replica
open Structure
open scoped Classical
noncomputable section

private theorem labels_at_none {I : Type} (n : ℕ) (c : Fin (n + 6) → Option I)
    (hzero : c 0 = none)
    (hboundary : ∀ i j, c i = none → c j = none → i ≠ j → CycleAdjacent i j)
    (hedge : ∀ i j, CycleAdjacent i j → ∀ p q, c i = some p → c j = some q → p = q) :
    ∃ p, ∀ i, c i = none ∨ c i = some p := by
  have middle (j : Fin (n + 6)) (hj : 2 ≤ j.val) (hj' : j.val + 1 < n + 6) : c j ≠ none := by
    intro hc
    have he := hboundary 0 j hzero hc (by intro h; have := congrArg Fin.val h; simp at this; omega)
    rw [cycleAdjacent_linear] at he
    simp only [Fin.val_zero] at he
    omega
  obtain ⟨p,hp⟩ : ∃ p, c 2 = some p := by
    cases h : c 2 with
    | none => exact (middle 2 (by simp) (by simp) h).elim
    | some p => exact ⟨p,rfl⟩
  have chain : ∀ k (hk : k + 2 < n + 6), ∀ q, c ⟨k + 2,hk⟩ = some q → q = p := by
    intro k
    induction k with
    | zero =>
      intro hk q hq
      exact Option.some.inj (hq.symm.trans hp)
    | succ k ih =>
      intro hk q hq
      have hprev : k + 2 < n + 6 := by omega
      obtain ⟨r,hr⟩ : ∃ r, c ⟨k + 2,hprev⟩ = some r := by
        cases h : c ⟨k + 2,hprev⟩ with
        | none => exact (middle ⟨k + 2,hprev⟩ (by simp) (by simp; omega) h).elim
        | some r => exact ⟨r,rfl⟩
      have he : CycleAdjacent (⟨k + 2,hprev⟩ : Fin (n + 6)) ⟨k + 1 + 2,hk⟩ := by
        rw [cycleAdjacent_linear]
        exact Or.inl (by simp)
      exact (hedge _ _ he r q hr hq).symm.trans (ih hprev r hr)
  refine ⟨p,?_⟩
  intro j
  cases h : c j with
  | none => exact Or.inl rfl
  | some q =>
    right
    have heq : q = p := by
      by_cases hz : j.val = 0
      · have hj : j = 0 := Fin.ext hz
        have hh := hzero
        rw [← hj,h] at hh
        cases hh
      by_cases ho : j.val = 1
      · have he : CycleAdjacent j (2 : Fin (n + 6)) := by
          rw [cycleAdjacent_linear]
          exact Or.inl (by simp [ho])
        exact hedge j 2 he q p h hp
      · obtain ⟨k,hk⟩ : ∃ k, j.val = k + 2 := ⟨j.val - 2,by omega⟩
        have hlt : k + 2 < n + 6 := by omega
        have hj : j = ⟨k + 2,hlt⟩ := Fin.ext hk
        exact chain k hlt q (hj ▸ h)
    rw [heq]

theorem cycle_labels_constant {I : Type} {n : ℕ} (hn : 6 ≤ n) (c : Fin n → Option I)
    (hboundary : ∀ i j, c i = none → c j = none → i ≠ j → CycleAdjacent i j)
    (hedge : ∀ i j, CycleAdjacent i j → ∀ p q, c i = some p → c j = some q → p = q) :
    ∃ p, ∀ i, c i = none ∨ c i = some p := by
  letI : NeZero n := ⟨by omega⟩
  by_cases hz : ∃ k, c k = none
  · obtain ⟨k,hk⟩ := hz
    have hb i j : c (i + k) = none → c (j + k) = none → i ≠ j → CycleAdjacent i j := by
      intro hi hj hij
      exact (Star.cycleAdjacent_shift k i j).mp
        (hboundary _ _ hi hj (fun h => hij (add_right_cancel h)))
    have he i j (hij : CycleAdjacent i j) p q :
        c (i + k) = some p → c (j + k) = some q → p = q :=
      hedge _ _ ((Star.cycleAdjacent_shift k i j).mpr hij) p q
    have h0 : c ((0 : Fin n) + k) = none := by simpa using hk
    obtain ⟨m,hm⟩ : ∃ m, n = m + 6 := ⟨n - 6,by omega⟩
    subst n
    obtain ⟨p,hp⟩ := labels_at_none m (fun i => c (i + k)) h0 hb he
    refine ⟨p,fun i => ?_⟩
    simpa using hp (i - k)
  · have hsome (j : Fin n) : ∃ p, c j = some p := by
      cases h : c j with
      | none => exact (hz ⟨j,h⟩).elim
      | some p => exact ⟨p,rfl⟩
    obtain ⟨p,hp⟩ := hsome 0
    have chain : ∀ k (hk : k < n), c ⟨k,hk⟩ = some p := by
      intro k
      induction k with
      | zero => intro _; exact hp
      | succ k ih =>
        intro hk
        obtain ⟨q,hq⟩ := hsome ⟨k + 1,hk⟩
        have hprev : k < n := by omega
        have he : CycleAdjacent (⟨k,hprev⟩ : Fin n) ⟨k + 1,hk⟩ := by
          rw [cycleAdjacent_linear]; exact Or.inl rfl
        have hh := hedge _ _ he p q (ih hprev) hq
        simpa [← hh] using hq
    exact ⟨p,fun i => Or.inr (chain i.val i.isLt)⟩

variable {V I : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def copyIndex {S : Finset V} : Vertex S I → Option I
  | .inl _ => none
  | .inr iv => some iv.1

omit [Fintype V] in
theorem boundary_clique {S : Finset V} (hS : BoundaryShape G S)
    (u v : S) (hne : u ≠ v) : G.Adj u.val v.val := by
  rcases hS with he | ⟨w,he⟩ | ⟨x,y,he,hxy⟩
  · have h := u.property; simp [he] at h
  · have hu : u.val = w := by simpa [he] using u.property
    have hv : v.val = w := by simpa [he] using v.property
    exact (hne (Subtype.ext (hu.trans hv.symm))).elim
  · have hu : u.val = x ∨ u.val = y := by simpa [he] using u.property
    have hv : v.val = x ∨ v.val = y := by simpa [he] using v.property
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (hne (Subtype.ext (hu.trans hv.symm))).elim
    · simpa [hu,hv] using hxy
    · simpa [hu,hv] using hxy.symm
    · exact (hne (Subtype.ext (hu.trans hv.symm))).elim

omit [Fintype V] in
theorem chordal (hg : ChordalBipartite G) {S : Finset V} (hS : BoundaryShape G S) :
    ChordalBipartite (graph G S I) := by
  obtain ⟨b⟩ := hg.1
  refine ⟨⟨bipartition b S I⟩,?_⟩
  intro n hn
  rintro ⟨f,hf,he⟩
  have hb i j (hi : copyIndex (f i) = none) (hj : copyIndex (f j) = none) (hne : i ≠ j) :
      CycleAdjacent i j := by
    cases hfi : f i with
    | inr iv => simp [hfi,copyIndex] at hi
    | inl u =>
      cases hfj : f j with
      | inr jv => simp [hfj,copyIndex] at hj
      | inl v =>
        have huv : u ≠ v := by intro h; apply hne; apply hf; rw [hfi,hfj,h]
        apply (he i j).mp
        rw [hfi,hfj]
        exact ⟨boundary_clique hS u v huv,trivial⟩
  have hc i j (hij : CycleAdjacent i j) p q
      (hi : copyIndex (f i) = some p) (hj : copyIndex (f j) = some q) : p = q := by
    have hh := ((he i j).mpr hij).2
    cases hfi : f i with
    | inl u => simp [hfi,copyIndex] at hi
    | inr iv =>
      cases hfj : f j with
      | inl v => simp [hfj,copyIndex] at hj
      | inr jv =>
        simp only [hfi,hfj,SameCopy] at hh
        simp only [hfi,copyIndex,Option.some.injEq] at hi
        simp only [hfj,copyIndex,Option.some.injEq] at hj
        exact hi.symm.trans (hh.trans hj)
  obtain ⟨p,hp⟩ := cycle_labels_constant hn (fun i => copyIndex (f i)) hb hc
  have hrep (i : Fin n) : f i = embed S p (base S (f i)) := by
    have hh := hp i
    cases h : f i with
    | inl v => exact (embed_mem S p v).symm
    | inr iv =>
      have hh' : iv.1 = p := by simpa [h,copyIndex] using hh
      change Sum.inr iv = embed S p iv.2.val
      rw [embed_not_mem]
      exact congrArg Sum.inr (Prod.ext hh' rfl)
  apply hg.2 n hn
  refine ⟨fun i => base S (f i),?_,?_⟩
  · intro i j hij
    apply hf
    rw [hrep i,hrep j]
    exact congrArg (embed S p) hij
  · intro i j
    have hh := he i j
    rw [hrep i,hrep j,embed_adj] at hh
    exact hh

end
end CoefficientwiseRigidity.Replica
