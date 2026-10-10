import CoefficientwiseRigidity.StarCyclePaths

/-! Chordal bipartiteness is preserved by the actual star contraction. -/
namespace CoefficientwiseRigidity.Star
open Structure
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V} {u : V}

theorem cycleAdjacent_add {n : ℕ} [NeZero n] (i j : Fin n) :
    CycleAdjacent i j ↔ i + 1 = j ∨ j + 1 = i := by
  simp only [CycleAdjacent,Fin.ext_iff,Fin.val_add,Fin.val_one',Nat.add_mod_mod]

theorem cycleAdjacent_shift {n : ℕ} [NeZero n] (k i j : Fin n) :
    CycleAdjacent (i + k) (j + k) ↔ CycleAdjacent i j := by
  rw [cycleAdjacent_add,cycleAdjacent_add]
  rw [add_right_comm i k 1,add_right_comm j k 1]
  simp only [add_left_inj]

theorem no_cycle_avoiding_none (hg : ChordalBipartite G) {n : ℕ} (hn : 6 ≤ n)
    (f : Fin n → Vertex G u) (hf : Function.Injective f)
    (he : ∀ i j, (graph G u).Adj (f i) (f j) ↔ CycleAdjacent i j)
    (hnone : ∀ i, f i ≠ none) : False := by
  have hex (i : Fin n) : ∃ v : Outside G u, f i = some v := by
    cases h : f i with
    | none => exact (hnone i h).elim
    | some v => exact ⟨v,rfl⟩
  let c (i : Fin n) : Outside G u := Classical.choose (hex i)
  have hc (i : Fin n) : f i = some (c i) := Classical.choose_spec (hex i)
  apply hg.2 n hn
  refine ⟨fun i => (c i).val,?_,?_⟩
  · intro i j hij
    apply hf
    rw [hc i,hc j,Subtype.ext hij]
  · intro i j
    have h := he i j
    rw [hc i,hc j,graph_some] at h
    exact h

theorem no_cycle_at_none (b : Bipartition G) (hu : b.side u = true) (hg : ChordalBipartite G)
    (n : ℕ) (f : Fin (n + 6) → Vertex G u) (hf : Function.Injective f)
    (he : ∀ i j, (graph G u).Adj (f i) (f j) ↔ CycleAdjacent i j) (hzero : f 0 = none) : False := by
  have hex (i : Fin (n + 5)) : ∃ v : Outside G u, f ⟨i.val + 1,by omega⟩ = some v := by
    cases h : f ⟨i.val + 1,by omega⟩ with
    | none =>
      have hi := hf (h.trans hzero.symm)
      have hh := congrArg Fin.val hi
      simp only [Fin.val_mk,Fin.val_zero] at hh
      omega
    | some v => exact ⟨v,rfl⟩
  let c (i : Fin (n + 5)) : Outside G u := Classical.choose (hex i)
  have hc (i : Fin (n + 5)) : f ⟨i.val + 1,by omega⟩ = some (c i) := Classical.choose_spec (hex i)
  let p : InducedPath G (c 0).val (c ⟨n + 4,by omega⟩).val := {
    length := n + 4
    vertex := fun i => (c i).val
    first := rfl
    last := rfl
    injective := by
      intro i j hij
      have hh : f ⟨i.val + 1,by omega⟩ = f ⟨j.val + 1,by omega⟩ := by
        rw [hc i,hc j,Subtype.ext hij]
      have hi := congrArg Fin.val (hf hh)
      exact Fin.ext (by simpa using hi)
    adj_iff := by
      intro i j
      have h := he ⟨i.val + 1,by omega⟩ ⟨j.val + 1,by omega⟩
      rw [hc i,hc j,graph_some] at h
      rw [h,cycleAdjacent_linear]
      have hi := i.isLt
      have hj := j.isLt
      simp only [Fin.val_mk]
      omega }
  apply no_outside_path b hu hg p (by dsimp [p]; omega)
  · intro i
    exact (c i).property
  · intro i hi hin w hw hadj
    change i.val < n + 4 at hin
    have hedge : (graph G u).Adj (f 0) (f ⟨i.val + 1,by omega⟩) := by
      rw [hzero,hc i]
      exact ⟨w,hw,G.symm hadj⟩
    have hcycle := (he _ _).mp hedge
    rw [cycleAdjacent_linear] at hcycle
    simp only [Fin.val_zero,Fin.val_mk] at hcycle
    omega
  · have hh : CycleAdjacent (0 : Fin (n + 6)) ⟨1,by omega⟩ := by
      rw [cycleAdjacent_linear]; exact Or.inl rfl
    have h := (he _ _).mpr hh
    have hc0 : f ⟨1,by omega⟩ = some (c 0) := by simpa using hc 0
    rw [hzero,hc0] at h
    exact h
  · have hh : CycleAdjacent (0 : Fin (n + 6)) ⟨n + 5,by omega⟩ := by
      rw [cycleAdjacent_linear]; exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))
    have h := (he _ _).mpr hh
    rw [hzero,hc ⟨n + 4,by omega⟩] at h
    exact h

theorem chordalBipartite (b : Bipartition G) (u : V) (hu : b.side u = true)
    (hg : ChordalBipartite G) : ChordalBipartite (graph G u) := by
  refine ⟨⟨bipartition b u hu⟩,?_⟩
  intro n hn
  rintro ⟨f,hf,he⟩
  by_cases hz : ∃ k, f k = none
  · obtain ⟨k,hk⟩ := hz
    letI : NeZero n := ⟨by omega⟩
    have hf' : Function.Injective (fun i => f (i + k)) := hf.comp (fun _ _ h => add_right_cancel h)
    have he' (i j : Fin n) : (graph G u).Adj (f (i + k)) (f (j + k)) ↔ CycleAdjacent i j :=
      (he _ _).trans (cycleAdjacent_shift k i j)
    have hzero : f ((0 : Fin n) + k) = none := by simpa using hk
    obtain ⟨m,rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6,by omega⟩
    exact no_cycle_at_none b hu hg m (fun i => f (i + k)) hf' he' hzero
  · exact no_cycle_avoiding_none hg hn f hf he (by simpa using hz)

end
end CoefficientwiseRigidity.Star
