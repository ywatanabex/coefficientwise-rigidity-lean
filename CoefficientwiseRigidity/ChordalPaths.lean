import CoefficientwiseRigidity.PrimalChordal

/-! Concrete induced paths, retained inside a specified vertex set. -/
namespace CoefficientwiseRigidity.Structure
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V} {S T : Set V} {a b c : V}

def ReachIn (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  a ∈ S ∧ Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∈ S ∧ y ∈ S) a b

theorem ReachIn.refl (ha : a ∈ S) : ReachIn G S a a := ⟨ha,.refl⟩

theorem ReachIn.end_mem (h : ReachIn G S a b) : b ∈ S := by
  obtain ⟨ha,h⟩ := h
  induction h with
  | refl => exact ha
  | tail _ h _ => exact h.2.2

theorem ReachIn.step (h : ReachIn G S a b) (hbc : G.Adj b c) (hc : c ∈ S) :
    ReachIn G S a c := ⟨h.1,h.2.tail ⟨hbc,h.end_mem,hc⟩⟩

theorem ReachIn.trans (h : ReachIn G S a b) (h' : ReachIn G S b c) :
    ReachIn G S a c := ⟨h.1,h.2.trans h'.2⟩

theorem ReachIn.symm (h : ReachIn G S a b) : ReachIn G S b a := by
  have hb := h.end_mem
  obtain ⟨_,hab⟩ := h
  refine ⟨hb,?_⟩
  induction hab with
  | refl => exact .refl
  | tail _ he ih => exact .head ⟨G.symm he.1,he.2.2,he.2.1⟩ (ih he.2.1)

theorem ReachIn.mono (h : ReachIn G S a b) (hst : S ⊆ T) : ReachIn G T a b :=
  ⟨hst h.1,h.2.mono fun _ _ he => ⟨he.1,hst he.2.1,hst he.2.2⟩⟩

structure InducedPath (G : SimpleGraph V) (a b : V) where
  length : ℕ
  vertex : Fin (length + 1) → V
  first : vertex 0 = a
  last : vertex ⟨length,by omega⟩ = b
  injective : Function.Injective vertex
  adj_iff : ∀ i j, G.Adj (vertex i) (vertex j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

def InducedPath.Inside (p : InducedPath G a b) (S : Set V) : Prop := ∀ i, p.vertex i ∈ S

def InducedPath.refl (G : SimpleGraph V) (a : V) : InducedPath G a a where
  length := 0
  vertex := fun _ => a
  first := rfl
  last := rfl
  injective := by intro i j _; fin_cases i; fin_cases j; rfl
  adj_iff := by intro i j; fin_cases i; fin_cases j; simp

def InducedPath.prefix (p : InducedPath G a b) (k : Fin (p.length + 1)) :
    InducedPath G a (p.vertex k) where
  length := k.val
  vertex := fun i => p.vertex ⟨i.val,by have := k.isLt; omega⟩
  first := p.first
  last := rfl
  injective := by
    intro i j h
    have hv := congrArg Fin.val (p.injective h)
    exact Fin.ext hv
  adj_iff := fun i j => p.adj_iff _ _

theorem InducedPath.prefix_inside (p : InducedPath G a b) (hp : p.Inside S)
    (k : Fin (p.length + 1)) : (p.prefix k).Inside S := fun _ => hp _

def InducedPath.extendAt (p : InducedPath G a b) (k : Fin (p.length + 1))
    (hc : ∀ i, p.vertex i ≠ c) (hk : G.Adj (p.vertex k) c)
    (hbefore : ∀ i, i.val < k.val → ¬ G.Adj (p.vertex i) c) : InducedPath G a c where
  length := k.val + 1
  vertex := fun i => if h : i.val ≤ k.val then p.vertex ⟨i.val,by have := k.isLt; omega⟩ else c
  first := by simp only [Fin.val_zero, Nat.zero_le, dite_true]; exact p.first
  last := by simp
  injective := by
    intro i j h
    dsimp at h
    by_cases hi : i.val ≤ k.val <;> by_cases hj : j.val ≤ k.val
    · rw [dif_pos hi,dif_pos hj] at h
      have hv := congrArg Fin.val (p.injective h)
      exact Fin.ext hv
    · rw [dif_pos hi,dif_neg hj] at h
      exact False.elim (hc _ h)
    · rw [dif_neg hi,dif_pos hj] at h
      exact False.elim (hc _ h.symm)
    · apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
  adj_iff := by
    intro i j
    have hi' := i.isLt
    have hj' := j.isLt
    have hbase (r : Fin (p.length + 1)) (hr : r.val ≤ k.val) :
        G.Adj (p.vertex r) c ↔ r.val = k.val := by
      constructor
      · intro h
        by_contra he
        exact hbefore r (by omega) h
      · intro he
        have : r = k := Fin.ext he
        simpa [this] using hk
    by_cases hi : i.val ≤ k.val <;> by_cases hj : j.val ≤ k.val
    · simp only [dif_pos hi,dif_pos hj,p.adj_iff]
    · simp only [dif_pos hi,dif_neg hj]
      rw [hbase _ hi]
      simp only [Fin.val_mk]
      omega
    · simp only [dif_neg hi,dif_pos hj]
      rw [G.adj_comm,hbase _ hj]
      simp only [Fin.val_mk]
      omega
    · have hij : i = j := Fin.ext (by omega)
      subst j
      simp

theorem InducedPath.extendAt_inside (p : InducedPath G a b) (k : Fin (p.length + 1))
    (hc : ∀ i, p.vertex i ≠ c) (hk : G.Adj (p.vertex k) c)
    (hbefore : ∀ i, i.val < k.val → ¬ G.Adj (p.vertex i) c)
    (hp : p.Inside S) (hcS : c ∈ S) : (p.extendAt k hc hk hbefore).Inside S := by
  intro i
  dsimp [InducedPath.extendAt]
  split_ifs
  · exact hp _
  · exact hcS

/-- Truncate at the first neighbour of a new endpoint, or at its earlier
occurrence. Thus extending reachability gives an actual induced path. -/
theorem InducedPath.step_inside (p : InducedPath G a b) (hp : p.Inside S)
    (hbc : G.Adj b c) (hcS : c ∈ S) : ∃ q : InducedPath G a c, q.Inside S := by
  by_cases hc : ∃ i, p.vertex i = c
  · obtain ⟨i,rfl⟩ := hc
    exact ⟨p.prefix i,p.prefix_inside hp i⟩
  · have hnew : ∀ i, p.vertex i ≠ c := by simpa using hc
    let A := Finset.univ.filter (fun i => G.Adj (p.vertex i) c)
    have hA : A.Nonempty := by
      refine ⟨⟨p.length,by omega⟩,?_⟩
      simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,p.last]
      exact hbc
    obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image A Fin.val hA
    have hk' : G.Adj (p.vertex k) c := (Finset.mem_filter.mp hk).2
    have hb (i : Fin (p.length + 1)) (hi : i.val < k.val) : ¬ G.Adj (p.vertex i) c := by
      intro hadj
      have := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩)
      omega
    exact ⟨p.extendAt k hnew hk' hb,p.extendAt_inside k hnew hk' hb hp hcS⟩

/-- No finiteness or shortest-path theorem is assumed for this construction. -/
theorem ReachIn.inducedPath (h : ReachIn G S a b) :
    ∃ p : InducedPath G a b, p.Inside S := by
  obtain ⟨ha,h⟩ := h
  induction h with
  | refl => exact ⟨InducedPath.refl G a,fun _ => ha⟩
  | tail _ h ih =>
    obtain ⟨p,hp⟩ := ih
    exact p.step_inside hp h.1 h.2.2

theorem InducedPath.two_le_length (p : InducedPath G a b) (hne : a ≠ b)
    (hnadj : ¬ G.Adj a b) : 2 ≤ p.length := by
  have h0 : p.length ≠ 0 := by
    intro h
    apply hne
    have he : (0 : Fin (p.length + 1)) = ⟨p.length,by omega⟩ := Fin.ext (by simpa using h.symm)
    exact p.first.symm.trans ((congrArg p.vertex he).trans p.last)
  by_contra h
  have h1 : p.length = 1 := by omega
  apply hnadj
  have ha := (p.adj_iff 0 ⟨p.length,by omega⟩).mpr (Or.inl (by simpa using h1.symm))
  simpa only [p.first,p.last] using ha

end
end CoefficientwiseRigidity.Structure
