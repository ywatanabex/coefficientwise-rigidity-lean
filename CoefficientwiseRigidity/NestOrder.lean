import CoefficientwiseRigidity.NestPoints

/-!
Actual finite elimination lists, with every suffix traced to its remaining
columns. The root-last theorem uses the proved two-nest-point induction.
-/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V]

/-- At each step the current incident rows are nested; the next step uses
exactly their traces on the remaining columns. -/
inductive NestOrder : Finset (Finset V) → List V → Prop
  | nil (H) : NestOrder H []
  | cons {H : Finset (Finset V)} {x : V} {L : List V}
      (head : NestPoint H x) (tail : NestOrder (Trace H L.toFinset) L) : NestOrder H (x :: L)

omit [DecidableEq V] in
theorem nestPoint_singleton {H : Finset (Finset V)} {x : V}
    (hs : FamilySupported {x} H) : NestPoint H x := by
  intro e he f _ _ hxf
  exact Or.inl ((hs e he).trans (Finset.singleton_subset_iff.mpr hxf))

private theorem root_last_aux (n : ℕ) :
    ∀ (U : Finset V) (H : Finset (Finset V)) (root : V), U.card = n →
      FamilySupported U H → HereditaryAlpha U H → root ∈ U →
      ∃ L : List V, NestOrder H L ∧ L.Nodup ∧ L.toFinset = U ∧ L.getLast? = some root := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U H root hcard hs ha hr
    by_cases hc : 2 ≤ U.card
    · obtain ⟨x,hx,hxr,hxn⟩ := exists_nest_ne hs ha hc root
      obtain ⟨L,hL,hnd,hU,hlast⟩ := ih (U.erase x).card (by
          have := Finset.card_erase_lt_of_mem hx
          omega) (U.erase x) (Trace H (U.erase x)) root rfl
          (trace_supported _ _) (ha.trace (Finset.erase_subset _ _))
          (Finset.mem_erase.mpr ⟨Ne.symm hxr,hr⟩)
      refine ⟨x :: L,?_,?_,?_,?_⟩
      · apply NestOrder.cons hxn
        simpa only [hU] using hL
      · apply List.nodup_cons.mpr
        refine ⟨?_,hnd⟩
        intro hm
        have hm' : x ∈ L.toFinset := List.mem_toFinset.mpr hm
        rw [hU] at hm'
        exact Finset.not_mem_erase _ _ hm'
      · simp only [List.toFinset_cons,hU,Finset.insert_erase hx]
      · cases L with
        | nil => simp at hlast
        | cons y L => simpa using hlast
    · have heq : U = {root} := by
        symm
        apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hr)
        have hn : 0 < U.card := Finset.card_pos.mpr ⟨root,hr⟩
        simp only [Finset.card_singleton]
        omega
      subst U
      exact ⟨[root],NestOrder.cons (nestPoint_singleton hs) (NestOrder.nil _),by simp,by simp,by simp⟩

/-- B4's complete list construction from its hereditary structural input. -/
theorem exists_root_last_nest_order {U : Finset V} {H : Finset (Finset V)}
    (hs : FamilySupported U H) (ha : HereditaryAlpha U H) {root : V} (hr : root ∈ U) :
    ∃ L : List V, NestOrder H L ∧ L.Nodup ∧ L.toFinset = U ∧ L.getLast? = some root :=
  root_last_aux U.card U H root rfl hs ha hr

theorem exists_nest_order {U : Finset V} {H : Finset (Finset V)}
    (hs : FamilySupported U H) (ha : HereditaryAlpha U H) :
    ∃ L : List V, NestOrder H L ∧ L.Nodup ∧ L.toFinset = U := by
  by_cases hU : U.Nonempty
  · obtain ⟨root,hr⟩ := hU
    obtain ⟨L,hL,hnd,hU,_⟩ := exists_root_last_nest_order hs ha hr
    exact ⟨L,hL,hnd,hU⟩
  · have heq : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    exact ⟨[],NestOrder.nil _,by simp,by simp [heq]⟩

/-- Removing rows preserves every nesting condition along an existing order. -/
theorem NestOrder.subfamily {H K : Finset (Finset V)} {L : List V}
    (h : NestOrder H L) (hK : K ⊆ H) : NestOrder K L := by
  induction h generalizing K with
  | nil H => exact NestOrder.nil _
  | @cons H x L hn ht ih =>
    refine NestOrder.cons ?_ (ih (trace_mono hK _))
    intro e he f hf hx hy
    exact hn e (hK he) f (hK hf) hx hy

/-- Every suffix is an actual elimination order of the original row traces.
This supplies the root-retaining induction's full suffix invariant. -/
theorem NestOrder.suffix {H : Finset (Finset V)} (A B : List V)
    (h : NestOrder H (A ++ B)) (hs : FamilySupported (A ++ B).toFinset H) :
    NestOrder (Trace H B.toFinset) B := by
  induction A generalizing H with
  | nil =>
    simp only [List.nil_append] at h hs
    rwa [trace_self hs]
  | cons x A ih =>
    change NestOrder H (x :: (A ++ B)) at h
    cases h with
    | cons hn ht =>
      have ht' := ih ht (trace_supported H (A ++ B).toFinset)
      have hsub : B.toFinset ⊆ (A ++ B).toFinset := by
        intro v hv
        exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hv))
      rwa [trace_trace H hsub] at ht'

end
end CoefficientwiseRigidity.Structure
