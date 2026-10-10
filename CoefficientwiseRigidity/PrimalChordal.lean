import CoefficientwiseRigidity.IncidenceConformal
import CoefficientwiseRigidity.CycleArithmetic

/-!
Primal chordality from the original incidence cycle prohibition, and the exact
alpha-leaf construction from a simplicial primal vertex. The general existence
of a simplicial vertex in a finite chordal graph is a separate obligation.
-/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V] {U : Finset V} {H : Finset (Finset V)}

def primalGraph (U : Finset V) (H : Finset (Finset V)) : SimpleGraph U where
  Adj x y := x ≠ y ∧ ∃ E ∈ H, x.val ∈ E ∧ y.val ∈ E
  symm := by
    rintro x y ⟨hne,E,hE,hx,hy⟩
    exact ⟨Ne.symm hne,E,hE,hy,hx⟩
  loopless := by intro x h; exact h.1 rfl

/-- The same arithmetic induced-cycle model, with threshold four. -/
def ChordalGraph {W : Type} (G : SimpleGraph W) : Prop :=
  ∀ n : ℕ, 4 ≤ n → ¬ ∃ f : Fin n → W, Function.Injective f ∧
    ∀ i j, G.Adj (f i) (f j) ↔ CycleAdjacent i j

def SimplicialVertex {W : Type} (G : SimpleGraph W) (x : W) : Prop :=
  ∀ y z, G.Adj x y → G.Adj x z → y ≠ z → G.Adj y z

omit [DecidableEq V] in
/-- Pair-row witnesses for a primal cycle give an exact incidence cycle twice
as long. Their injectivity follows from the two-element membership pattern. -/
theorem incidence_cycle_from_pairs {n : ℕ} (hn : 3 ≤ n)
    (c : Fin n → U) (hc : Function.Injective c) (e : Fin n → H)
    (hm : ∀ i j, (c j).val ∈ (e i).val ↔ j = i ∨ j = cycleNext i) :
    ∃ f : Fin (2 * n) → H ⊕ U, Function.Injective f ∧
      ∀ i j, (incidenceGraph U H).Adj (f i) (f j) ↔ CycleAdjacent i j := by
  have he : Function.Injective e := by
    intro i j heq
    have hi : i = j ∨ i = cycleNext j := by
      apply (hm j i).mp
      rw [← heq]
      exact (hm i i).mpr (Or.inl rfl)
    rcases hi with hi | hi
    · exact hi
    · have hnext : cycleNext i = j ∨ cycleNext i = cycleNext j := by
        apply (hm j (cycleNext i)).mp
        rw [← heq]
        exact (hm i (cycleNext i)).mpr (Or.inr rfl)
      rcases hnext with hj | hj
      · have hh : cycleNext (cycleNext j) = j := by rw [← hi,hj]
        exact False.elim (cycleNext_two_ne hn j hh)
      · have hh : cycleNext i = i := hj.trans hi.symm
        exact False.elim (cycleNext_ne (by omega) i hh)
  refine ⟨alternatingCycle e c,alternatingCycle_injective he hc,?_⟩
  intro i j
  rw [alternatingCycle_adjacent]
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0 <;>
    simp [alternatingCycle,hi,hj,incidenceGraph,hm]

omit [DecidableEq V] in
/-- An actual primal induced cycle has an incidence lift; no chordality or
simplicial-vertex theorem is used as an input to this step. -/
theorem primal_cycle_lift {n : ℕ} (hn : 4 ≤ n)
    (c : Fin n → U) (hc : Function.Injective c)
    (hcycle : ∀ i j, (primalGraph U H).Adj (c i) (c j) ↔ CycleAdjacent i j) :
    ∃ f : Fin (2 * n) → H ⊕ U, Function.Injective f ∧
      ∀ i j, (incidenceGraph U H).Adj (f i) (f j) ↔ CycleAdjacent i j := by
  have hex (i : Fin n) : ∃ E ∈ H, (c i).val ∈ E ∧ (c (cycleNext i)).val ∈ E :=
    ((hcycle i (cycleNext i)).mpr (cycleAdjacent_next i)).2
  choose E hE hiE hnE using hex
  apply incidence_cycle_from_pairs (by omega) c hc (fun i => ⟨E i,hE i⟩)
  intro i j
  constructor
  · intro hmem
    by_cases hji : j = i
    · exact Or.inl hji
    by_cases hjn : j = cycleNext i
    · exact Or.inr hjn
    have h1 : (primalGraph U H).Adj (c i) (c j) :=
      ⟨fun h => hji (hc h).symm,E i,hE i,hiE i,hmem⟩
    have h2 : (primalGraph U H).Adj (c (cycleNext i)) (c j) :=
      ⟨fun h => hjn (hc h).symm,E i,hE i,hnE i,hmem⟩
    exact False.elim (cycle_no_triangle hn i j ((hcycle i j).mp h1)
      ((hcycle (cycleNext i) j).mp h2))
  · rintro (rfl | rfl)
    · exact hiE _
    · exact hnE _

omit [DecidableEq V] in
/-- The primal graph is chordal under the original incidence hypothesis. -/
theorem primal_chordal (hg : ChordalBipartite (incidenceGraph U H)) :
    ChordalGraph (primalGraph U H) := by
  intro n hn
  rintro ⟨c,hc,hcycle⟩
  exact hg.2 (2 * n) (by omega) (primal_cycle_lift hn c hc hcycle)

/-- Every simplicial primal vertex is an alpha leaf, with the actual largest
row constructed using proved conformality. Isolated vertices use a singleton. -/
theorem primal_simplicial_alpha (hg : ChordalBipartite (incidenceGraph U H))
    (hs : FamilySupported U H) (x : U) (hx : SimplicialVertex (primalGraph U H) x) :
    ∃ E, AlphaLeaf U H x.val E := by
  let K := U.filter (fun y => y = x.val ∨ ∃ E ∈ H, x.val ∈ E ∧ y ∈ E)
  have hKU : K ⊆ U := Finset.filter_subset _ _
  have hxK : x.val ∈ K := Finset.mem_filter.mpr ⟨x.property,Or.inl rfl⟩
  have hrow (F : Finset V) (hF : F ∈ H) (hxF : x.val ∈ F) : F ⊆ K := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨hs F hF hy,Or.inr ⟨F,hF,hxF,hy⟩⟩
  have hAdj (y : V) (hy : y ∈ K) (hne : y ≠ x.val) :
      (primalGraph U H).Adj x ⟨y,hKU hy⟩ := by
    obtain ⟨_,hy⟩ := Finset.mem_filter.mp hy
    rcases hy with hy | hy
    · exact False.elim (hne hy)
    · exact ⟨fun h => hne (congrArg Subtype.val h).symm,hy⟩
  have hclique : FamilyClique H K := by
    intro y hy z hz hyz
    by_cases hyx : y = x.val
    · subst y
      exact (hAdj z hz (Ne.symm hyz)).2
    by_cases hzx : z = x.val
    · subst z
      obtain ⟨E,hE,hxE,hyE⟩ := (hAdj y hy hyx).2
      exact ⟨E,hE,hyE,hxE⟩
    · exact (hx ⟨y,hKU hy⟩ ⟨z,hKU hz⟩ (hAdj y hy hyx) (hAdj z hz hzx)
        (fun h => hyz (congrArg Subtype.val h))).2
  by_cases hc : 2 ≤ K.card
  · obtain ⟨E,hE,hKE⟩ := incidence_clique_covered hg hKU hclique hc
    exact ⟨E,hKE hxK,hs E hE,Or.inl hE,fun F hF hxF => (hrow F hF hxF).trans hKE⟩
  · refine ⟨{x.val},by simp,Finset.singleton_subset_iff.mpr x.property,Or.inr rfl,?_⟩
    intro F hF hxF y hy
    apply Finset.mem_singleton.mpr
    exact Finset.card_le_one.mp (by omega : K.card ≤ 1) y (hrow F hF hxF hy) x.val hxK

end
end CoefficientwiseRigidity.Structure
