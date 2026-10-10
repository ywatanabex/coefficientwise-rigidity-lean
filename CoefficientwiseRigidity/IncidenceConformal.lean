import CoefficientwiseRigidity.IncidenceRestrictions

/-!
The conformality part of paper §05 B2. A smallest uncovered primal clique
would give an induced incidence C6, in the original arithmetic cycle model.
-/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V] {U : Finset V} {H : Finset (Finset V)}

omit [DecidableEq V] in
set_option maxHeartbeats 600000 in
/-- Three rows each miss exactly one of three columns: an actual induced C6. -/
theorem incidence_no_triangle (hg : ChordalBipartite (incidenceGraph U H))
    (c : Fin 3 → U) (e : Fin 3 → H)
    (hm : ∀ i j, (c j).val ∈ (e i).val ↔ i ≠ j) : False := by
  have hc : Function.Injective c := by
    intro i j heq
    by_contra hn
    have hh := (hm i j).mpr hn
    rw [← heq] at hh
    exact (hm i i).mp hh rfl
  have he : Function.Injective e := by
    intro i j heq
    by_contra hn
    have hh := (hm i j).mpr hn
    rw [heq] at hh
    exact (hm j j).mp hh rfl
  let f : Fin 6 → H ⊕ U := fun i => match i.val with
    | 0 => Sum.inr (c 0)
    | 1 => Sum.inl (e 2)
    | 2 => Sum.inr (c 1)
    | 3 => Sum.inl (e 0)
    | 4 => Sum.inr (c 2)
    | _ => Sum.inl (e 1)
  apply hg.2 6 (by decide)
  refine ⟨f,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f,hc.eq_iff,he.eq_iff]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [f,incidenceGraph,CycleAdjacent,hm] <;> decide

/-- Pairwise coverage is exactly clique membership in the primal graph. -/
def FamilyClique (H : Finset (Finset V)) (K : Finset V) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, x ≠ y → ∃ E ∈ H, x ∈ E ∧ y ∈ E

/-- The size-two base of conformality is already present in pairwise coverage. -/
theorem FamilyClique.covered_pair {K : Finset V} (hk : FamilyClique H K)
    (hcard : K.card = 2) : ∃ E ∈ H, K ⊆ E := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < K.card)
  obtain ⟨E,hE,hxE,hyE⟩ := hk x hx y hy hxy
  have hpair : ({x,y} : Finset V) ⊆ K := by simp [Finset.insert_subset_iff,hx,hy]
  have heq : K = {x,y} := by
    symm
    apply Finset.eq_of_subset_of_card_le hpair
    simp [hcard,hxy]
  refine ⟨E,hE,?_⟩
  rw [heq]
  simp [Finset.insert_subset_iff,hxE,hyE]

private theorem clique_covered_aux (n : ℕ)
    (hg : ChordalBipartite (incidenceGraph U H)) :
    ∀ K : Finset V, K.card = n → K ⊆ U → FamilyClique H K → 2 ≤ K.card →
      ∃ E ∈ H, K ⊆ E := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hcard hKU hk hn
    by_cases htwo : K.card = 2
    · exact hk.covered_pair htwo
    · by_contra hno
      have hthree : 2 < K.card := by omega
      obtain ⟨x,hx,y,hy,z,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card.mp hthree
      have smaller (w : V) (hw : w ∈ K) : ∃ E ∈ H, K.erase w ⊆ E ∧ w ∉ E := by
        have hlt := Finset.card_erase_lt_of_mem hw
        have hc := Finset.card_erase_add_one hw
        obtain ⟨E,hE,hsub⟩ := ih (K.erase w).card (by omega) (K.erase w) rfl
          ((Finset.erase_subset _ _).trans hKU)
          (fun a ha b hb hab => hk a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)
          (by omega)
        refine ⟨E,hE,hsub,?_⟩
        intro hwE
        apply hno
        refine ⟨E,hE,?_⟩
        intro v hv
        by_cases hvw : v = w
        · exact hvw ▸ hwE
        · exact hsub (Finset.mem_erase.mpr ⟨hvw,hv⟩)
      obtain ⟨Ex,hEx,hxsub,hxnot⟩ := smaller x hx
      obtain ⟨Ey,hEy,hysub,hynot⟩ := smaller y hy
      obtain ⟨Ez,hEz,hzsub,hznot⟩ := smaller z hz
      have hxEy := hysub (Finset.mem_erase.mpr ⟨hxy,hx⟩)
      have hxEz := hzsub (Finset.mem_erase.mpr ⟨hxz,hx⟩)
      have hyEx := hxsub (Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩)
      have hyEz := hzsub (Finset.mem_erase.mpr ⟨hyz,hy⟩)
      have hzEx := hxsub (Finset.mem_erase.mpr ⟨Ne.symm hxz,hz⟩)
      have hzEy := hysub (Finset.mem_erase.mpr ⟨Ne.symm hyz,hz⟩)
      apply incidence_no_triangle hg ![⟨x,hKU hx⟩,⟨y,hKU hy⟩,⟨z,hKU hz⟩]
        ![⟨Ex,hEx⟩,⟨Ey,hEy⟩,⟨Ez,hEz⟩]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp_all

/-- Every nontrivial primal clique is contained in an actual row. Isolated
singletons are handled separately by the virtual singleton in AlphaLeaf. -/
theorem incidence_clique_covered (hg : ChordalBipartite (incidenceGraph U H))
    {K : Finset V} (hKU : K ⊆ U) (hk : FamilyClique H K) (hn : 2 ≤ K.card) :
    ∃ E ∈ H, K ⊆ E := clique_covered_aux K.card hg K rfl hKU hk hn

end
end CoefficientwiseRigidity.Structure
