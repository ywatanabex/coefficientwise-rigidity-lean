import CoefficientwiseRigidity.CoverIntersections
import CoefficientwiseRigidity.Support

/-! Exact independent-set coefficient bridge for the intersection comparison. -/
namespace CoefficientwiseRigidity.Intersections
open Finset Compression Structure
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def columnRanks (M : ℕ) (a : V → ℕ) : V → ℕ := fun v => M - a v

def rightComplements (b : Bipartition G) (S : V → Finset (Fin M)) : V → Finset (Fin M) :=
  fun v => if b.side v = true then ∅ else (S v)ᶜ

abbrev ColumnChoices (b : Bipartition G) (M : ℕ) (a : V → ℕ) :=
  {Q : V → Finset (Fin M) // ValidOn (columnRanks M a) (columnSet b) (fun _ => ∅) Q}

abbrev BipartiteChoices (b : Bipartition G) (X : Cover G M) (a : V → ℕ) :=
  (Q : ColumnChoices b M a) × RowCompletions b X a Q.val

omit [DecidableEq V] in
theorem rightComplements_valid (b : Bipartition G) (a : V → ℕ) (S : V → Finset (Fin M))
    (hs : ∀ v, (S v).card = a v) :
    ValidOn (columnRanks M a) (columnSet b) (fun _ => ∅) (rightComplements b S) := by
  constructor
  · intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    simp [rightComplements,hv',Finset.card_compl,hs,columnRanks]
  · intro v hv
    have hv' : b.side v = true := by
      cases h : b.side v <;> simp_all [columnSet]
    simp [rightComplements,hv']

def toBipartiteChoices (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (S : Configuration X a) : BipartiteChoices b X a :=
  ⟨⟨rightComplements b S.val,rightComplements_valid b a S.val S.property.1⟩,
    fun u => ⟨S.val u.val,by
      constructor
      · intro x hx
        rw [mem_cover_row]
        intro v he
        have hv : b.side v = false := by
          have hn := b.opposite he
          rw [u.property] at hn
          cases h : b.side v <;> simp_all
        simpa [rightComplements,hv] using S.property.2 u.val v he x hx
      · exact S.property.1 u.val⟩⟩

def assemble (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (C : BipartiteChoices b X a) : V → Finset (Fin M) :=
  fun v => if hv : b.side v = true then (C.2 ⟨v,hv⟩).val else (C.1.val v)ᶜ

omit [DecidableEq V] in
theorem assemble_admissible (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : ∀ v, a v ≤ M) (C : BipartiteChoices b X a) : Admissible X a (assemble b X a C) := by
  have hleft (u : V) (hu : b.side u = true) : assemble b X a C u = (C.2 ⟨u,hu⟩).val := by
    simp [assemble,hu]
  have hright (v : V) (hv : b.side v = false) : assemble b X a C v = (C.1.val v)ᶜ := by
    simp [assemble,hv]
  constructor
  · intro v
    cases hv : b.side v with
    | true => rw [hleft v hv]; exact (C.2 ⟨v,hv⟩).property.2
    | false =>
      rw [hright v hv,Finset.card_compl,Fintype.card_fin]
      have hq := C.1.property.1 v (by simp [columnSet,hv])
      change (C.1.val v).card = M - a v at hq
      rw [hq]
      exact Nat.sub_sub_self (ha v)
  · intro u v he x hx hy
    cases hu : b.side u with
    | true =>
      have hv : b.side v = false := by
        have hn := b.opposite he
        rw [hu] at hn
        cases h : b.side v <;> simp_all
      rw [hleft u hu] at hx
      rw [hright v hv,Finset.mem_compl] at hy
      exact hy ((mem_cover_row b X ⟨u,hu⟩ C.1.val x).mp ((C.2 ⟨u,hu⟩).property.1 hx) v he)
    | false =>
      have hv : b.side v = true := by
        have hn := b.opposite he
        rw [hu] at hn
        cases h : b.side v <;> simp_all
      rw [hright u hu,Finset.mem_compl] at hx
      rw [hleft v hv] at hy
      have hbad := (mem_cover_row b X ⟨v,hv⟩ C.1.val (X.transport u v x)).mp
        ((C.2 ⟨v,hv⟩).property.1 hy) u (G.symm he)
      rw [X.reverse he,Equiv.symm_apply_apply] at hbad
      exact hx hbad

def configurationBipartiteEquiv (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : ∀ v, a v ≤ M) : Configuration X a ≃ BipartiteChoices b X a where
  toFun := toBipartiteChoices b X a
  invFun C := ⟨assemble b X a C,assemble_admissible b X a ha C⟩
  left_inv S := by
    apply Subtype.ext
    funext v
    cases hv : b.side v <;> simp [assemble,toBipartiteChoices,rightComplements,hv]
  right_inv C := by
    have hQ : rightComplements b (assemble b X a C) = C.1.val := by
      funext v
      cases hv : b.side v with
      | true =>
        have he := C.1.property.2 v (by simp [columnSet,hv])
        simpa [rightComplements,hv] using he
      | false => simp [rightComplements,assemble,hv]
    apply Sigma.ext (Subtype.ext hQ)
    apply Function.hfunext rfl
    intro u u' hu
    have huu : u = u' := eq_of_heq hu
    subst u'
    apply (Subtype.heq_iff_coe_eq (by
      intro A
      change (A ⊆ row (graphRows b u) (coverGains b X u) (rightComplements b (assemble b X a C)) ∧ A.card = a u.val) ↔
        (A ⊆ row (graphRows b u) (coverGains b X u) C.1.val ∧ A.card = a u.val)
      rw [hQ])).mpr
    simp [toBipartiteChoices,assemble,u.property]

theorem coefficient_eq_intersection_sum (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : ∀ v, a v ≤ M) :
    (coefficient X a : ℚ) = sumSet (columnRanks M a) (columnSet b)
      (fun Q => binomialCost (fun u : LeftRows b => a u.val) (ranks (graphRows b) (coverGains b X) Q)) (fun _ => ∅) := by
  rw [coefficient,Fintype.card_congr (configurationBipartiteEquiv b X a ha),Fintype.card_sigma]
  push_cast
  simp only [card_rowCompletions]
  rw [sumSet_eq_assignment_sum]
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun Q => by simp) _

theorem coefficient_le_of_chordalBipartite (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) (ha : ∀ v, a v ≤ M) : coefficient X a ≤ ordinary G M a := by
  have h := graph_cone_comparison b hg (coverGains b X) (columnRanks M a)
    (binomialCost_cone (fun u : LeftRows b => a u.val)) (fun _ => ∅)
  rw [← coefficient_eq_intersection_sum b X a ha] at h
  change (coefficient X a : ℚ) ≤ sumSet (columnRanks M a) (columnSet b)
    (fun Q => binomialCost (fun u : LeftRows b => a u.val) (ranks (graphRows b) (coverGains b (trivialCover G M)) Q)) (fun _ => ∅) at h
  rw [← coefficient_eq_intersection_sum b (trivialCover G M) a ha] at h
  exact_mod_cast h

end
end CoefficientwiseRigidity.Intersections

namespace CoefficientwiseRigidity
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

/-- All occupations, including infeasible profiles, for the original graph. -/
theorem coefficient_le_of_chordalBipartite (X : Cover G M) (a : V → ℕ)
    (hg : ChordalBipartite G) : coefficient X a ≤ ordinary G M a := by
  obtain ⟨b⟩ := hg.1
  by_cases ha : Feasible G M a
  · exact Intersections.coefficient_le_of_chordalBipartite b hg X a ha.1
  · rw [coefficient_zero_of_not_feasible X a ha]
    exact Nat.zero_le _

/-- Comparison depends only on the original positive-rank support graph. -/
theorem coefficient_le_of_active_chordalBipartite (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (hg : ChordalBipartite (supportGraph G a)) : coefficient X a ≤ ordinary G M a := by
  rw [coefficient_support_eq X a,ordinary_support_eq G M a]
  let b' : Bipartition (supportGraph G a) :=
    ⟨fun v => b.side v.val,fun h => b.opposite h⟩
  exact coefficient_le_of_chordalBipartite (supportCover X a) (fun v => a v.val) ⟨⟨b'⟩,hg.2⟩

end CoefficientwiseRigidity
