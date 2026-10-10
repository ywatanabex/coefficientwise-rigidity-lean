import CoefficientwiseRigidity.CoefficientQuantitative

/-!
Exact removal of full isolated occupations, followed by the existing deletion
of zero occupations. This closes all active-support boundaries of width-two A.
-/
namespace CoefficientwiseRigidity
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ} {a : V → ℕ}

omit [Fintype V] [DecidableEq V] in
/-- Restricting every bag proves heredity for the original tree-bag definition. -/
theorem treewidth_induce (hw : TreewidthAtMostTwo G) (P : Set V) :
    TreewidthAtMostTwo (G.induce P) := by
  obtain ⟨n,T,B,ht,hs,hc,he,hr⟩ := hw
  refine ⟨n,T,fun i => (B i).subtype (fun v => v ∈ P),ht,?_,?_,?_,?_⟩
  · intro i
    exact (Finset.card_subtype _ _).trans_le ((Finset.card_filter_le _ _).trans (hs i))
  · intro v
    obtain ⟨i,hi⟩ := hc v.val
    exact ⟨i,Finset.mem_subtype.mpr hi⟩
  · intro u v huv
    obtain ⟨i,hi,hj⟩ := he u.val v.val huv
    exact ⟨i,Finset.mem_subtype.mpr hi,Finset.mem_subtype.mpr hj⟩
  · intro v
    have hset : {t | v ∈ (B t).subtype (fun w => w ∈ P)} = {t | v.val ∈ B t} := by
      ext t
      exact Finset.mem_subtype
    rw [hset]
    exact hr v.val

omit [Fintype V] [DecidableEq V] in
theorem feasible_edge_interior (hf : Feasible G M a) (hp : Positive a)
    {u v : V} (huv : G.Adj u v) : a u < M ∧ a v < M := by
  have := hf.2 u v huv
  have := hp u
  have := hp v
  omega

def interiorCover (X : Cover G M) (a : V → ℕ) : Cover (G.induce {v | a v < M}) M where
  transport u v := X.transport u.val v.val
  reverse h := X.reverse h

def extendFull (M : ℕ) (a : V → ℕ) (S : Assignment {v : V // a v < M} M) :
    Assignment V M := fun v => if h : a v < M then S ⟨v,h⟩ else univ

omit [Fintype V] [DecidableEq V] in
theorem extendFull_admissible (X : Cover G M) (hf : Feasible G M a) (hp : Positive a)
    (S : Configuration (interiorCover X a) (fun v => a v.val)) :
    Admissible X a (extendFull M a S.val) := by
  constructor
  · intro v
    by_cases h : a v < M
    · simpa [extendFull,h] using S.property.1 ⟨v,h⟩
    · have he : a v = M := by have := hf.1 v; omega
      simp [extendFull,h,he]
  · intro u v huv i hi hj
    obtain ⟨hu,hv⟩ := feasible_edge_interior hf hp huv
    simp only [extendFull,dif_pos hu] at hi
    simp only [extendFull,dif_pos hv] at hj
    exact S.property.2 ⟨u,hu⟩ ⟨v,hv⟩ huv i hi hj

/-- A full occupation at an isolated vertex has exactly one configuration. -/
def interiorConfigurationEquiv (X : Cover G M) (hf : Feasible G M a) (hp : Positive a) :
    Configuration X a ≃ Configuration (interiorCover X a) (fun v => a v.val) where
  toFun S := ⟨fun v => S.val v.val, ⟨fun v => S.property.1 v.val,
    fun u v huv i hi => S.property.2 u.val v.val huv i hi⟩⟩
  invFun S := ⟨extendFull M a S.val, extendFull_admissible X hf hp S⟩
  left_inv S := by
    apply Subtype.ext
    funext v
    by_cases h : a v < M
    · simp [extendFull,h]
    · have he : a v = M := by have := hf.1 v; omega
      have hfull : S.val v = univ := by
        apply Finset.eq_univ_of_card
        simpa [he] using S.property.1 v
      simp [extendFull,h,hfull]
  right_inv S := by
    apply Subtype.ext
    funext v
    change (if h : a v.val < M then S.val ⟨v.val,h⟩ else univ) = S.val v
    rw [dif_pos (show a v.val < M from v.property)]

theorem coefficient_interior_eq (X : Cover G M) (hf : Feasible G M a) (hp : Positive a) :
    coefficient X a = coefficient (interiorCover X a) (fun v => a v.val) :=
  Fintype.card_congr (interiorConfigurationEquiv X hf hp)

theorem ordinary_interior_eq (hf : Feasible G M a) (hp : Positive a) :
    ordinary G M a = ordinary (G.induce {v | a v < M}) M (fun v => a v.val) :=
  coefficient_interior_eq (trivialCover G M) hf hp

omit [Fintype V] [DecidableEq V] in
theorem interiorCover_flat_iff (X : Cover G M) (hf : Feasible G M a) (hp : Positive a) :
    Flat (interiorCover X a) ↔ Flat X := by
  constructor
  · rintro ⟨γ,hγ⟩
    refine ⟨fun v => if h : a v < M then γ ⟨v,h⟩ else Equiv.refl _,?_⟩
    intro u v huv i
    obtain ⟨hu,hv⟩ := feasible_edge_interior hf hp huv
    simpa only [dif_pos hu,dif_pos hv] using hγ ⟨u,hu⟩ ⟨v,hv⟩ huv i
  · rintro ⟨γ,hγ⟩
    exact ⟨fun v => γ v.val, fun u v huv => hγ u.val v.val huv⟩

/-- Positive feasible occupations allow isolated full ranks and small layers. -/
theorem coefficient_eq_iff_flat_of_positive_treewidth (b : Bipartition G) (X : Cover G M)
    (hf : Feasible G M a) (hp : Positive a) (hw : TreewidthAtMostTwo G) :
    coefficient X a = ordinary G M a ↔ Flat X := by
  by_cases hM : 2 ≤ M
  · obtain ⟨m,rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2,by omega⟩
    let b' : Bipartition (G.induce {v | a v < m + 2}) :=
      ⟨fun v => b.side v.val, fun h => b.opposite h⟩
    have hf' : Feasible (G.induce {v | a v < m + 2}) (m + 2) (fun v => a v.val) :=
      ⟨fun v => hf.1 v.val, fun u v huv => hf.2 u.val v.val huv⟩
    rw [coefficient_interior_eq X hf hp, ordinary_interior_eq hf hp]
    exact (coefficient_eq_iff_flat_of_interior_treewidth b' (interiorCover X a)
      (fun v => ⟨hp v.val,v.property⟩) hf' (treewidth_induce hw _)).trans
      (interiorCover_flat_iff X hf hp)
  · have hflat : Flat X := by
      refine ⟨fun _ => Equiv.refl _,?_⟩
      intro u v huv
      have := hf.2 u v huv
      have := hp u
      have := hp v
      omega
    exact ⟨fun _ => hflat, fun h => activeFlat_coefficient_eq X a (flat_activeFlat X a h)⟩

/-- The equality characterization at the exact active support of Main A. -/
theorem coefficient_eq_iff_activeFlat_of_treewidth (b : Bipartition G) (X : Cover G M)
    (hf : Feasible G M a) (hw : TreewidthAtMostTwo (supportGraph G a)) :
    coefficient X a = ordinary G M a ↔ ActiveFlat X a := by
  let b' : Bipartition (supportGraph G a) :=
    ⟨fun v => b.side v.val, fun h => b.opposite h⟩
  have hf' : Feasible (supportGraph G a) M (fun v => a v.val) :=
    ⟨fun v => hf.1 v.val, fun u v huv => hf.2 u.val v.val huv⟩
  rw [coefficient_support_eq X a,ordinary_support_eq G M a,activeFlat_iff_support_flat]
  exact coefficient_eq_iff_flat_of_positive_treewidth b' (supportCover X a) hf'
    (fun v => v.property) hw

/-- The complete width-two branch of the unchanged Main A proposition.
The chordal-bipartite branch remains a separate obligation. -/
theorem mainA_of_treewidth (b : Bipartition G) (M : ℕ) (X : Cover G M) (a : V → ℕ)
    (hf : Feasible G M a) (hw : TreewidthAtMostTwo (supportGraph G a)) :
    coefficient X a ≤ ordinary G M a ∧
      (coefficient X a = ordinary G M a ↔ ActiveFlat X a) :=
  ⟨coefficient_le_of_active_treewidth b X a hw,
    coefficient_eq_iff_activeFlat_of_treewidth b X hf hw⟩

end
end CoefficientwiseRigidity
