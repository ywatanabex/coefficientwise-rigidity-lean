import CoefficientwiseRigidity.Targets
import CoefficientwiseRigidity.Gauge

/-! Actual gauge gluing for empty, vertex, and real-edge seams. -/
namespace CoefficientwiseRigidity.Gluing
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G G₁ G₂ : SimpleGraph V} {M : ℕ} {U₁ U₂ : Finset V}

def subCover (X : Cover G M) (H : SimpleGraph V) (h : H ≤ G) : Cover H M where
  transport := X.transport
  reverse huv := X.reverse (h huv)

omit [Fintype V] in
theorem seam_clique_left (hs : LegalSeam U₁ U₂ G₁ G₂)
    {u v : V} (hu : u ∈ U₁ ∩ U₂) (hv : v ∈ U₁ ∩ U₂) (hne : u ≠ v) :
    G₁.Adj u v := by
  rcases hs with he | ⟨w, he⟩ | ⟨s, t, he, hst, _⟩
  · simp [he] at hu
  · have hu' : u = w := by simpa [he] using hu
    have hv' : v = w := by simpa [he] using hv
    exact False.elim (hne (hu'.trans hv'.symm))
  · have hu' : u = s ∨ u = t := by simpa [he] using hu
    have hv' : v = s ∨ v = t := by simpa [he] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact False.elim (hne rfl)
    · exact hst
    · exact hst.symm
    · exact False.elim (hne rfl)

omit [Fintype V] in
theorem seam_symm (hs : LegalSeam U₁ U₂ G₁ G₂) : LegalSeam U₂ U₁ G₂ G₁ := by
  rcases hs with he | ⟨v, he⟩ | ⟨u, v, he, h₁, h₂⟩
  · exact Or.inl (by simpa [Finset.inter_comm] using he)
  · exact Or.inr (Or.inl ⟨v, by simpa [Finset.inter_comm] using he⟩)
  · exact Or.inr (Or.inr ⟨u, v, by simpa [Finset.inter_comm] using he, h₂, h₁⟩)

omit [Fintype V] in
theorem align_active_gauges (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hs : LegalSeam U₁ U₂ G₁ G₂) (γ₁ γ₂ : V → Equiv.Perm (Fin M))
    (h₁ : ∀ u v, G₁.Adj u v → 0 < a u → 0 < a v →
      ∀ i, X.transport u v (γ₁ u i) = γ₁ v i)
    (h₂ : ∀ u v, G₂.Adj u v → 0 < a u → 0 < a v →
      ∀ i, X.transport u v (γ₂ u i) = γ₂ v i) :
    ∃ μ : Equiv.Perm (Fin M), ∀ v, v ∈ U₁ ∩ U₂ → 0 < a v →
      ∀ i, γ₂ v (μ i) = γ₁ v i := by
  classical
  by_cases hp : ∃ p, p ∈ U₁ ∩ U₂ ∧ 0 < a p
  · obtain ⟨p, hp, hap⟩ := hp
    refine ⟨(γ₁ p).trans (γ₂ p).symm, ?_⟩
    intro v hv hav i
    by_cases he : p = v
    · subst v
      simp
    · have hleft := seam_clique_left hs hp hv he
      have hright := seam_clique_left (seam_symm hs)
        (by simpa [Finset.inter_comm] using hp)
        (by simpa [Finset.inter_comm] using hv) he
      calc
        γ₂ v (((γ₁ p).trans (γ₂ p).symm) i) =
            X.transport p v (γ₂ p (((γ₁ p).trans (γ₂ p).symm) i)) :=
          (h₂ p v hright hap hav _).symm
        _ = X.transport p v (γ₁ p i) := by simp
        _ = γ₁ v i := h₁ p v hleft hap hav i
  · refine ⟨Equiv.refl _, ?_⟩
    intro v hv hav
    exact False.elim (hp ⟨v, hv, hav⟩)

omit [Fintype V] in
theorem activeFlat_sup_iff (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂) :
    ActiveFlat X a ↔ ActiveFlat (subCover X G₁ le_sup_left) a ∧
      ActiveFlat (subCover X G₂ le_sup_right) a := by
  classical
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨⟨γ, fun u v h => hγ u v (Or.inl h)⟩,
      ⟨γ, fun u v h => hγ u v (Or.inr h)⟩⟩
  · rintro ⟨⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩⟩
    obtain ⟨μ, hμ⟩ := align_active_gauges X a hs γ₁ γ₂ h₁ h₂
    let γ : V → Equiv.Perm (Fin M) :=
      fun v => if v ∈ U₁ then γ₁ v else μ.trans (γ₂ v)
    have hγ₁ : ∀ v, v ∈ U₁ → γ v = γ₁ v := by
      intro v hv
      simp [γ, hv]
    have hγ₂ : ∀ v, v ∈ U₂ → 0 < a v → ∀ i, γ v i = γ₂ v (μ i) := by
      intro v hv hav i
      by_cases hv₁ : v ∈ U₁
      · simpa [γ, hv₁] using (hμ v (Finset.mem_inter.mpr ⟨hv₁, hv⟩) hav i).symm
      · simp [γ, hv₁]
    refine ⟨γ, ?_⟩
    intro u v huv hau hav i
    rcases huv with huv | huv
    · obtain ⟨hu, hv⟩ := hU₁ u v huv
      rw [hγ₁ u hu, hγ₁ v hv]
      exact h₁ u v huv hau hav i
    · obtain ⟨hu, hv⟩ := hU₂ u v huv
      rw [hγ₂ u hu hau, hγ₂ v hv hav]
      exact h₂ u v huv hau hav (μ i)

omit [Fintype V] in
theorem activeFlat_restrict_iff (X : Cover G M) (a : V → ℕ)
    (U : Finset V) (H : SimpleGraph V) (hle : H ≤ G) (hs : SupportedOn H U) :
    ActiveFlat (restrictCover X U H hle) (fun v => a v.val) ↔
      ActiveFlat (subCover X H hle) a := by
  classical
  constructor
  · rintro ⟨γ, hγ⟩
    let δ : V → Equiv.Perm (Fin M) :=
      fun v => if hv : v ∈ U then γ ⟨v, hv⟩ else Equiv.refl _
    refine ⟨δ, ?_⟩
    intro u v huv hau hav i
    obtain ⟨hu, hv⟩ := hs u v huv
    simpa [δ, hu, hv, subCover, restrictCover] using
      hγ ⟨u, hu⟩ ⟨v, hv⟩ huv hau hav i
  · rintro ⟨γ, hγ⟩
    exact ⟨fun v => γ v.val, fun u v huv => hγ u.val v.val huv⟩

omit [Fintype V] in
theorem activeFlat_glue_iff (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂) :
    ActiveFlat X a ↔
      ActiveFlat (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val) ∧
      ActiveFlat (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val) := by
  rw [activeFlat_restrict_iff X a U₁ G₁ le_sup_left hU₁,
    activeFlat_restrict_iff X a U₂ G₂ le_sup_right hU₂]
  exact activeFlat_sup_iff X a hU₁ hU₂ hs

end
end CoefficientwiseRigidity.Gluing

namespace CoefficientwiseRigidity
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem StructuralHull.supported {U : Finset V} {G : SimpleGraph V}
    (h : StructuralHull U G) : SupportedOn G U := by
  induction h with
  | atom U G hs _ => exact hs
  | glue h₁ h₂ hs ih₁ ih₂ =>
    intro u v huv
    rcases huv with huv | huv
    · exact ⟨Finset.mem_union_left _ (ih₁ u v huv).1,
        Finset.mem_union_left _ (ih₁ u v huv).2⟩
    · exact ⟨Finset.mem_union_right _ (ih₂ u v huv).1,
        Finset.mem_union_right _ (ih₂ u v huv).2⟩

omit [Fintype V] in
theorem WitnessHull.toStructuralHull {W U : Finset V} {H G : SimpleGraph V}
    (h : WitnessHull W H U G) : StructuralHull U G := by
  induction h with
  | here hs ha => exact StructuralHull.atom _ _ hs ha
  | left h₁ h₂ hs ih => exact StructuralHull.glue ih h₂ hs
  | right h₁ h₂ hs ih => exact StructuralHull.glue h₁ ih hs

omit [Fintype V] in
theorem WitnessHull.subgraph {W U : Finset V} {H G : SimpleGraph V}
    (h : WitnessHull W H U G) : H ≤ G := by
  induction h with
  | here hs ha => exact le_rfl
  | left h₁ h₂ hs ih => exact ih.trans le_sup_left
  | right h₁ h₂ hs ih => exact ih.trans le_sup_right

omit [Fintype V] in
theorem WitnessHull.subset {W U : Finset V} {H G : SimpleGraph V}
    (h : WitnessHull W H U G) : W ⊆ U := by
  induction h with
  | here hs ha => exact Finset.Subset.refl _
  | left h₁ h₂ hs ih => exact ih.trans Finset.subset_union_left
  | right h₁ h₂ hs ih => exact ih.trans Finset.subset_union_right

end CoefficientwiseRigidity
