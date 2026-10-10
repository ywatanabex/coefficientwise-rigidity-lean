import CoefficientwiseRigidity.Gauge

/-! Exact deletion of zero occupations and support-dependent flatness (F2/F4). -/
namespace CoefficientwiseRigidity
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def supportCover (X : Cover G M) (a : V → ℕ) : Cover (supportGraph G a) M where
  transport u v := X.transport u.val v.val
  reverse h := X.reverse h

def extendActive (a : V → ℕ) (S : Assignment (ActiveVertex a) M) : Assignment V M :=
  fun v => if h : 0 < a v then S ⟨v, h⟩ else ∅

omit [Fintype V] [DecidableEq V] in
theorem extendActive_admissible (X : Cover G M) (a : V → ℕ)
    (S : Configuration (supportCover X a) (fun v => a v.val)) :
    Admissible X a (extendActive a S.val) := by
  constructor
  · intro v
    by_cases h : 0 < a v
    · simpa [extendActive, h] using S.property.1 ⟨v, h⟩
    · have hz : a v = 0 := by omega
      simp [extendActive, h, hz]
  · intro u v huv i hi hj
    by_cases hu : 0 < a u
    · by_cases hv : 0 < a v
      · simp only [extendActive, dif_pos hu] at hi
        simp only [extendActive, dif_pos hv] at hj
        exact S.property.2 ⟨u, hu⟩ ⟨v, hv⟩ huv i hi hj
      · simp [extendActive, hv] at hj
    · simp [extendActive, hu] at hi

noncomputable def supportConfigurationEquiv (X : Cover G M) (a : V → ℕ) :
    Configuration X a ≃ Configuration (supportCover X a) (fun v => a v.val) where
  toFun S := ⟨fun v => S.val v.val, ⟨fun v => S.property.1 v.val,
    fun u v huv i hi => S.property.2 u.val v.val huv i hi⟩⟩
  invFun S := ⟨extendActive a S.val, extendActive_admissible X a S⟩
  left_inv S := by
    apply Subtype.ext
    funext v
    by_cases h : 0 < a v
    · simp [extendActive, h]
    · have hz : a v = 0 := by omega
      have he : S.val v = ∅ := Finset.card_eq_zero.mp ((S.property.1 v).trans hz)
      simp [extendActive, h, he]
  right_inv S := by
    apply Subtype.ext
    funext v
    simp [extendActive, v.property]

theorem coefficient_support_eq (X : Cover G M) (a : V → ℕ) :
    coefficient X a = coefficient (supportCover X a) (fun v => a v.val) :=
  Fintype.card_congr (supportConfigurationEquiv X a)

theorem ordinary_support_eq (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) :
    ordinary G M a = ordinary (supportGraph G a) M (fun v => a v.val) :=
  coefficient_support_eq (trivialCover G M) a

omit [Fintype V] [DecidableEq V] in
theorem activeFlat_iff_support_flat (X : Cover G M) (a : V → ℕ) :
    ActiveFlat X a ↔ Flat (supportCover X a) := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨fun v => γ v.val, fun u v huv =>
      hγ u.val v.val huv u.property v.property⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨fun v => if h : 0 < a v then γ ⟨v, h⟩ else Equiv.refl _, ?_⟩
    intro u v huv hu hv i
    simpa only [dif_pos hu, dif_pos hv] using hγ ⟨u, hu⟩ ⟨v, hv⟩ huv i

end CoefficientwiseRigidity
