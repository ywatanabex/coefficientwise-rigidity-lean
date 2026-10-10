import CoefficientwiseRigidity.IntersectionRows
import CoefficientwiseRigidity.ColumnSums

/-! C3: full-cone comparison along actual nest orders, retaining one root. -/
namespace CoefficientwiseRigidity.Intersections
open Finset Compression
open scoped Classical
noncomputable section
variable {V : Type} {I : Type*} [Fintype I] {M : ℕ}

def incidentRows (J : I → Finset V) (v : V) : Finset I := univ.filter (fun i => v ∈ J i)

def pullbackRows (J : I → Finset V) (σ : I → V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) (v : V) : I → Finset (Fin M) :=
  fun i => (row ((J i).erase v) (σ i) Q).map (σ i v).symm.toEmbedding

theorem column_sum_eq_setOperator (J : I → Finset V) (σ : I → V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) (v : V) (q : ℕ) (F : (I → ℕ) → ℚ) :
    (∑ A : Finset (Fin M), if A.card = q then F (ranks J σ (Function.update Q v A)) else 0) =
      setOperator (incidentRows J v) q F (pullbackRows J σ Q v) (ranks (eraseRows J v) σ Q) := by
  apply Finset.sum_congr rfl
  intro A _
  by_cases hq : A.card = q
  · simp only [hq,if_true]
    congr 1
    funext i
    simp only [ranks,row_update,mixedRanks,incidentRows,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hi : v ∈ J i
    · simp only [hi,if_true,card_map_inter,pullbackRows]
    · simp [hi,eraseRows]
  · simp [hq]

theorem inputRanks_pullback (J : I → Finset V) (σ : I → V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) (v : V) :
    inputRanks (incidentRows J v) (ranks (eraseRows J v) σ Q) (pullbackRows J σ Q v) =
      ranks (eraseRows J v) σ Q := by
  funext i
  simp [inputRanks,pullbackRows,ranks,eraseRows]

theorem column_compression_le (J : I → Finset V) (σ : I → V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) (v : V) (q : ℕ) {F : (I → ℕ) → ℚ} (hF : ProductCone F) :
    (∑ A : Finset (Fin M), if A.card = q then F (ranks J σ (Function.update Q v A)) else 0) ≤
      prefixOperator M (incidentRows J v) q F (ranks (eraseRows J v) σ Q) := by
  rw [column_sum_eq_setOperator]
  simpa only [inputRanks_pullback] using
    hF.compression_le (incidentRows J v) q (pullbackRows J σ Q v) (ranks (eraseRows J v) σ Q)

theorem column_compression_eq_identity (J : I → Finset V) (v : V)
    (hn : Structure.NestPoint (family J) v) (Q : V → Finset (Fin M))
    (q : ℕ) {F : (I → ℕ) → ℚ} (hF : ProductCone F) :
    (∑ A : Finset (Fin M), if A.card = q then F (ranks J (fun _ _ => Equiv.refl _) (Function.update Q v A)) else 0) =
      prefixOperator M (incidentRows J v) q F (ranks (eraseRows J v) (fun _ _ => Equiv.refl _) Q) := by
  rw [column_sum_eq_setOperator]
  have hnest : ∀ i ∈ incidentRows J v, ∀ j ∈ incidentRows J v,
      pullbackRows J (fun _ _ => Equiv.refl _) Q v i ⊆ pullbackRows J (fun _ _ => Equiv.refl _) Q v j ∨
      pullbackRows J (fun _ _ => Equiv.refl _) Q v j ⊆ pullbackRows J (fun _ _ => Equiv.refl _) Q v i := by
    intro i hi j hj
    simp only [incidentRows,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
    simpa [pullbackRows] using identity_residual_nested J v hn Q hi hj
  simpa only [inputRanks_pullback] using hF.compression_eq_of_nested (incidentRows J v) q
    (pullbackRows J (fun _ _ => Equiv.refl _) Q v)
    (ranks (eraseRows J v) (fun _ _ => Equiv.refl _) Q) hnest

omit [Fintype I] in
theorem ranks_eq_identity_of_short_support (P : List V) (hP : P.length ≤ 1)
    (J : I → Finset V) (hs : ∀ i, J i ⊆ P.toFinset)
    (σ : I → V → Equiv.Perm (Fin M)) (Q : V → Finset (Fin M)) :
    ranks J σ Q = ranks J (fun _ _ => Equiv.refl _) Q := by
  cases P with
  | nil =>
    have he : ∀ i, J i = ∅ := fun i => Finset.subset_empty.mp (hs i)
    funext i
    simp [ranks,he]
  | cons root P =>
    have hp0 : P.length = 0 := by simp only [List.length_cons] at hP; omega
    have hpe := List.length_eq_zero.mp hp0
    subst P
    exact ranks_eq_identity_of_single_root J root (by simpa using hs) σ Q

/-- The order includes the retained root. Every induction step uses the true
row traces on the entire remaining suffix, rather than dropping the root. -/
theorem cone_comparison (L P : List V) (hP : P.length ≤ 1)
    (J : I → Finset V) (ho : Structure.NestOrder (family J) (L ++ P))
    (hnd : (L ++ P).Nodup) (hs : ∀ i, J i ⊆ (L ++ P).toFinset)
    (σ : I → V → Equiv.Perm (Fin M)) (q : V → ℕ)
    {F : (I → ℕ) → ℚ} (hF : ProductCone F) (Q : V → Finset (Fin M)) :
    sumColumns q L (fun R => F (ranks J σ R)) Q ≤
      sumColumns q L (fun R => F (ranks J (fun _ _ => Equiv.refl _) R)) Q := by
  induction L generalizing J F with
  | nil =>
    simp only [List.nil_append] at hs
    exact le_of_eq (congrArg F (ranks_eq_identity_of_short_support P hP J hs σ Q))
  | cons v L ih =>
    change Structure.NestOrder (family J) (v :: (L ++ P)) at ho
    cases ho with
    | cons hn ht =>
      have hnd' := List.nodup_cons.mp hnd
      have hv : v ∉ (L ++ P).toFinset := by simpa using hnd'.1
      have hs' : ∀ i, J i ⊆ insert v (L ++ P).toFinset := by simpa using hs
      have htrace := trace_family_erase J v (L ++ P).toFinset hs' hv
      rw [htrace] at ht
      have hsupport : ∀ i, eraseRows J v i ⊆ (L ++ P).toFinset := by
        intro i w hw
        have hw' := Finset.mem_erase.mp hw
        exact (Finset.mem_insert.mp (hs' i hw'.2)).resolve_left hw'.1
      calc
        _ ≤ sumColumns q L (fun R => prefixOperator M (incidentRows J v) (q v) F
              (ranks (eraseRows J v) σ R)) Q :=
          sumColumns_mono q L (fun R => column_compression_le J σ R v (q v) hF) Q
        _ ≤ sumColumns q L (fun R => prefixOperator M (incidentRows J v) (q v) F
              (ranks (eraseRows J v) (fun _ _ => Equiv.refl _) R)) Q :=
          ih (eraseRows J v) ht hnd'.2 hsupport (hF.prefixOperator M (incidentRows J v) (q v))
        _ = _ := sumColumns_congr q L (fun R => (column_compression_eq_identity J v hn R (q v) hF).symm) Q

end
end CoefficientwiseRigidity.Intersections
