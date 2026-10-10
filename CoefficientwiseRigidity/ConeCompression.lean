import CoefficientwiseRigidity.IncreasingProductCone

/-! C2 compression and nested equality for the whole increasing product cone. -/
namespace CoefficientwiseRigidity.Compression
open Finset
open scoped Classical
noncomputable section
variable {I : Type*} [Fintype I] {M : ℕ}

def selectedSets (S : Finset I) (D : I → Finset (Fin M)) : I → Finset (Fin M) :=
  fun i => if i ∈ S then D i else ∅

def selectedProfiles (S : Finset I) (d : I → ℕ) (f : I → ℕ → ℚ) : I → ℕ → ℚ :=
  fun i n => if i ∈ S then f i n else f i (d i)

def inputRanks (S : Finset I) (d : I → ℕ) (D : I → Finset (Fin M)) : I → ℕ :=
  fun i => if i ∈ S then (D i).card else d i

omit [Fintype I] in
theorem selectedProfiles_nonneg (S : Finset I) (d : I → ℕ) (f : I → ℕ → ℚ)
    (hn : ∀ i n, 0 ≤ f i n) : ∀ i n, 0 ≤ selectedProfiles S d f i n := by
  intro i n
  dsimp [selectedProfiles]
  split_ifs <;> exact hn i _

omit [Fintype I] in
theorem selectedProfiles_mono (S : Finset I) (d : I → ℕ) (f : I → ℕ → ℚ)
    (hm : ∀ i, Monotone (f i)) : ∀ i, Monotone (selectedProfiles S d f i) := by
  intro i n m hnm
  dsimp [selectedProfiles]
  split_ifs
  · exact hm i hnm
  · exact le_refl _

theorem setOperator_prod (S : Finset I) (q : ℕ) (f : I → ℕ → ℚ)
    (D : I → Finset (Fin M)) (d : I → ℕ) :
    setOperator S q (fun e => ∏ i, f i (e i)) D d =
      sliceSum q (selectedProfiles S d f) (selectedSets S D) := by
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hq : Q.card = q
  · simp only [hq,if_true,productCost]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · simp only [mixedRanks,selectedProfiles,selectedSets,hi,if_true]
      congr 1
      congr 1
      ext x
      simp only [Finset.mem_inter]
    · simp [mixedRanks,selectedProfiles,selectedSets,hi]
  · simp [hq]

theorem prefixOperator_prod (S : Finset I) (q : ℕ) (f : I → ℕ → ℚ)
    (D : I → Finset (Fin M)) (d : I → ℕ) :
    Compression.prefixOperator M S q (fun e => ∏ i, f i (e i)) (inputRanks S d D) =
      sliceSum q (selectedProfiles S d f) (fun i => initialSegment M ((selectedSets S D i).card)) := by
  unfold prefixOperator setOperator sliceSum
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hq : Q.card = q
  · simp only [hq,if_true,productCost]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · simp only [mixedRanks,inputRanks,selectedProfiles,selectedSets,hi,if_true]
      congr 1
      congr 1
      ext x
      simp only [Finset.mem_inter]
    · simp [mixedRanks,inputRanks,selectedProfiles,selectedSets,hi]
  · simp [hq]

omit [Fintype I] in
theorem setOperator_add (S : Finset I) (q : ℕ) (F G : (I → ℕ) → ℚ)
    (D : I → Finset (Fin M)) (d : I → ℕ) :
    setOperator S q (fun e => F e + G e) D d = setOperator S q F D d + setOperator S q G D d := by
  simp only [setOperator,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q _
  split_ifs <;> simp

omit [Fintype I] in
theorem setOperator_scale (S : Finset I) (q : ℕ) (c : ℚ) (F : (I → ℕ) → ℚ)
    (D : I → Finset (Fin M)) (d : I → ℕ) :
    setOperator S q (fun e => c * F e) D d = c * setOperator S q F D d := by
  simp [setOperator,Finset.mul_sum]

/-- Arbitrary selected rows, with every other coordinate retained exactly. -/
theorem ProductCone.compression_le {F : (I → ℕ) → ℚ} (h : ProductCone F)
    (S : Finset I) (q : ℕ) (D : I → Finset (Fin M)) (d : I → ℕ) :
    setOperator S q F D d ≤ Compression.prefixOperator M S q F (inputRanks S d D) := by
  induction h with
  | zero => simp [setOperator,Compression.prefixOperator]
  | prod f hn hm =>
    rw [setOperator_prod,prefixOperator_prod]
    exact simultaneous_compression q _ (selectedProfiles_nonneg S d f hn)
      (selectedProfiles_mono S d f hm) _
  | add h h' ih ih' =>
    simpa only [Compression.prefixOperator,setOperator_add] using add_le_add ih ih'
  | scale c hc h ih =>
    simpa only [Compression.prefixOperator,setOperator_scale] using mul_le_mul_of_nonneg_left ih hc

theorem ProductCone.compression_eq_of_nested {F : (I → ℕ) → ℚ} (h : ProductCone F)
    (S : Finset I) (q : ℕ) (D : I → Finset (Fin M)) (d : I → ℕ)
    (hD : ∀ i ∈ S, ∀ j ∈ S, D i ⊆ D j ∨ D j ⊆ D i) :
    setOperator S q F D d = Compression.prefixOperator M S q F (inputRanks S d D) := by
  induction h with
  | zero => simp [setOperator,Compression.prefixOperator]
  | prod f hn hm =>
    rw [setOperator_prod,prefixOperator_prod]
    apply simultaneous_compression_eq_of_nested q _ (selectedProfiles_nonneg S d f hn)
      (selectedProfiles_mono S d f hm)
    intro i j
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · simpa only [selectedSets,hi,hj,if_true] using hD i hi j hj
    · simp [selectedSets,hi,hj]
    · simp [selectedSets,hi,hj]
    · simp [selectedSets,hi,hj]
  | add h h' ih ih' => simp only [Compression.prefixOperator,setOperator_add,ih,ih']
  | scale c hc h ih => simp only [Compression.prefixOperator,setOperator_scale,ih]

def cardRank (D : Finset (Fin M)) : Fin (M + 1) :=
  ⟨D.card,by have h := D.card_le_univ; simp only [Fintype.card_fin] at h; omega⟩

theorem clampRank_card (D : Finset (Fin M)) : clampRank M D.card = cardRank D := by
  apply Fin.ext
  exact min_eq_left (by simpa using D.card_le_univ)

theorem clampRank_val (d : Fin (M + 1)) : clampRank M d.val = d := by
  apply Fin.ext
  exact min_eq_left (by have := d.isLt; omega)

def finiteExtension (F : (I → Fin (M + 1)) → ℚ) : (I → ℕ) → ℚ :=
  fun d => F (fun i => clampRank M (d i))

def finiteSetOperator (S : Finset I) (q : ℕ) (F : (I → Fin (M + 1)) → ℚ)
    (D : I → Finset (Fin M)) (d : I → Fin (M + 1)) : ℚ :=
  setOperator S q (finiteExtension F) D (fun i => (d i).val)

def finitePrefixOperator (S : Finset I) (q : ℕ) (F : (I → Fin (M + 1)) → ℚ)
    (d : I → Fin (M + 1)) : ℚ :=
  Compression.prefixOperator M S q (finiteExtension F) (fun i => (d i).val)

omit [Fintype I] in
/-- The finite-domain operator evaluates actual intersection ranks; its
definition by extension introduces no extra monotonicity assumption. -/
theorem finiteSetOperator_apply (S : Finset I) (q : ℕ) (F : (I → Fin (M + 1)) → ℚ)
    (D : I → Finset (Fin M)) (d : I → Fin (M + 1)) :
    finiteSetOperator S q F D d = ∑ Q : Finset (Fin M), if Q.card = q then
      F (fun i => if i ∈ S then cardRank (Q ∩ D i) else d i) else 0 := by
  unfold finiteSetOperator setOperator
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hq : Q.card = q
  · simp only [hq,if_true,finiteExtension]
    congr 1
    funext i
    by_cases hi : i ∈ S <;> simp [mixedRanks,hi,clampRank_card,clampRank_val]
  · simp [hq]

theorem ProductCone.finitePrefixOperator {F : (I → Fin (M + 1)) → ℚ} (h : ProductCone F)
    (S : Finset I) (q : ℕ) : ProductCone (Compression.finitePrefixOperator S q F) :=
  (h.extend_finite.prefixOperator M S q).restrict_finite

theorem ProductCone.finite_compression_le {F : (I → Fin (M + 1)) → ℚ} (h : ProductCone F)
    (S : Finset I) (q : ℕ) (D : I → Finset (Fin M)) (d : I → Fin (M + 1)) :
    finiteSetOperator S q F D d ≤
      Compression.finitePrefixOperator S q F (fun i => if i ∈ S then cardRank (D i) else d i) := by
  have hh := h.extend_finite.compression_le S q D (fun i => (d i).val)
  simpa only [finiteSetOperator,Compression.finitePrefixOperator,finiteExtension,inputRanks,cardRank,apply_ite] using hh

theorem ProductCone.finite_compression_eq_of_nested {F : (I → Fin (M + 1)) → ℚ} (h : ProductCone F)
    (S : Finset I) (q : ℕ) (D : I → Finset (Fin M)) (d : I → Fin (M + 1))
    (hD : ∀ i ∈ S, ∀ j ∈ S, D i ⊆ D j ∨ D j ⊆ D i) :
    finiteSetOperator S q F D d =
      Compression.finitePrefixOperator S q F (fun i => if i ∈ S then cardRank (D i) else d i) := by
  have hh := h.extend_finite.compression_eq_of_nested S q D (fun i => (d i).val) hD
  simpa only [finiteSetOperator,Compression.finitePrefixOperator,finiteExtension,inputRanks,cardRank,apply_ite] using hh

end
end CoefficientwiseRigidity.Compression
