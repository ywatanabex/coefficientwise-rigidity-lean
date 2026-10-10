import CoefficientwiseRigidity.NetworkReserveValue
import CoefficientwiseRigidity.NetworkRigidStep

/-!
W3 on actual simple width-two networks. All branches use the same concrete
forward-difference reserve, and induction is on the number of vertices.
-/
namespace CoefficientwiseRigidity
open Kernel Finset
open scoped Classical
noncomputable section

theorem treewidth_mono {V : Type} [Fintype V] {G H : SimpleGraph V}
    (hH : TreewidthAtMostTwo H) (hle : G ≤ H) : TreewidthAtMostTwo G := by
  obtain ⟨n,T,B,ht,hs,hc,he,hr⟩ := hH
  exact ⟨n,T,B,ht,hs,hc,fun u v huv => he u v (hle huv),hr⟩

namespace Network
variable {M : ℕ} {V : Type} [Fintype V] {p : V → ℕ}

/-- A newly composed edge may meet an existing edge. Extract that actual factor
and use the proved three-way parallel step; every recursive branch is simple. -/
theorem Net.addSingle_kappa_step (N : Net (M + 2) p)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hs : N.Simple) (G : SimpleGraph V) (hw : TreewidthAtMostTwo G)
    (hE : ∀ e ∈ N.edges, G.Adj e.left e.right)
    (u v : V) (huv : u ≠ v) (hfill : G.Adj u v) (e : GainEntry (M + 2) (p u) (p v))
    (he : e.Nonconstant) (heΓ : e.gain ∈ Γ) (hn : ¬ (N.addEdge u v huv [e]).Flat)
    (hrec : ∀ R : Net (M + 2) p, R.Rigid Γ → R.Simple →
      (∀ f ∈ R.edges, G.Adj f.left f.right) → ¬ R.Flat →
      kappa (M + 2) Γ * R.reserveValue ≤ R.value true - R.value false) :
    kappa (M + 2) Γ * (N.addEdge u v huv [e]).reserveValue ≤
      (N.addEdge u v huv [e]).value true - (N.addEdge u v huv [e]).value false := by
  obtain ⟨q,rfl⟩ := exists_successor_ranks (fun v => (hp v).1)
  dsimp only at hp e
  have hq (v : V) : q v ≤ M := by have := (hp v).2; omega
  by_cases ha : N.graph.Adj u v
  · obtain ⟨R,f,hc,hx,hf,hfΓ,hR,hRs,hnot,_⟩ := N.extract_rigid_edge Γ hr hs u v huv ha
    let P := (R.addEdge u v huv [f]).addEdge u v huv [e]
    have hx' : EdgeListEquiv (N.addEdge u v huv [e]).edges P.edges := .cons _ hx
    have hval (b : Bool) : (N.addEdge u v huv [e]).value b = P.value b :=
      Net.value_exact (N.addEdge u v huv [e]) P hc.symm hx' b
    have hres : (N.addEdge u v huv [e]).reserveValue = P.reserveValue :=
      Net.reserveValue_exact (N.addEdge u v huv [e]) P hc.symm hx'
    have hnon : ¬ P.Flat := fun h => hn ((Net.flat_exact _ _ hx').mpr h)
    have hRsup : ∀ g ∈ R.edges, G.Adj g.left g.right := by
      intro g hg
      exact (hx.supported_iff G).mp hE g (List.mem_cons_of_mem _ hg)
    have hsup (g : GainEntry (M + 2) (q u + 1) (q v + 1)) :
        ∀ j ∈ (R.addEdge u v huv [g]).edges, G.Adj j.left j.right := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hfill
      · exact hRsup j hj
    have hb := R.parallel_kappa_step hq Γ hR.hasEntries u v huv e f he hf heΓ hfΓ
      (treewidth_mono hw ((Net.graph_le_iff _ G).mpr (hsup e))) hnon (by
        intro g hg hgΓ hgn
        have hi := hrec (R.addEdge u v huv [g])
          ((R.rigid_addSingle_iff u v huv g Γ).mpr ⟨hg,hgΓ,hR⟩)
          ((R.simple_addSingle_iff u v huv g).mpr ⟨hRs,hnot⟩) (hsup g) hgn
        rwa [Net.reserveValue_eq_reduce _ hq] at hi)
    rw [hval true, hval false, hres]
    rwa [Net.reserveValue_eq_reduce _ hq]
  · apply hrec
    · exact (N.rigid_addSingle_iff u v huv e Γ).mpr ⟨he,heΓ,hr⟩
    · exact (N.simple_addSingle_iff u v huv e).mpr ⟨hs,ha⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hfill
      · exact hE f hf
    · exact hn

private theorem scaled_reserve_bound {k c d R D : ℚ} (hk : 0 ≤ k) (hR : 0 ≤ R)
    (hc : 0 ≤ c) (hd : d ≤ c) (h : k * R ≤ D) : k * (d * R) ≤ c * D := by
  calc
    k * (d * R) ≤ k * (c * R) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hd hR) hk
    _ = c * (k * R) := by ring
    _ ≤ c * D := mul_le_mul_of_nonneg_left h hc

theorem choose_pred_le (M m : ℕ) : M.choose (m - 1) ≤ (M + 2).choose m := by
  cases m with
  | zero => simp
  | succ k =>
    simpa only [Nat.succ_sub_one, Nat.choose_succ_succ] using
      (Nat.choose_le_succ M k).trans (Nat.le_add_right ((M + 1).choose k) ((M + 1).choose (k + 1)))

omit [Fintype V] in
theorem compose_nonconstant_interior {a b c : ℕ}
    (e : GainEntry (M + 2) a b) (f : GainEntry (M + 2) b c)
    (ha : 0 < a ∧ a < M + 2) (hb : 0 < b ∧ b < M + 2) (hc : 0 < c ∧ c < M + 2)
    (he : e.Nonconstant) (hf : f.Nonconstant) :
    (e.compose (Nat.le_of_lt ha.2) (Nat.le_of_lt hb.2) (Nat.le_of_lt hc.2) f).Nonconstant := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha.1)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb.1)
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc.1)
  exact e.compose_nonconstant f (by omega) (by omega) (by omega) he hf

/-- The quantitative star step, with the smaller-vertex bound as induction hypothesis. -/
theorem Net.star_kappa (N : Net (M + 2) p) (m : ℕ) {S : List V}
    (K : Spokes (M + 2) p m S) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hs : N.Simple) (hK : K.Rigid Γ) (hnd : S.Nodup) (hsize : S.length ≤ 2)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (hm : 0 < m ∧ m < M + 2)
    (G : SimpleGraph V) (hw : TreewidthAtMostTwo G) (hE : ∀ e ∈ N.edges, G.Adj e.left e.right)
    (hfill : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)
    (hn : ¬ (N.attachSpokes m K).Flat)
    (hrec : ∀ R : Net (M + 2) p, R.Rigid Γ → R.Simple →
      (∀ f ∈ R.edges, G.Adj f.left f.right) → ¬ R.Flat →
      kappa (M + 2) Γ * R.reserveValue ≤ R.value true - R.value false) :
    kappa (M + 2) Γ * (N.attachSpokes m K).reserveValue ≤
      (N.attachSpokes m K).value true - (N.attachSpokes m K).value false := by
  cases K with
  | nil =>
    have hflat : ¬ N.Flat := fun h => hn ((N.flat_lift_iff m).mpr h)
    have hi := hrec N hr hs hE hflat
    have hle : (M.choose (m - 1) : ℚ) ≤ (M + 2).choose m := by exact_mod_cast choose_pred_le M m
    simpa only [Net.attachSpokes, Net.reserveValue_lift, Net.isolated_value, mul_sub] using
      scaled_reserve_bound (kappa_nonneg Γ) (N.reserveValue_nonneg hp)
        (Nat.cast_nonneg ((M + 2).choose m)) hle hi
  | @cons S u L K =>
    obtain ⟨⟨e,rfl,he,heΓ⟩,hK⟩ := hK
    cases K with
    | nil =>
      have hflat : ¬ N.Flat := fun h => hn ((N.flat_attachLeaf_iff m u e).mpr h)
      have hi := hrec N hr hs hE hflat
      obtain ⟨c,_,hle,hval⟩ := N.reserveValue_leaf m u hp hm e
      change kappa (M + 2) Γ * (N.attachLeaf m u [e]).reserveValue ≤
        (N.attachLeaf m u [e]).value true - (N.attachLeaf m u [e]).value false
      rw [hval, N.leaf_value m u (Nat.le_of_lt (hp u).2) [e] true,
        N.leaf_value m u (Nat.le_of_lt (hp u).2) [e] false]
      simpa only [mul_sub] using scaled_reserve_bound (kappa_nonneg Γ)
        (N.reserveValue_nonneg hp) (rowMass_nonneg (Nat.le_of_lt (hp u).2) [e]) hle hi
    | @cons T v L K =>
      obtain ⟨⟨f,rfl,hf,hfΓ⟩,hK⟩ := hK
      have huv : u ≠ v := by
        have := (List.nodup_cons.mp hnd).1
        simp only [List.mem_cons, not_or] at this
        exact this.1
      cases K with
      | nil =>
        let g := e.compose (Nat.le_of_lt (hp u).2) (Nat.le_of_lt hm.2)
          (Nat.le_of_lt (hp v).2) f.reverse
        have hg : g.Nonconstant := compose_nonconstant_interior e f.reverse
          (hp u) hm (hp v) he ((gainEntry_nonconstant_reverse_iff f).mpr hf)
        have hgΓ : g.gain ∈ Γ := Γ.mul_mem heΓ (Γ.inv_mem hfΓ)
        have hx := N.twoSpokes_exact m u v e f
        have hseries : ¬ (N.attachSeries m u v [e] [f.reverse]).Flat :=
          fun h => hn ((Net.flat_exact _ _ hx).mpr h)
        have hnon : ¬ (N.addEdge u v huv [g]).Flat := fun h => hseries
          ((N.flat_attachSeries_iff m u v huv _ _ _ e f.reverse).mpr h)
        have hi := N.addSingle_kappa_step hp Γ hr hs G hw hE u v huv
          (hfill u (by simp) v (by simp) huv) g hg hgΓ hnon hrec
        have hres := Net.reserveValue_exact
          (N.attachSpokes m (.cons u [e] (.cons v [f] .nil)))
          (N.attachSeries m u v [e] [f.reverse]) rfl hx
        rw [N.reserveValue_series m u v huv hp hm e f.reverse] at hres
        have hval (b : Bool) : (N.attachSpokes m (.cons u [e] (.cons v [f] .nil))).value b =
            (N.addEdge u v huv [g]).value b := by
          rw [Net.value_exact (N.attachSpokes m (.cons u [e] (.cons v [f] .nil)))
            (N.attachSeries m u v [e] [f.reverse]) rfl hx b, Net.series_value N m u v huv
            (Nat.le_of_lt (hp u).2) (Nat.le_of_lt hm.2) (Nat.le_of_lt (hp v).2)]
          rfl
        rw [hval true, hval false, hres]
        exact hi
      | cons w L K => simp only [List.length_cons] at hsize; omega

private theorem treewidth_kappa_aux (M n : ℕ) :
    ∀ (V : Type) [Fintype V] (p : V → ℕ) (N : Net (M + 2) p),
      Fintype.card V = n → (∀ v, 0 < p v ∧ p v < M + 2) →
      ∀ Γ : Subgroup (Equiv.Perm (Fin (M + 2))), N.Rigid Γ → N.Simple →
      TreewidthAtMostTwo N.graph → ¬ N.Flat →
      kappa (M + 2) Γ * N.reserveValue ≤ N.value true - N.value false := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ p N hcard hp Γ hr hs hw hn
    cases isEmpty_or_nonempty V with
    | inl h =>
      haveI := h
      apply False.elim (hn ?_)
      refine ⟨fun _ => Equiv.refl _, ?_⟩
      intro e _ _ _ _
      exact False.elim (isEmptyElim e.left : False)
    | inr h =>
      haveI := h
      obtain ⟨v,R,S,K,hc,hx,hR,hK,hRs,hS,hsize,hlt,hw',hE,hfill⟩ :=
        N.low_degree_rigid_presentation Γ hr hs hw
      have hscalar : (N.atVertex v).scalar = (R.attachSpokes (p v) K).scalar := by
        rw [Net.attachSpokes_scalar, hc]
        rw [Net.atVertex, Net.changeRanks_scalar]
        rfl
      have hval (b : Bool) : (R.attachSpokes (p v) K).value b = N.value b := by
        rw [← Net.value_exact _ _ hscalar hx b, Net.atVertex_value]
      have hres : (R.attachSpokes (p v) K).reserveValue = N.reserveValue := by
        rw [← Net.reserveValue_exact _ _ hscalar hx, Net.reserveValue_atVertex]
      have hflat : ¬ (R.attachSpokes (p v) K).Flat := fun h => hn
        ((N.atVertex_flat v).mp ((Net.flat_exact _ _ hx).mpr h))
      have hi := R.star_kappa (p v) K Γ hR hRs hK hS hsize
        (fun w => hp w.val) (hp v) (Structure.smooth N.graph v) hw' hE hfill hflat (by
          intro Q hQr hQs hQE hQn
          apply ih (Fintype.card {w : V // w ≠ v}) (by omega)
            {w : V // w ≠ v} (fun w => p w.val) Q rfl (fun w => hp w.val) Γ hQr hQs
          · exact treewidth_mono hw' ((Q.graph_le_iff _).mpr hQE)
          · exact hQn)
      simpa only [hval, hres] using hi

/-- W3 with no elimination or quantitative induction premise. The ranks are
interior; each simple edge carries exactly one nonconstant Newton-cone entry.
Disconnected networks and scalar zero are allowed. -/
theorem Net.kappa_of_treewidth (N : Net (M + 2) p)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hs : N.Simple) (hw : TreewidthAtMostTwo N.graph) (hn : ¬ N.Flat) :
    kappa (M + 2) Γ * N.reserveValue ≤ N.value true - N.value false :=
  treewidth_kappa_aux M (Fintype.card V) V p N rfl hp Γ hr hs hw hn

/-- The same unconditional W3 bound for the original `Net.reduce` reserve. -/
theorem Net.reduce_kappa_of_treewidth (N : Net (M + 2) (fun v => p v + 1))
    (hp : ∀ v, p v ≤ M) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hs : N.Simple) (hw : TreewidthAtMostTwo N.graph) (hn : ¬ N.Flat) :
    kappa (M + 2) Γ * (N.reduce hp).value true ≤ N.value true - N.value false := by
  rw [← N.reserveValue_eq_reduce hp]
  apply N.kappa_of_treewidth _ Γ hr hs hw hn
  intro v
  have := hp v
  omega

omit [Fintype V] in
theorem Net.Rigid.group_nontrivial {N : Net (M + 2) p}
    {Γ : Subgroup (Equiv.Perm (Fin (M + 2)))} (hr : N.Rigid Γ) (hn : ¬ N.Flat) :
    ∃ σ : Equiv.Perm (Fin (M + 2)), σ ∈ Γ ∧ σ ≠ 1 := by
  by_contra h
  push_neg at h
  apply hn
  refine ⟨fun _ => Equiv.refl _, ?_⟩
  intro e he f hf i
  obtain ⟨g,hg,_,hgΓ⟩ := hr e he
  have hfg : f = g := by simpa only [hg, List.mem_singleton] using hf
  subst f
  simp only [h g.gain hgΓ, Equiv.Perm.one_apply, Equiv.refl_apply]

theorem Net.reserveValue_pos (N : Net (M + 2) p)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hc : 0 < N.scalar) : 0 < N.reserveValue := by
  obtain ⟨q,rfl⟩ := exists_successor_ranks (fun v => (hp v).1)
  dsimp only at hp
  rw [N.reserveValue_eq_reduce (fun v => by have := (hp v).2; omega)]
  apply N.reduce_value_pos _ hc
  intro e he
  obtain ⟨f,hf,hn,_⟩ := hr e he
  exact ⟨f, by simp [hf], hn⟩

theorem Net.two_of_treewidth (N : Net (M + 2) p)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hs : N.Simple) (hw : TreewidthAtMostTwo N.graph) (hn : ¬ N.Flat) :
    2 * N.reserveValue ≤ N.value true - N.value false :=
  (mul_le_mul_of_nonneg_right (two_le_kappa Γ (hr.group_nontrivial hn))
    (N.reserveValue_nonneg hp)).trans (N.kappa_of_treewidth hp Γ hr hs hw hn)

theorem Net.three_of_treewidth_of_odd (N : Net (M + 2) p)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hs : N.Simple) (hw : TreewidthAtMostTwo N.graph) (hn : ¬ N.Flat)
    (hodd : Odd (Nat.card Γ)) : 3 * N.reserveValue ≤ N.value true - N.value false :=
  (mul_le_mul_of_nonneg_right (three_le_kappa_of_odd Γ (hr.group_nontrivial hn) hodd)
    (N.reserveValue_nonneg hp)).trans (N.kappa_of_treewidth hp Γ hr hs hw hn)

theorem Net.value_eq_iff_flat_of_treewidth (N : Net (M + 2) p)
    (hp : ∀ v, 0 < p v ∧ p v < M + 2) (Γ : Subgroup (Equiv.Perm (Fin (M + 2))))
    (hr : N.Rigid Γ) (hc : 0 < N.scalar) (hs : N.Simple) (hw : TreewidthAtMostTwo N.graph) :
    N.value false = N.value true ↔ N.Flat := by
  constructor
  · intro he
    by_contra hn
    have h := N.two_of_treewidth hp Γ hr hs hw hn
    have hR := N.reserveValue_pos hp Γ hr hc
    linarith
  · exact fun h => h.value_eq

end Network
end
end CoefficientwiseRigidity
