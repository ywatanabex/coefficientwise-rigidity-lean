import CoefficientwiseRigidity.NetworkQuantitativeSplit

/-!
Exact packing for rigidity. Only edge order and orientation change; no kernel
is merged and no dummy edge is inserted. This preserves the actual reserve,
flatness and the single nonconstant entry invariant needed by W3.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M m : ℕ} {V : Type} {p : V → ℕ}

def Edge.key (e : Edge M p) : Sym2 V := s(e.left, e.right)

@[simp] theorem Edge.key_reverse (e : Edge M p) : e.reverse.key = e.key :=
  Sym2.eq_swap

/-- A purely structural equivalence of lists of actual factors. -/
inductive EdgeListEquiv : List (Edge M p) → List (Edge M p) → Prop where
  | perm {E F} (h : E.Perm F) : EdgeListEquiv E F
  | reverse (e : Edge M p) (E) : EdgeListEquiv (e :: E) (e.reverse :: E)
  | cons (e) {E F} (h : EdgeListEquiv E F) : EdgeListEquiv (e :: E) (e :: F)
  | trans {E F H} (h : EdgeListEquiv E F) (k : EdgeListEquiv F H) : EdgeListEquiv E H

theorem EdgeListEquiv.refl (E : List (Edge M p)) : EdgeListEquiv E E :=
  .perm (.refl _)

theorem EdgeListEquiv.map_perm {α : Type*} {E F : List (Edge M p)}
    (h : EdgeListEquiv E F) (f : Edge M p → α) (hf : ∀ e, f e.reverse = f e) :
    (E.map f).Perm (F.map f) := by
  induction h with
  | perm h => exact h.map f
  | reverse e E => simp only [List.map_cons, hf]; exact .refl _
  | cons e h ih => exact .cons _ ih
  | trans h k ih ik => exact ih.trans ik

theorem EdgeListEquiv.forall_iff {E F : List (Edge M p)} (h : EdgeListEquiv E F)
    (Q : Edge M p → Prop) (hQ : ∀ e, Q e.reverse ↔ Q e) :
    (∀ e ∈ E, Q e) ↔ ∀ e ∈ F, Q e := by
  induction h with
  | perm h => exact ⟨fun hQ e he => hQ e (h.mem_iff.mpr he),
      fun hQ e he => hQ e (h.mem_iff.mp he)⟩
  | reverse e E => simp only [List.forall_mem_cons, hQ]
  | cons e h ih => simpa only [List.forall_mem_cons] using and_congr_right (fun _ => ih)
  | trans h k ih ik => exact ih.trans ik

theorem EdgeListEquiv.weight_eq {E F : List (Edge M p)} (h : EdgeListEquiv E F)
    (b : Bool) (A : State M p) : weight E b A = weight F b A :=
  (h.map_perm (fun e => e.eval b A) (fun e => e.reverse_eval b A)).prod_eq

theorem EdgeListEquiv.length_eq {E F : List (Edge M p)} (h : EdgeListEquiv E F) :
    E.length = F.length := by
  simpa only [List.length_map] using (h.map_perm Edge.key Edge.key_reverse).length_eq

theorem EdgeListEquiv.keys_perm {E F : List (Edge M p)} (h : EdgeListEquiv E F) :
    (E.map Edge.key).Perm (F.map Edge.key) := h.map_perm _ Edge.key_reverse

private theorem reverse_gauge (e : Edge M p) (γ : V → Equiv.Perm (Fin M)) :
    (∀ f ∈ e.reverse.kernels, ∀ i, f.gain (γ e.reverse.right i) = γ e.reverse.left i) ↔
      ∀ f ∈ e.kernels, ∀ i, f.gain (γ e.right i) = γ e.left i := by
  simp only [Edge.reverse, reverseList, List.forall_mem_map, GainEntry.reverse]
  constructor
  · intro h f hf i
    have := congrArg f.gain (h f hf i)
    simpa using this.symm
  · intro h f hf i
    have := congrArg f.gain.symm (h f hf i)
    simpa using this.symm

theorem EdgeListEquiv.gauge_iff {E F : List (Edge M p)} (h : EdgeListEquiv E F)
    (γ : V → Equiv.Perm (Fin M)) :
    (∀ e ∈ E, ∀ f ∈ e.kernels, ∀ i, f.gain (γ e.right i) = γ e.left i) ↔
      ∀ e ∈ F, ∀ f ∈ e.kernels, ∀ i, f.gain (γ e.right i) = γ e.left i :=
  h.forall_iff _ (fun e => reverse_gauge e γ)

theorem EdgeListEquiv.reduce_weight_eq
    {E F : List (Edge (M + 2) (fun v => p v + 1))} (h : EdgeListEquiv E F)
    (hp : ∀ v, p v ≤ M) (A : State M p) :
    weight (E.map fun e => e.reduce hp) true A =
      weight (F.map fun e => e.reduce hp) true A := by
  have hr (e : Edge (M + 2) (fun v => p v + 1)) :
      (e.reverse.reduce hp).eval true A = (e.reduce hp).eval true A := by
    simp [Edge.reverse, Edge.reduce, Edge.eval, kernel, reduceList, reverseList,
      listOrdinary, GainEntry.ordinary, GainEntry.reduce, GainEntry.reverse,
      Function.comp_def, overlap_symm (A e.right) (A e.left)]
  simpa only [weight, List.map_map, Function.comp_def] using
    (h.map_perm (fun e => (e.reduce hp).eval true A) hr).prod_eq

def Net.Simple (N : Net M p) : Prop := (N.edges.map Edge.key).Nodup

def Edge.Rigid (Γ : Subgroup (Equiv.Perm (Fin M))) (e : Edge M p) : Prop :=
  ∃ f, e.kernels = [f] ∧ f.Nonconstant ∧ f.gain ∈ Γ

def Net.Rigid (Γ : Subgroup (Equiv.Perm (Fin M))) (N : Net M p) : Prop :=
  ∀ e ∈ N.edges, e.Rigid Γ

theorem gainEntry_nonconstant_reverse_iff {a b : ℕ} (f : GainEntry M a b) :
    f.reverse.Nonconstant ↔ f.Nonconstant := by
  simp only [GainEntry.Nonconstant, GainEntry.reverse, overlapRank, overlapShift,
    min_comm a b, add_comm a b]

theorem Edge.rigid_reverse_iff (e : Edge M p) (Γ : Subgroup (Equiv.Perm (Fin M))) :
    e.reverse.Rigid Γ ↔ e.Rigid Γ := by
  constructor
  · rintro ⟨f, hf, hn, hg⟩
    have hl : e.kernels.length = 1 := by
      have := congrArg List.length hf
      simpa [Edge.reverse, reverseList] using this
    obtain ⟨g, hE⟩ := List.length_eq_one.mp hl
    have hfg : g.reverse = f := by simpa [Edge.reverse, reverseList, hE] using hf
    subst f
    exact ⟨g, hE, (gainEntry_nonconstant_reverse_iff g).mp hn, Γ.inv_mem hg⟩
  · rintro ⟨f, hf, hn, hg⟩
    refine ⟨f.reverse, by simp [Edge.reverse, reverseList, hf],
      (gainEntry_nonconstant_reverse_iff f).mpr hn, ?_⟩
    exact Γ.inv_mem hg

theorem Net.Rigid.hasEntries {Γ : Subgroup (Equiv.Perm (Fin M))} {N : Net M p}
    (h : N.Rigid Γ) : N.HasEntries := by
  intro e he
  obtain ⟨f, hf, _⟩ := h e he
  simp [hf]

/-- All network invariants are inherited from the structural list relation. -/
theorem Net.exact_value [Fintype V] (N : Net M p) (F : List (Edge M p))
    (h : EdgeListEquiv N.edges F) (b : Bool) :
    ({N with edges := F} : Net M p).value b = N.value b := by
  unfold Net.value
  congr 1
  exact Finset.sum_congr rfl (fun A _ => (h.weight_eq b A).symm)

theorem Net.exact_flat (N : Net M p) (F : List (Edge M p))
    (h : EdgeListEquiv N.edges F) : ({N with edges := F} : Net M p).Flat ↔ N.Flat := by
  exact exists_congr (fun γ => (h.gauge_iff γ).symm)

theorem Net.exact_rigid (N : Net M p) (F : List (Edge M p))
    (h : EdgeListEquiv N.edges F) (Γ : Subgroup (Equiv.Perm (Fin M))) :
    ({N with edges := F} : Net M p).Rigid Γ ↔ N.Rigid Γ :=
  (h.forall_iff _ (fun e => e.rigid_reverse_iff Γ)).symm

theorem Net.exact_simple (N : Net M p) (F : List (Edge M p))
    (h : EdgeListEquiv N.edges F) : ({N with edges := F} : Net M p).Simple ↔ N.Simple :=
  h.keys_perm.nodup_iff.symm

theorem Net.exact_reduce_value [Fintype V]
    (N : Net (M + 2) (fun v => p v + 1)) (F : List (Edge (M + 2) (fun v => p v + 1)))
    (h : EdgeListEquiv N.edges F) (hp : ∀ v, p v ≤ M) :
    (({N with edges := F} : Net (M + 2) (fun v => p v + 1)).reduce hp).value true =
      (N.reduce hp).value true := by
  unfold Net.value Net.reduce
  congr 1
  exact Finset.sum_congr rfl (fun A _ => (h.reduce_weight_eq hp A).symm)

def Spokes.edges {S : List V} (K : Spokes M p m S) : List (Edge M (extendRanks m p)) :=
  match K with
  | .nil => []
  | .cons u L K => ⟨some u, none, by simp, L⟩ :: K.edges

theorem Net.attachSpokes_edges (N : Net M p) {S : List V} (K : Spokes M p m S) :
    (N.attachSpokes m K).edges = K.edges ++ N.edges.map (liftEdge m) := by
  induction K with
  | nil => rfl
  | cons u L K ih =>
    simp only [Net.attachSpokes, Net.addEdge, Spokes.edges, List.cons_append]
    rw [ih]

/-- Every incident factor becomes one spoke; the neighbour list may initially repeat. -/
theorem pack_edges_exact (E : List (Edge M (extendRanks m p))) :
    ∃ (R : List (Edge M p)) (S : List V) (K : Spokes M p m S),
      EdgeListEquiv E (K.edges ++ R.map (liftEdge m)) := by
  induction E with
  | nil => exact ⟨[], [], .nil, .refl _⟩
  | cons e E ih =>
    obtain ⟨R,S,K,hK⟩ := ih
    rcases e with ⟨l,r,hd,L⟩
    cases l with
    | none =>
      cases r with
      | none => exact False.elim (hd rfl)
      | some u =>
        refine ⟨R, u :: S, .cons u (reverseList L) K, ?_⟩
        exact (EdgeListEquiv.reverse _ _).trans (.cons _ hK)
    | some u =>
      cases r with
      | none => exact ⟨R, u :: S, .cons u L K, .cons _ hK⟩
      | some w =>
        let f : Edge M p := ⟨u,w,fun h => hd (congrArg some h),L⟩
        refine ⟨f :: R,S,K, (EdgeListEquiv.cons _ hK).trans (.perm ?_)⟩
        exact List.perm_middle.symm

theorem Net.pack_exact (N : Net M (extendRanks m p)) :
    ∃ (R : Net M p) (S : List V) (K : Spokes M p m S),
      R.scalar = N.scalar ∧ EdgeListEquiv N.edges (R.attachSpokes m K).edges := by
  obtain ⟨R,S,K,h⟩ := pack_edges_exact N.edges
  refine ⟨⟨N.scalar,N.scalar_nonneg,R⟩,S,K,rfl,?_⟩
  rwa [Net.attachSpokes_edges]

theorem EdgeListEquiv.supported_iff {E F : List (Edge M p)} (h : EdgeListEquiv E F)
    (G : SimpleGraph V) :
    (∀ e ∈ E, G.Adj e.left e.right) ↔ ∀ e ∈ F, G.Adj e.left e.right :=
  h.forall_iff _ (fun e => G.adj_comm e.right e.left)

theorem Net.graph_le_iff (N : Net M p) (G : SimpleGraph V) :
    N.graph ≤ G ↔ ∀ e ∈ N.edges, G.Adj e.left e.right := by
  constructor
  · intro h e he
    exact h ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  · intro h u v
    rintro ⟨e,he,h' | h'⟩
    · exact h'.1 ▸ h'.2 ▸ h e he
    · exact h'.2 ▸ h'.1 ▸ (h e he).symm

theorem Net.exact_graph (N : Net M p) (F : List (Edge M p))
    (h : EdgeListEquiv N.edges F) : ({N with edges := F} : Net M p).graph = N.graph := by
  apply le_antisymm
  · apply (Net.graph_le_iff _ _).mpr
    apply (h.supported_iff _).mp
    exact (N.graph_le_iff _).mp le_rfl
  · apply (N.graph_le_iff _).mpr
    apply (h.supported_iff _).mpr
    intro e he
    exact ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem Spokes.keys {S : List V} (K : Spokes M p m S) :
    K.edges.map Edge.key = S.map (fun u => s(some u, (none : Option V))) := by
  induction K with
  | nil => rfl
  | cons u L K ih => simp only [Spokes.edges, List.map_cons, Edge.key, ih]

theorem Spokes.nodup_of_simple (N : Net M p) {S : List V} (K : Spokes M p m S)
    (h : (N.attachSpokes m K).Simple) : S.Nodup := by
  unfold Net.Simple at h
  rw [Net.attachSpokes_edges, List.map_append, List.nodup_append] at h
  rw [K.keys] at h
  exact h.1.of_map _

theorem Net.simple_of_attachSpokes (N : Net M p) {S : List V} (K : Spokes M p m S)
    (h : (N.attachSpokes m K).Simple) : N.Simple := by
  unfold Net.Simple at h ⊢
  rw [Net.attachSpokes_edges, List.map_append, List.nodup_append] at h
  have he : (N.edges.map (liftEdge m)).map Edge.key =
      (N.edges.map Edge.key).map (Sym2.map some) := by
    simp only [List.map_map, Function.comp_def, Edge.key, liftEdge, Sym2.map_pair_eq]
  rw [he] at h
  exact h.2.1.of_map _

def Spokes.Rigid (Γ : Subgroup (Equiv.Perm (Fin M))) {S : List V}
    (K : Spokes M p m S) : Prop :=
  match K with
  | .nil => True
  | .cons _ L K => (∃ f, L = [f] ∧ f.Nonconstant ∧ f.gain ∈ Γ) ∧ K.Rigid Γ

theorem Net.rigid_attachSpokes_iff (N : Net M p) {S : List V} (K : Spokes M p m S)
    (Γ : Subgroup (Equiv.Perm (Fin M))) :
    (N.attachSpokes m K).Rigid Γ ↔ K.Rigid Γ ∧ N.Rigid Γ := by
  induction K with
  | nil =>
    simp only [Net.attachSpokes, Net.Rigid, Net.lift, List.forall_mem_map,
      Spokes.Rigid, true_and]
    rfl
  | cons u L K ih =>
    simp only [Net.attachSpokes, Net.Rigid, Net.addEdge, List.forall_mem_cons]
    change ((∃ f, L = [f] ∧ f.Nonconstant ∧ f.gain ∈ Γ) ∧
      (N.attachSpokes m K).Rigid Γ) ↔ _
    rw [ih]
    exact and_assoc.symm

theorem Spokes.supported (N : Net M p) {S : List V} (K : Spokes M p m S)
    (H : SimpleGraph (Option V))
    (h : ∀ e ∈ (N.attachSpokes m K).edges, H.Adj e.left e.right) :
    (∀ u ∈ S, H.Adj none (some u)) ∧
      (∀ e ∈ N.edges, H.Adj (some e.left) (some e.right)) := by
  induction K with
  | nil =>
    constructor
    · simp
    · intro e he
      exact h (liftEdge m e) (List.mem_map.mpr ⟨e,he,rfl⟩)
  | cons u L K ih =>
    have hh := h ⟨some u,none,by simp,L⟩ (List.mem_cons_self _ _)
    have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    refine ⟨?_, ht.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hh.symm
    · exact ht.1 w hw

/-- A simple network has an exact star presentation with at most the actual
neighbours. In particular, a degree-two vertex gives zero, one or two spokes. -/
theorem Net.pack_rigid_simple (N : Net M (extendRanks m p))
    (Γ : Subgroup (Equiv.Perm (Fin M))) (hr : N.Rigid Γ) (hs : N.Simple)
    (H : SimpleGraph (Option V))
    (hH : ∀ e ∈ N.edges, H.Adj e.left e.right)
    (T : Finset V) (hT : ∀ u, H.Adj none (some u) → u ∈ T) :
    ∃ (R : Net M p) (S : List V) (K : Spokes M p m S),
      R.scalar = N.scalar ∧ EdgeListEquiv N.edges (R.attachSpokes m K).edges ∧
      R.Rigid Γ ∧ K.Rigid Γ ∧ R.Simple ∧ S.Nodup ∧ S.length ≤ T.card ∧
      (∀ u ∈ S, u ∈ T) ∧ (∀ e ∈ R.edges, H.Adj (some e.left) (some e.right)) := by
  classical
  obtain ⟨R,S,K,hc,he⟩ := N.pack_exact
  have heq : ({N with edges := (R.attachSpokes m K).edges} : Net M (extendRanks m p)) =
      R.attachSpokes m K := by
    cases N
    cases h : R.attachSpokes m K
    have := R.attachSpokes_scalar K
    simp only [h] at this
    simp_all
  have hr' : (R.attachSpokes m K).Rigid Γ := by
    rw [← heq]
    exact (N.exact_rigid _ he Γ).mpr hr
  obtain ⟨hK,hR⟩ := (R.rigid_attachSpokes_iff K Γ).mp hr'
  have hs' : (R.attachSpokes m K).Simple := by
    rw [← heq]
    exact (N.exact_simple _ he).mpr hs
  have hnd := K.nodup_of_simple R hs'
  obtain ⟨hS,hE⟩ := K.supported R H ((he.supported_iff H).mp hH)
  have hsub : S.toFinset ⊆ T := fun u hu => hT u (hS u (List.mem_toFinset.mp hu))
  refine ⟨R,S,K,hc,he,hR,hK,R.simple_of_attachSpokes K hs',hnd,?_,?_,hE⟩
  · rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card hsub
  · exact fun u hu => hT u (hS u hu)

theorem Net.rigid_rename {W : Type} (N : Net M p) (e : V ≃ W)
    (Γ : Subgroup (Equiv.Perm (Fin M))) (h : N.Rigid Γ) : (N.rename e).Rigid Γ := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨f,hf,hn,hΓ⟩ := h g hg
  refine ⟨renameEntry e g.left g.right f, ?_, ?_, hΓ⟩
  · simp [Edge.rename, hf]
  · simpa [GainEntry.Nonconstant, renameEntry, Edge.rename, Function.comp_def] using hn

theorem Net.simple_rename {W : Type} (N : Net M p) (e : V ≃ W)
    (h : N.Simple) : (N.rename e).Simple := by
  change ((N.edges.map (Edge.rename e)).map Edge.key).Nodup
  have he : (N.edges.map (Edge.rename e)).map Edge.key =
      (N.edges.map Edge.key).map (Sym2.map e) := by
    simp only [List.map_map, Function.comp_def, Edge.key, Edge.rename, Sym2.map_pair_eq]
  rw [he]
  exact List.Nodup.map (Sym2.map.injective e.injective) h

theorem Net.rename_reduce_value [Fintype V] {W : Type} [Fintype W]
    (N : Net (M + 2) (fun v => p v + 1)) (e : V ≃ W) (hp : ∀ v, p v ≤ M) :
    ((N.rename e).reduce (fun w => hp (e.symm w))).value true = (N.reduce hp).value true := by
  classical
  unfold Net.value
  change N.scalar * (∑ A, weight ((N.rename e).reduce _).edges true A) = _
  congr 1
  symm
  apply Fintype.sum_equiv (stateRenameEquiv e)
  intro A
  have ha (v : V) : (A (e.symm (e v))).val = (A v).val :=
    congrArg (fun x => (A x).val) (e.symm_apply_apply v)
  simp [Net.reduce, Net.rename, Edge.reduce, Edge.rename, weight, Edge.eval,
    kernel, listOrdinary, reduceList, renameEntry, GainEntry.reduce, GainEntry.ordinary,
    Function.comp_def, stateRenameEquiv, Equiv.piCongrLeft', overlap, ha]

theorem Net.key_mem_iff (N : Net M p) (u v : V) :
    s(u,v) ∈ N.edges.map Edge.key ↔ N.graph.Adj u v := by
  simp only [List.mem_map, Edge.key, Sym2.eq_iff, Net.graph]

theorem Net.simple_addSingle_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (f : GainEntry M (p u) (p v)) :
    (N.addEdge u v huv [f]).Simple ↔ N.Simple ∧ ¬ N.graph.Adj u v := by
  simp only [Net.Simple, Net.addEdge, List.map_cons, Edge.key, List.nodup_cons]
  rw [← Net.key_mem_iff N u v]
  exact and_comm

theorem Net.rigid_addSingle_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (f : GainEntry M (p u) (p v)) (Γ : Subgroup (Equiv.Perm (Fin M))) :
    (N.addEdge u v huv [f]).Rigid Γ ↔ f.Nonconstant ∧ f.gain ∈ Γ ∧ N.Rigid Γ := by
  simp only [Net.Rigid, Net.addEdge, List.forall_mem_cons, Edge.Rigid,
    List.cons.injEq, and_true, exists_eq_left, exists_eq_left']
  exact and_assoc

/-- Select an existing edge in the requested orientation. The residual network
has no second edge on that pair; this follows from simplicity, not an input. -/
theorem Net.extract_rigid_edge (N : Net M p) (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hr : N.Rigid Γ) (hs : N.Simple) (u v : V) (huv : u ≠ v) (hadj : N.graph.Adj u v) :
    ∃ (R : Net M p) (f : GainEntry M (p u) (p v)),
      R.scalar = N.scalar ∧ EdgeListEquiv N.edges (R.addEdge u v huv [f]).edges ∧
      f.Nonconstant ∧ f.gain ∈ Γ ∧ R.Rigid Γ ∧ R.Simple ∧ ¬ R.graph.Adj u v ∧
      R.edges.length + 1 = N.edges.length := by
  classical
  obtain ⟨R,f,hc,he⟩ : ∃ (R : Net M p) (f : GainEntry M (p u) (p v)),
      R.scalar = N.scalar ∧ EdgeListEquiv N.edges (R.addEdge u v huv [f]).edges := by
    obtain ⟨⟨a,b,hab,L⟩,he,hor⟩ := hadj
    let e : Edge M p := ⟨a,b,hab,L⟩
    let R : Net M p := {N with edges := N.edges.erase e}
    have hperm : EdgeListEquiv N.edges (e :: R.edges) := .perm (List.perm_cons_erase he)
    obtain ⟨f,hf,_,_⟩ := hr e he
    dsimp [e] at hf hor
    have hf' : e = (⟨a,b,hab,[f]⟩ : Edge M p) := by
      exact congrArg (fun K => (⟨a,b,hab,K⟩ : Edge M p)) hf
    rw [hf'] at hperm
    rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨R,f,rfl,hperm⟩
    · exact ⟨R,f.reverse,rfl,hperm.trans (.reverse _ _)⟩
  have hr' : (R.addEdge u v huv [f]).Rigid Γ :=
    (he.forall_iff _ (fun e => e.rigid_reverse_iff Γ)).mp hr
  obtain ⟨hn,hΓ,hR⟩ := (R.rigid_addSingle_iff u v huv f Γ).mp hr'
  have hs' : (R.addEdge u v huv [f]).Simple := he.keys_perm.nodup_iff.mp hs
  obtain ⟨hS,hnot⟩ := (R.simple_addSingle_iff u v huv f).mp hs'
  refine ⟨R,f,hc,he,hn,hΓ,hR,hS,hnot,?_⟩
  exact he.length_eq.symm

end
end CoefficientwiseRigidity.Network
