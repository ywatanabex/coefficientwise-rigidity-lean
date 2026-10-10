import CoefficientwiseRigidity.SeamNormalization
import CoefficientwiseRigidity.Composition

/-!
Finite copies glued along a specified induced boundary. The vertex type, cover,
and occupation vector are constructed explicitly. Their configurations are
exactly a boundary configuration together with one extension in each copy.
The boundary need not be a clique for this counting theorem.
-/
namespace CoefficientwiseRigidity.Replica
open scoped BigOperators Classical
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V]

abbrev Vertex (S : Finset V) (I : Type) := S ⊕ (I × {v : V // v ∉ S})

def base (S : Finset V) : Vertex S I → V
  | .inl v => v.val
  | .inr iv => iv.2.val

def embed (S : Finset V) (i : I) (v : V) : Vertex S I :=
  if h : v ∈ S then .inl ⟨v,h⟩ else .inr (i,⟨v,h⟩)

omit [Fintype V] in
@[simp] theorem base_embed (S : Finset V) (i : I) (v : V) :
    base S (embed S i v) = v := by
  unfold embed
  split_ifs <;> rfl

omit [Fintype V] in
@[simp] theorem embed_mem (S : Finset V) (i : I) (v : S) :
    embed S i v.val = .inl v := by simp [embed,v.property]

omit [Fintype V] in
@[simp] theorem embed_not_mem (S : Finset V) (i : I) (v : {v : V // v ∉ S}) :
    embed S i v.val = .inr (i,v) := by simp [embed,v.property]

def embedding (S : Finset V) (i : I) : V ↪ Vertex S I :=
  ⟨embed S i,fun _ _ h => by simpa using congrArg (base S) h⟩

def SameCopy (S : Finset V) : Vertex S I → Vertex S I → Prop
  | .inr x,.inr y => x.1 = y.1
  | _,_ => True

def graph (G : SimpleGraph V) (S : Finset V) (I : Type) : SimpleGraph (Vertex S I) where
  Adj x y := G.Adj (base S x) (base S y) ∧ SameCopy S x y
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    cases x <;> cases y <;> simp_all [SameCopy,eq_comm]
  loopless := by intro x h; exact G.loopless _ h.1

omit [Fintype V] in
@[simp] theorem embed_adj (G : SimpleGraph V) (S : Finset V) (i : I) (u v : V) :
    (graph G S I).Adj (embed S i u) (embed S i v) ↔ G.Adj u v := by
  simp only [graph,base_embed,and_iff_left_iff_imp]
  intro _
  unfold embed
  split_ifs <;> simp [SameCopy]

def hom (G : SimpleGraph V) (S : Finset V) (i : I) : G →g graph G S I :=
  ⟨embed S i,fun h => (embed_adj G S i _ _).mpr h⟩

def bipartition {G : SimpleGraph V} (b : Bipartition G) (S : Finset V) (I : Type) :
    Bipartition (graph G S I) :=
  ⟨fun x => b.side (base S x),fun h => b.opposite h.1⟩

variable {G : SimpleGraph V} {M : ℕ}

def cover (X : Cover G M) (S : Finset V) (I : Type) : Cover (graph G S I) M where
  transport x y := X.transport (base S x) (base S y)
  reverse h := X.reverse h.1

abbrev BoundaryConfiguration (X : Cover G M) (a : V → ℕ) (S : Finset V) :=
  Configuration (restrictCover X S G le_rfl) (fun v => a v.val)

def restriction (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (C : Configuration X a) : BoundaryConfiguration X a S :=
  ⟨fun v => C.val v.val, ⟨fun v => C.property.1 v.val,
    fun u v h => C.property.2 u.val v.val h⟩⟩

abbrev Fibre (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (b : BoundaryConfiguration X a S) :=
  {C : Configuration X a // restriction X a S C = b}

abbrev CopiedConfiguration (X : Cover G M) (a : V → ℕ) (S : Finset V) (I : Type) :=
  Configuration (cover X S I) (fun x => a (base S x))

def boundary (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (C : CopiedConfiguration X a S I) : BoundaryConfiguration X a S :=
  ⟨fun v => C.val (.inl v), ⟨fun v => C.property.1 (.inl v),
    fun u v h => C.property.2 (.inl u) (.inl v) ⟨h,trivial⟩⟩⟩

def part (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (C : CopiedConfiguration X a S I) (i : I) : Configuration X a := by
  refine ⟨fun v => C.val (embed S i v),⟨?_,?_⟩⟩
  · intro v
    simpa using C.property.1 (embed S i v)
  · intro u v h j hj hk
    have he := C.property.2 (embed S i u) (embed S i v)
      ((embed_adj G S i u v).mpr h) j hj
    apply he
    simpa [cover] using hk

omit [Fintype V] in
@[simp] theorem restriction_part (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (C : CopiedConfiguration X a S I) (i : I) :
    restriction X a S (part X a S C i) = boundary X a S C := by
  apply Subtype.ext
  funext v
  simp [restriction,part,boundary]

def assembleAssignment (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (b : BoundaryConfiguration X a S) (f : I → Fibre X a S b) : Assignment (Vertex S I) M
  | .inl v => b.val v
  | .inr iv => (f iv.1).val.val iv.2.val

omit [Fintype V] in
@[simp] theorem assemble_embed (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (b : BoundaryConfiguration X a S) (f : I → Fibre X a S b) (i : I) (v : V) :
    assembleAssignment X a S b f (embed S i v) = (f i).val.val v := by
  unfold embed
  split_ifs with hv
  · change b.val ⟨v,hv⟩ = (f i).val.val v
    exact (congrFun (congrArg Subtype.val (f i).property) ⟨v,hv⟩).symm
  · rfl

def assemble (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (b : BoundaryConfiguration X a S) (f : I → Fibre X a S b) :
    CopiedConfiguration X a S I := by
  refine ⟨assembleAssignment X a S b f,⟨?_,?_⟩⟩
  · intro x
    cases x with
    | inl v => exact b.property.1 v
    | inr iv => exact (f iv.1).val.property.1 iv.2.val
  · intro x y h j hj hk
    have hp (i : I) (u v : V) (huv : G.Adj u v)
        (hu : j ∈ assembleAssignment X a S b f (embed S i u))
        (hv : X.transport u v j ∈ assembleAssignment X a S b f (embed S i v)) : False := by
      rw [assemble_embed] at hu hv
      exact (f i).val.property.2 u v huv j hu hv
    cases x with
    | inl u =>
      cases y with
      | inl v => exact b.property.2 u v h.1 j hj hk
      | inr iv =>
        apply hp iv.1 u.val iv.2.val h.1
        · simpa using hj
        · simpa [cover,base] using hk
    | inr iu =>
      cases y with
      | inl v =>
        apply hp iu.1 iu.2.val v.val h.1
        · simpa using hj
        · simpa [cover,base] using hk
      | inr iv =>
        have he : iu.1 = iv.1 := h.2
        apply hp iu.1 iu.2.val iv.2.val h.1
        · simpa using hj
        · simpa [cover,base,he] using hk

def configurationEquiv (X : Cover G M) (a : V → ℕ) (S : Finset V) (I : Type) :
    CopiedConfiguration X a S I ≃
      Σ b : BoundaryConfiguration X a S, I → Fibre X a S b where
  toFun C := ⟨boundary X a S C, fun i => ⟨part X a S C i,restriction_part X a S C i⟩⟩
  invFun p := assemble X a S p.1 p.2
  left_inv C := by
    apply Subtype.ext
    funext x
    cases x with
    | inl v => rfl
    | inr iv => simp [assemble,assembleAssignment,part]
  right_inv p := by
    rcases p with ⟨b,f⟩
    have hb : boundary X a S (assemble X a S b f) = b := by
      apply Subtype.ext
      rfl
    apply Sigma.ext hb
    apply heq_of_eq
    funext i
    apply Subtype.ext
    apply Subtype.ext
    funext v
    exact assemble_embed X a S b f i v

theorem coefficient_eq_sum_powers [Fintype I] (X : Cover G M) (a : V → ℕ) (S : Finset V) :
    coefficient (cover X S I) (fun x => a (base S x)) =
      ∑ b : BoundaryConfiguration X a S, Fintype.card (Fibre X a S b) ^ Fintype.card I := by
  classical
  change Fintype.card (CopiedConfiguration X a S I) = _
  rw [Fintype.card_congr (configurationEquiv X a S I), Fintype.card_sigma]
  simp only [Fintype.card_fun]

end
end CoefficientwiseRigidity.Replica
