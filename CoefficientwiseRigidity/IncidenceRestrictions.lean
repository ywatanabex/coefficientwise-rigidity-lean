import CoefficientwiseRigidity.NestPoints

/-!
Exact incidence-graph restriction for subfamilies of traces. Distinct trace rows
have distinct chosen original representatives, so this is an induced embedding,
including empty rows and isolated columns. Uses the original cycle definition.
-/
namespace CoefficientwiseRigidity
open Finset
open scoped Classical
noncomputable section
variable {V W : Type}

/-- Induced embeddings preserve the original prohibition on long induced cycles. -/
theorem chordalBipartite_comap {G : SimpleGraph V} (hG : ChordalBipartite G) (f : W ↪ V) :
    ChordalBipartite (G.comap f) := by
  obtain ⟨⟨b⟩,hc⟩ := hG
  refine ⟨⟨⟨fun v => b.side (f v),fun h => b.opposite h⟩⟩,?_⟩
  intro n hn hcycle
  obtain ⟨g,hg,he⟩ := hcycle
  exact hc n hn ⟨fun i => f (g i),f.injective.comp hg,he⟩

theorem chordalBipartite_induce {G : SimpleGraph V} (hG : ChordalBipartite G) (P : Set V) :
    ChordalBipartite (G.induce P) := chordalBipartite_comap hG ⟨Subtype.val,Subtype.val_injective⟩

namespace Structure
variable [DecidableEq V]

def incidenceGraph (U : Finset V) (H : Finset (Finset V)) : SimpleGraph (H ⊕ U) where
  Adj a b := match a,b with
    | .inl e,.inr x => x.val ∈ e.val
    | .inr x,.inl e => x.val ∈ e.val
    | _,_ => False
  symm := by intro a b; cases a <;> cases b <;> exact id
  loopless := by intro a; cases a <;> exact id

def incidenceBipartition (U : Finset V) (H : Finset (Finset V)) :
    Bipartition (incidenceGraph U H) where
  side := fun v => match v with | .inl _ => true | .inr _ => false
  opposite := by
    intro u v huv
    cases u <;> cases v <;> simp_all [incidenceGraph]

/-- Choose an actual original row for each distinct trace row. -/
def traceRowLift {H K : Finset (Finset V)} {U : Finset V} (hK : K ⊆ Trace H U) (e : K) : H :=
  ⟨Classical.choose (Finset.mem_image.mp (hK e.property)),
    (Classical.choose_spec (Finset.mem_image.mp (hK e.property))).1⟩

theorem traceRowLift_trace {H K : Finset (Finset V)} {U : Finset V}
    (hK : K ⊆ Trace H U) (e : K) : (traceRowLift hK e).val ∩ U = e.val :=
  (Classical.choose_spec (Finset.mem_image.mp (hK e.property))).2

theorem traceRowLift_injective {H K : Finset (Finset V)} {U : Finset V}
    (hK : K ⊆ Trace H U) : Function.Injective (traceRowLift hK) := by
  intro e f hef
  apply Subtype.ext
  rw [← traceRowLift_trace hK e,← traceRowLift_trace hK f,hef]

def incidenceTraceEmbedding {U W : Finset V} {H K : Finset (Finset V)}
    (hW : W ⊆ U) (hK : K ⊆ Trace H W) : (K ⊕ W) ↪ (H ⊕ U) where
  toFun := Sum.map (traceRowLift hK) (fun x => ⟨x.val,hW x.property⟩)
  inj' := by
    intro a b hab
    cases a with
    | inl e =>
      cases b with
      | inl f => exact congrArg Sum.inl (traceRowLift_injective hK (Sum.inl.inj hab))
      | inr x => cases hab
    | inr x =>
      cases b with
      | inl f => cases hab
      | inr y =>
        have hxy : (⟨x.val,hW x.property⟩ : U) = ⟨y.val,hW y.property⟩ := Sum.inr.inj hab
        exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : U => z.val) hxy))

theorem incidenceTraceEmbedding_graph {U W : Finset V} {H K : Finset (Finset V)}
    (hW : W ⊆ U) (hK : K ⊆ Trace H W) :
    (incidenceGraph U H).comap (incidenceTraceEmbedding hW hK) = incidenceGraph W K := by
  ext a b
  have hmem (e : K) (x : W) : x.val ∈ (traceRowLift hK e).val ↔ x.val ∈ e.val := by
    rw [← traceRowLift_trace hK e]
    simp only [Finset.mem_inter,show x.val ∈ W from x.property,and_true]
  cases a <;> cases b <;> first | exact hmem _ _ | rfl

/-- Every row subfamily of every column trace remains chordal bipartite in the
original induced-cycle sense, without assuming an alpha leaf or nest order. -/
theorem incidence_chordal_subtrace {U W : Finset V} {H K : Finset (Finset V)}
    (hG : ChordalBipartite (incidenceGraph U H)) (hW : W ⊆ U) (hK : K ⊆ Trace H W) :
    ChordalBipartite (incidenceGraph W K) := by
  have h := chordalBipartite_comap hG (incidenceTraceEmbedding hW hK)
  rwa [incidenceTraceEmbedding_graph] at h

end Structure
end
end CoefficientwiseRigidity
