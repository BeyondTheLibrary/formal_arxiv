import Workspace.ProofLemmas.Thm192Claim2Transfer

/-!
# The classes `F₁, …, F₇` are inherited by induced subgraphs

Every one of the eleven classes of §1 is defined by a Bergeness condition together
with conditions of the form *"no induced subgraph of `G` (or of `Ḡ`) is …"*.  Such
conditions are inherited by induced subgraphs, because an induced subgraph of an
induced subgraph is an induced subgraph.  The paper uses this silently; §19 needs
it because the induction of 19.2 is over *all* counterexamples, so it is applied
inside induced subgraphs of the graph at hand (see
`Thm192Claim2Localization.inductive_wheel_with_rim_in_A`).

The transports of the individual shapes live in `Thm192Claim2Transfer`; here they
are only assembled, using twice over that the complement of `G|S` is `Ḡ|S`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim2Heredity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Claim2Transfer

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- The complement of an induced subgraph is the induced subgraph of the complement. -/
theorem compl_induce (G : SimpleGraph V) (S : Set V) : (G.induce S)ᶜ = Gᶜ.induce S := by
  ext a b
  simp [SimpleGraph.induce, Subtype.ext_iff]

private theorem hf : Function.Injective (Subtype.val : ↥S → V) := Subtype.val_injective

private theorem hadj (G : SimpleGraph V) (S : Set V) :
    ∀ a b : ↥S, (G.induce S).Adj a b ↔ G.Adj a.1 b.1 := fun _ _ => Iff.rfl

/-! ### The individual conditions -/

theorem berge_induce (h : Berge G) : Berge (G.induce S) := by
  constructor
  · intro c hc
    have := h.1 _ ((isHoleList_map hf (hadj G S) c).mp hc)
    simpa [holeLength] using this
  · intro c hc
    rw [compl_induce] at hc
    have := h.2 _ ((isHoleList_map hf (hadj Gᶜ S) c).mp hc)
    simpa [holeLength] using this

/-- An induced subgraph of `G|S` is an induced subgraph of `G`. -/
theorem exists_induce_iso {α : Type*} {H : SimpleGraph α}
    (h : ∃ K : Set ↥S, Nonempty ((G.induce S).induce K ≃g H)) :
    ∃ K : Set V, Nonempty (G.induce K ≃g H) := by
  obtain ⟨K, ⟨e⟩⟩ := h
  exact ⟨(Subtype.val : ↥S → V) '' K,
    ⟨((imgIso hf (hadj G S) K).symm).trans e⟩⟩

theorem inF1_induce (h : InF1 G) : InF1 (G.induce S) := by
  refine ⟨berge_induce h.1, ?_⟩
  intro n H hH hex
  exact h.2 n H hH (exists_induce_iso hex)

theorem inF2_induce (h : InF2 G) : InF2 (G.induce S) := by
  refine ⟨inF1_induce h.1, ?_, ?_⟩
  · have := @inF1_induce V Gᶜ S h.2.1
    rwa [← compl_induce] at this
  · rintro hex
    exact h.2.2 (exists_induce_iso hex)

theorem inF3_induce (h : InF3 G) : InF3 (G.induce S) := by
  refine ⟨berge_induce h.1, ?_⟩
  intro n H hH
  refine ⟨fun hex => (h.2 n H hH).1 (exists_induce_iso hex), fun hex => (h.2 n H hH).2 ?_⟩
  obtain ⟨K, ⟨e⟩⟩ := hex
  rw [compl_induce] at e
  exact ⟨(Subtype.val : ↥S → V) '' K, ⟨((imgIso hf (hadj Gᶜ S) K).symm).trans e⟩⟩

theorem inF4_induce (h : InF4 G) : InF4 (G.induce S) := by
  refine ⟨inF3_induce h.1, ?_⟩
  rintro ⟨a, b, R₁, R₂, R₃, hp⟩
  exact h.2 ⟨_, _, _, _, _, isEvenPrism_map hf (hadj G S) hp⟩

theorem inF5_induce (h : InF5 G) : InF5 (G.induce S) := by
  refine ⟨inF3_induce h.1, ?_, ?_⟩
  · rintro ⟨a, b, P₁, P₂, P₃, hp⟩
    exact h.2.1 ⟨_, _, _, _, _, isLongPrism_map hf (hadj G S) hp⟩
  · rintro ⟨a, b, P₁, P₂, P₃, hp⟩
    rw [compl_induce] at hp
    exact h.2.2 ⟨_, _, _, _, _, isLongPrism_map hf (hadj Gᶜ S) hp⟩

theorem inF6_induce (h : InF6 G) : InF6 (G.induce S) := by
  refine ⟨inF5_induce h.1, ?_⟩
  rintro ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, hd⟩
  exact h.2 ⟨_, _, _, _, _, _, _, _, isDoubleDiamond_map hf (hadj G S) hd⟩

/-- **`F₇` is hereditary.**  This is what lets the induction of 19.2 be applied
inside an induced subgraph. -/
theorem inF7_induce (h : InF7 G) (S : Set V) : InF7 (G.induce S) := by
  refine ⟨inF6_induce h.1, ?_, ?_⟩
  · rintro ⟨C, Y, hw⟩
    exact h.2.1 ⟨_, _, isOddWheel_map hf (hadj G S) hw⟩
  · rintro ⟨C, Y, hw⟩
    rw [compl_induce] at hw
    exact h.2.2 ⟨_, _, isOddWheel_map hf (hadj Gᶜ S) hw⟩

end Workspace.ProofLemmas.Thm192Claim2Heredity
