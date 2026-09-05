/-  **13.3, the skew partition and its kernel** (printed p. 83).

    PAPER: *"Now since `S` is step-connected, it follows that `A ∪ C` is connected; and
    therefore belongs to a component `A₁` of `G \ (X ∪ Y ∪ B)`.  Let `A₂` be the union of all
    the other components.  So by (1), `b₀ ∈ A₂`, and `(A₁ ∪ A₂, X ∪ Y ∪ B)` is a skew
    partition of `G` (since `Y ∪ B` is complete to `X`, and `X` is nonempty). … Every vertex
    in `Y ∪ B` has a neighbour in `A ∪ C`, so `A ∪ C` is a kernel for this skew partition, in
    `Ḡ`."*

    The overline on that last `Ḡ` is lost by `pdftotext` and is recovered here: a kernel is by
    definition a subset of the *second* side of the skew partition, and `A ∪ C` lies in the
    first side `A₁ ∪ A₂`.  Passing to `Ḡ` exchanges the two sides, so `(X ∪ Y ∪ B, A₁ ∪ A₂)`
    is a skew partition of `Ḡ` and `A ∪ C ⊆ A₁ ∪ A₂` is a legitimate candidate kernel there;
    it is anticonnected in `Ḡ` exactly because `A ∪ C` is connected in `G`, and the component
    of `X ∪ Y ∪ B` witnessing the kernel condition is one contained in `Y ∪ B`, every vertex
    of which has a `G`-neighbour in `A ∪ C`.  This is also what makes the subsequent appeal to
    4.6 come out with the printed pair of conditions (the `Ḡ`-path condition of 4.6 is the
    printed *even antipath*, and its `Ḡ`-antipath condition is the printed *even path*).

    Here `A₁ ∪ A₂` is `(X ∪ Y ∪ B)ᶜ`, so the two sides are `Ws` and `Wsᶜ`.  -/
import Mathlib
import Workspace.ProofLemmas.Thm133Setup
import Workspace.ProofLemmas.SkewPartitionFromSeparator
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ComponentsOfSetBasics

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm133SkewSetup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.ProofLemmas.Thm133Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **13.3, the skew partition.**  `(X ∪ Y ∪ B, (X ∪ Y ∪ B)ᶜ)` is a skew partition of `Ḡ`,
`A ∪ C` is a kernel for it, and some `Ḡ`-component of `X ∪ Y ∪ B` lies inside `Y ∪ B`.

The hypothesis `hclaim1` is claim (1) of the printed proof, which is what forces
`(X ∪ Y ∪ B)ᶜ` to be disconnected in `G` (equivalently, not anticonnected in `Ḡ`): `A ∪ C`
and `b₀` lie in different components of it. -/
theorem thm133_skew_setup {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {x : List V} (c : Ctx G A C B a₀ b₀ R₀ x)
    (hclaim1 : ∀ (u : V) (P : List V), u ∈ A ∪ C → IsPathFrom G P u b₀ →
      ∃ w ∈ SPGT.interior P, w ∈ Ws G A C B x) :
    ∃ A₁ : Set V,
      IsSkewPartition Gᶜ (Ws G A C B x) (Ws G A C B x)ᶜ ∧
      IsKernel Gᶜ (Ws G A C B x) (Ws G A C B x)ᶜ (A ∪ C) ∧
      IsComponent Gᶜ (Ws G A C B x) A₁ ∧
      A₁ ⊆ Ys G A C B x ∪ B := by
  classical
  obtain ⟨a, haA⟩ := c.Ane
  have ha₀Y : a₀ ∈ Ys G A C B x := c.a₀_mem_Y
  have ha₀W : a₀ ∈ Ws G A C B x := Or.inl (Or.inr ha₀Y)
  obtain ⟨x₁, hx₁⟩ := c.X_nonempty
  have hx₁W : x₁ ∈ Ws G A C B x := Or.inl (Or.inl hx₁)
  have hWsub : Ws G A C B x ⊆ Xs x ∪ (Ys G A C B x ∪ B) := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr hz)
  -- PAPER: *"since `Y ∪ B` is complete to `X`"*.
  have hcompl : ∀ s ∈ Xs x, ∀ t ∈ Ys G A C B x ∪ B, G.Adj s t :=
    fun s hs t ht => (c.YB_complete_X t ht s hs).symm
  -- `X ∪ Y ∪ B` is not anticonnected: `X` is nonempty, `a₀ ∈ Y`, and `X` is complete
  -- to `Y ∪ B`, so in `Ḡ` no walk inside it can cross from `X` to `Y ∪ B`.
  have hWnotanti : ¬ AnticonnectedSet G (Ws G A C B x) :=
    SkewPartitionFromSeparator.not_anticonnectedSet_of_meets hWsub hcompl
      hx₁W hx₁ ha₀W (Or.inl ha₀Y)
  have hACsubWc : A ∪ C ⊆ (Ws G A C B x)ᶜ := fun z hz => c.AC_disjoint_W z hz
  have hb₀Wc : b₀ ∈ (Ws G A C B x)ᶜ := c.b₀_not_mem_W
  -- PAPER: *"So by (1), `b₀ ∈ A₂`"* — `A ∪ C` and `b₀` lie in different components of
  -- `G \ (X ∪ Y ∪ B)`, for a path between them inside the complement would contradict (1).
  have hWcnotconn : ¬ ConnectedSet G (Ws G A C B x)ᶜ := by
    intro hconn
    obtain ⟨P, hP, hPmem⟩ :=
      InducedPathExtraction.exists_isPathFrom_of_connected hconn
        (hACsubWc (Or.inl haA)) hb₀Wc
    obtain ⟨w, hwint, hwW⟩ := hclaim1 a P (Or.inl haA) hP
    exact hPmem w (PathBasics.interior_subset hwint) hwW
  -- PAPER: *"`(A₁ ∪ A₂, X ∪ Y ∪ B)` is a skew partition of `G`"*, read in `Ḡ`.
  have hskew : IsSkewPartition Gᶜ (Ws G A C B x) (Ws G A C B x)ᶜ := by
    refine ⟨Set.union_compl_self _, disjoint_compl_right, hWnotanti, ?_⟩
    intro hc'
    apply hWcnotconn
    unfold AnticonnectedSet at hc'
    rwa [compl_compl] at hc'
  -- The `Ḡ`-component of `X ∪ Y ∪ B` containing `a₀`.
  obtain ⟨A₁, hA₁, ha₀A₁⟩ :=
    ComponentsOfSetBasics.exists_isComponent_mem Gᶜ (Ws G A C B x) ha₀W
  -- It avoids `X`: otherwise it would meet both sides of a complete pair, so it could
  -- not be connected in `Ḡ`.
  have hsub : A₁ ⊆ Ys G A C B x ∪ B := by
    intro z hz
    rcases hA₁.1 hz with (hzX | hzY) | hzB
    · exact absurd hA₁.2.1
        (SkewPartitionFromSeparator.not_anticonnectedSet_of_meets
          (D := A₁) (fun w hw => hWsub (hA₁.1 hw)) hcompl hz hzX ha₀A₁ (Or.inl ha₀Y))
    · exact Or.inl hzY
    · exact Or.inr hzB
  -- PAPER: *"Every vertex in `Y ∪ B` has a neighbour in `A ∪ C`, so `A ∪ C` is a kernel
  -- for this skew partition, in `Ḡ`."*
  have hkernel : IsKernel Gᶜ (Ws G A C B x) (Ws G A C B x)ᶜ (A ∪ C) := by
    refine ⟨hskew, ?_, hACsubWc, A₁, hA₁, ?_⟩
    · unfold AnticonnectedSet
      rw [compl_compl]
      exact c.AC_connected
    · intro v hv hvcomp
      have hz : ∃ z ∈ A ∪ C, G.Adj v z := by
        rcases hsub hv with hvY | hvB
        · exact ⟨a, Or.inl haA, hvY.2 a (Or.inl haA)⟩
        · exact bVertex_has_neighbour_in_AC c.maxStaircase v hvB
      obtain ⟨z, hzAC, hvz⟩ := hz
      exact ((SimpleGraph.compl_adj G v z).mp (hvcomp z hzAC)).2 hvz
  exact ⟨A₁, hskew, hkernel, hA₁, hsub⟩

end Workspace.ProofLemmas.Thm133SkewSetup
