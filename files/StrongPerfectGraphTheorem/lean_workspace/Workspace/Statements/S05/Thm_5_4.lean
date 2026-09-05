/-  Proof attempt for statement 5.4 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.

    THE PAPER'S PROOF.  5.4 is stated in section 5 with "The proof of this will take
    several sections", and is proved in section 8:

        "We are now ready to prove 5.4, which we restate:
         8.6 Let G be Berge. ..."

    and the proof of 8.6 ends "This proves 5.4."  So the paper's proof of 5.4 is
    literally "8.6 is 5.4".  Accordingly this file cites `thm_8_6` and nothing else.

    The two Lean transcriptions are the same assertion, except that 8.6 quantifies the
    3-connected graph `J` over an arbitrary finite vertex type `U`, where 5.4 uses
    `Fin m`.  So 8.6 is the more general form and 5.4 is its instance at `U := Fin m`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Statements.S08.Thm_8_6

set_option autoImplicit false

namespace Workspace.Statements.S05

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **5.4** (printed p. 21)

PAPER: *"Let `G` be Berge.  Let `J` be a 3-connected graph, such that there is no
`J`-enlargement with a nondegenerate appearance in `G`.  Let `L(H₀)` be an appearance of `J`
in `G`, such that if `L(H₀)` is degenerate, then `H₀ = J = K₃,₃` and no `J`-enlargement
appears in `Ḡ`.  Then either `G = L(H₀)`, or `H₀ ≠ K₃,₃` and `G` admits a proper 2-join, or
`G` admits a balanced skew partition."*

Transcription notes.

* The side condition *"`H₀ ≠ K₃,₃` and"* on the second alternative is **new in the published
  version** (the arXiv v1 draft had only *"`G` admits a 2-join"*) and is mathematically
  essential — it is exactly what makes the published 5.2 have no 2-join outcome.  It is
  transcribed as a conjunct of that alternative.
* *"`G = L(H₀)`"* is `Nonempty (G ≃g L(H₀))`: under the equality convention of printed p. 20
  the appearance `L(H₀)` *is* the induced subgraph `G|K₀`, so `G = L(H₀)` says that this
  induced subgraph is all of `G`.
* *"`H₀ = J = K₃,₃`"* is the conjunction `H₀ ≅ K₃,₃` and `J ≅ K₃,₃`. -/
theorem thm_5_4 (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (hnoenl : ¬ ∃ (m' : ℕ) (J' : SimpleGraph (Fin m')),
      IsJEnlargement J J' ∧
      ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (n : ℕ) (H₀ : SimpleGraph (Fin n)) (K₀ : Set V)
    (happ : IsAppearance G J H₀ K₀)
    (hdeg : DegenerateAppearance J H₀ →
      Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ ∃ (m' : ℕ) (J' : SimpleGraph (Fin m')), IsJEnlargement J J' ∧ Appears Gᶜ J') :
    Nonempty (G ≃g H₀.lineGraph) ∨
    (¬ Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧ AdmitsProper2Join G) ∨
    AdmitsBalancedSkewPartition G := by
  -- The paper restates 5.4 as 8.6 and proves it there ("This proves 5.4.").  8.6 is
  -- transcribed with `J` over an arbitrary finite vertex type; instantiate at `Fin m`.
  exact _root_.Workspace.Statements.S08.SPGT.thm_8_6 (U := Fin m) G hG J hJ hnoenl n H₀ K₀
    happ hdeg


end SPGT

end Workspace.Statements.S05
