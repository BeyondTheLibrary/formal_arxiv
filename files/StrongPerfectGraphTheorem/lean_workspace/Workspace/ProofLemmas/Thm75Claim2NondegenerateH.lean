import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# 7.5 claim (2): `L(H)` is nondegenerate

PAPER (proof of 7.5, claim (2), printed p. 36):

*"Suppose first that 5.8.1 holds.  Then we obtain an appearance `L(H′)` in `G` of some
`J`-enlargement, with `L(H)` an induced subgraph of `L(H′)`.  Since `Rc₁c₂` has even nonzero
length, it follows that `L(H)` is not degenerate, and therefore neither is `L(H′)`, and hence the
theorem holds."*

Only the middle clause is carved out here: *"Since `Rc₁c₂` has even nonzero length, it follows
that `L(H)` is not degenerate."*  `Rc₁c₂` has length `trackLength B - 1`, which is even and
nonzero because `trackLength B` is odd and `≥ 3`; a degenerate `K₄`-appearance has a four-cycle
through all four branch-vertices, so all four of its branches have length 1 and every rung has
length 0.

The conclusion is shaped as the hypothesis `hnd` of
`Thm75Claim2Transport.enlargementFromNonlocalAttachmentPathW`, which only needs nondegeneracy in
the case `J ≅ K₄` (`DegenerateAppearance` is vacuous for `J ≇ K₄, K₃,₃`, and the `K₃,₃` case is
handled inside that lemma).

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2NondegenerateH

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- **`L(H)` is nondegenerate, because `Rc₁c₂` has even nonzero length** (printed p. 36). -/
theorem thm75Claim2NondegenerateH {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H := by
  intro hJK₄ hdeg
  rcases hdeg with ⟨_, hdeg⟩ | ⟨hnK₄, -, -⟩
  · obtain ⟨a, b, c, d, -, hab, hbc, hcd, hda, hcycle⟩ := hdeg
    have hends := Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
      J hJ H happ.1.1 B c₁ c₂ hbranch hfrom (by omega)
    have hc₁ := hcycle hends.2.1
    have hc₂ := hcycle hends.2.2.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc₁ hc₂
    obtain ⟨col⟩ :=
      Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite
        happ.1.2
    have hac : col a = col c := by
      have hab' := col.valid hab
      have hbc' := col.valid hbc
      cases ha : col a <;> cases hb : col b <;> cases hc : col c <;> simp_all
    have hbd : col b = col d := by
      have hbc' := col.valid hbc
      have hcd' := col.valid hcd
      cases hb : col b <;> cases hc : col c <;> cases hd : col d <;> simp_all
    have hcol : col c₁ = col c₂ := by
      rcases hc₁ with h₁ | h₁ | h₁ | h₁ <;>
        rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;>
        subst c₁ <;> subst c₂
      all_goals first
        | exact hac
        | exact hac.symm
        | exact hbd
        | exact hbd.symm
        | exact False.elim (hends.1 rfl)
        | exact False.elim (hends.2.2.2 hab)
        | exact False.elim (hends.2.2.2 hab.symm)
        | exact False.elim (hends.2.2.2 hbc)
        | exact False.elim (hends.2.2.2 hbc.symm)
        | exact False.elim (hends.2.2.2 hcd)
        | exact False.elim (hends.2.2.2 hcd.symm)
        | exact False.elim (hends.2.2.2 hda)
        | exact False.elim (hends.2.2.2 hda.symm)
    have heven : Even (trackLength B) :=
      (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom).2 hcol
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff] at heven
    omega
  · exact hnK₄ hJK₄

end Workspace.ProofLemmas.Thm75Claim2NondegenerateH
