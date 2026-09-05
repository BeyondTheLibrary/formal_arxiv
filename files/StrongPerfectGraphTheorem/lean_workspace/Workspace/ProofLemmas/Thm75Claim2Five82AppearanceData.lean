import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75Claim1
import Workspace.ProofLemmas.Thm75Claim2STAnticomplete

/-!
# Appearance data for 7.5 claim (2)

PAPER (printed p. 37): *"we obtain another appearance of J in G, say L(H')"*.

The distinguished branch is retained when the replaced branch is different. Otherwise it is
the new branch. Its odd length and its two endpoint cliques are the data used by claim (1).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- A new appearance with its distinguished odd branch. -/
structure BranchAppearance {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U) where
  m : ℕ
  H : SimpleGraph (Fin m)
  K : Set V
  φ : H.lineGraph ≃g G.induce K
  happ : IsAppearance G J H K
  B : List (Fin m)
  c₁ : Fin m
  c₂ : Fin m
  hbranch : IsBranch H B
  hfrom : IsTrackFrom H B c₁ c₂
  hodd : Odd (trackLength B)
  hlen : 3 ≤ trackLength B

namespace BranchAppearance

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}

/-- The clique of edges incident with the first distinguished branch end. -/
def leftClique (a : BranchAppearance G J) : Set V := NSet G a.H a.K a.φ a.c₁

/-- The clique of edges incident with the second distinguished branch end. -/
def rightClique (a : BranchAppearance G J) : Set V := NSet G a.H a.K a.φ a.c₂

/-- The vertices of the distinguished rung in the new appearance. -/
def rung (a : BranchAppearance G J) : Set V :=
  {x | ∃ (e : Sym2 (Fin a.m)) (he : e ∈ a.H.edgeSet),
    e ∈ trackEdges a.B ∧ x = (↑(a.φ ⟨e, he⟩) : V)}

/-- The two endpoint cliques have at least three vertices. -/
theorem three_le_cliques [Fintype U] [Finite V] (a : BranchAppearance G J)
    (hJ : IsKConnected J 3) : 3 ≤ a.leftClique.ncard ∧ 3 ≤ a.rightClique.ncard := by
  obtain ⟨_, hc₁, hc₂, _⟩ := Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
    J hJ a.H a.happ.1.1 a.B a.c₁ a.c₂ a.hbranch a.hfrom (by have := a.hlen; omega)
  exact ⟨Thm75DominanceTriangles.three_le_nset_ncard G a.H a.K a.φ a.c₁ hc₁,
    Thm75DominanceTriangles.three_le_nset_ncard G a.H a.K a.φ a.c₂ hc₂⟩

/-- The endpoint cliques of a distinguished branch of length at least three are disjoint.
A common rung vertex would represent the edge directly joining the two branch ends. -/
theorem cliques_disjoint [Fintype U] (a : BranchAppearance G J)
    (hJ : IsKConnected J 3) : Disjoint a.leftClique a.rightClique := by
  obtain ⟨hne, _, _, hnadj⟩ := Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
    J hJ a.H a.happ.1.1 a.B a.c₁ a.c₂ a.hbranch a.hfrom (by have := a.hlen; omega)
  apply Set.disjoint_left.mpr
  rintro x ⟨e, he, hec, hxe⟩ ⟨f, hf, hfc, hxf⟩
  have hef : (⟨e, he⟩ : a.H.edgeSet) = ⟨f, hf⟩ :=
    a.φ.injective (Subtype.ext (hxe.symm.trans hxf))
  have heq : e = f := congrArg Subtype.val hef
  have hce : a.c₁ ∈ f := heq ▸ hec.2
  have hfends : f = s(a.c₁, a.c₂) := (Sym2.mem_and_mem_iff hne).mp ⟨hce, hfc.2⟩
  apply hnadj
  have hedge : s(a.c₁, a.c₂) ∈ a.H.edgeSet := hfends ▸ hf
  exact hedge

/-- Claim (1) for a new appearance. -/
theorem cliques_diff_complete_subsingleton [Fintype V] [DecidableEq V] [Fintype U]
    (a : BranchAppearance G J) (hG : Berge G) (hJ : IsKConnected J 3)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G a.leftClique a.rightClique y) :
    (a.leftClique \ {x | VertexComplete G x Y}).Subsingleton ∧
      (a.rightClique \ {x | VertexComplete G x Y}).Subsingleton :=
  Workspace.ProofLemmas.Thm75Claim1.thm75Claim1 G hG J hJ a.H a.K a.φ a.happ
    a.B a.c₁ a.c₂ a.hbranch a.hfrom a.hodd a.hlen Y hYne hYanti hYdom

/-- The two new sides are anticomplete by claim (1). -/
theorem sides_anticomplete [Fintype V] [DecidableEq V]
    (a : BranchAppearance G J) (X : Set V)
    (hsmall : (a.leftClique \ X).Subsingleton ∧ (a.rightClique \ X).Subsingleton) :
    Anticomplete G (a.rung \ (X ∩ (a.leftClique ∪ a.rightClique)))
      ((a.K \ a.rung) \ (X ∩ (a.leftClique ∪ a.rightClique))) :=
  Workspace.ProofLemmas.Thm75Claim2STAnticomplete.thm75Claim2STAnticomplete
    G a.H a.K a.φ a.B a.c₁ a.c₂ a.hbranch a.hfrom X
    (X ∩ (a.leftClique ∪ a.rightClique)) a.rung
    (a.rung \ (X ∩ (a.leftClique ∪ a.rightClique)))
    ((a.K \ a.rung) \ (X ∩ (a.leftClique ∪ a.rightClique))) rfl rfl rfl rfl hsmall

end BranchAppearance

/-- PAPER (printed pp. 37--38): *"So case 2 applies ... N'ci = (Nci \\ {ri}) ∪ {r'i}"*.
One end of the replacement path has no neighbour in the old `T`, as in
*"From the minimality of F, r'₁ has no neighbour in T"*. The disjunction records the symmetry
used by the paper when orienting this path. -/
structure SameBranchReplacementData {V U : Type*} (G : SimpleGraph V)
    (N₁ N₂ K Rset T F : Set V) {J : SimpleGraph U} (a : BranchAppearance G J) where
  r₁ : V
  r₂ : V
  p₁ : V
  p₂ : V
  P : List V
  hP : IsPathFrom G P p₁ p₂
  hPF : ∀ x ∈ P, x ∈ F
  hr₁ : N₁ ∩ Rset = {r₁}
  hr₂ : N₂ ∩ Rset = {r₂}
  h₁ : ∀ x ∈ N₁ \ {r₁}, G.Adj p₁ x
  h₂ : ∀ x ∈ N₂ \ {r₂}, G.Adj p₂ x
  hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
    (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N₂ \ {r₂}) ∨
      (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)
  hno_T : (∀ x ∈ T, ¬ G.Adj p₁ x) ∨ (∀ x ∈ T, ¬ G.Adj p₂ x)
  hleft : a.leftClique = (N₁ \ {r₁}) ∪ {p₁}
  hright : a.rightClique = (N₂ \ {r₂}) ∪ {p₂}
  hrung : a.rung = {x | x ∈ P}

end Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
