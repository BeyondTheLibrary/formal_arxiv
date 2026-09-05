import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm75Setup

import Workspace.ProofLemmas.Thm75Claim2Five82SmallerSet
import Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
import Workspace.ProofLemmas.Thm75Claim2Five82Dominance
import Workspace.ProofLemmas.Thm75Claim2Five82DoubleSwap
import Workspace.ProofLemmas.Thm75Claim2Five82SecondClique
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.RungReplacementLabelled
import Workspace.ProofLemmas.RungReplacementRungLength
import Workspace.ProofLemmas.RungReplacementMinimalBridge
import Workspace.ProofLemmas.Thm75Claim2Five82CaseOne
import Workspace.ProofLemmas.Thm75Claim2Five82OtherBranch
import Workspace.ProofLemmas.Thm75Claim2Five82Reverse

/-!
# 7.5 claim (2): the unresolved exact-cardinality rung-replacement step

This file isolates the part of the 5.8.2 branch that is not covered by the induction hypothesis
at once.  The caller has already reduced to $$F.ncard = n+1$$, so every proper subset of `F`
is small enough for `ih`.

The gap is the two-paragraph rung-replacement argument on printed pp. 37--38, beginning with

> *"In case 1, let `R'` be the (unique) path from `p₁` to `s₂` in
> `(V(P) ∪ V(Rb₁b₂)) \ {s₁}`, and in the other cases let `R'` be `P`.  So if in `L(H)` we
> replace `Rb₁b₂` by `R'` we obtain another appearance of `J` in `G`, say `L(H')`."*

and ending with

> *"Hence we can apply induction on `F`, and the result follows.  This proves (2)."*

The available `EnlargementFromNonlocalAttachmentPath` theorem formalizes 5.8.1, not this
5.8.2 branch: it requires its two attachment vertices not to lie on a common branch, whereas
`b₁,b₂` below are the named ends of the common branch `q`.  The existing replacement statement
also does not accept all four cases: case 1 reuses vertices of `R ⊆ K`, and case 2 permits the
two edges `p₁r₁,p₂r₂`.  Those facts explain why the exact printed step is kept explicit here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82ExactCard

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- All data produced by the printed rung-replacement paragraphs that is needed for the next
use of the induction hypothesis.  The appearance and the distinguished branch may change, and
the new connected set already has cardinality at most `n`. -/
structure SmallerClaim2Instance {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (n : ℕ) (Y : Set V) where
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
  hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y
  hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
    (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y
  X : Set V
  X₀ : Set V
  X₁ : Set V
  Rset : Set V
  S : Set V
  T : Set V
  F : Set V
  hX : X = {x : V | VertexComplete G x Y}
  hRset : Rset = {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
    e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)}
  hX₀ : X₀ = X \ K
  hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)
  hS : S = Rset \ X₁
  hT : T = (K \ Rset) \ X₁
  hFcard : F.ncard ≤ n
  hFconn : ConnectedSet G F
  hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y
  hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f
  hTF : ∃ t ∈ T, ∃ f ∈ F, G.Adj t f

/-- The exact-cardinality input to the printed rung-replacement paragraphs.  Keeping this data
in one structure makes the remaining gap state only the mathematical output of those paragraphs,
instead of restating the final disjunction of claim (2). -/
structure ExactCardFive82Context {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) where
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
  hYne : Y.Nonempty
  hYanti : AnticonnectedSet G Y
  hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y
  hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
    (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y
  X : Set V
  X₀ : Set V
  X₁ : Set V
  Rset : Set V
  S : Set V
  T : Set V
  hX : X = {x : V | VertexComplete G x Y}
  hRset : Rset = {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
    e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)}
  hX₀ : X₀ = X \ K
  hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)
  hS : S = Rset \ X₁
  hT : T = (K \ Rset) \ X₁
  F : Set V
  hFcard : F.ncard = n + 1
  hFconn : ConnectedSet G F
  hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y
  hFK : ∀ x ∈ F, x ∉ K
  hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f
  hTF : ∃ t ∈ T, ∃ f ∈ F, G.Adj t f
  hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ConnectedSet G F' →
    (∀ x ∈ F', x ∉ X₀ ∪ X₁ ∪ Y) → (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) →
    (∃ t ∈ T, ∃ f ∈ F', G.Adj t f) → False
  P : List V
  p₁ : V
  p₂ : V
  hP : IsPathFrom G P p₁ p₂
  hPF : ∀ x ∈ P, x ∈ F
  b₁ : Fin m
  b₂ : Fin m
  q : List (Fin m)
  R : List V
  r₁ : V
  r₂ : V
  hb₁ : b₁ ∈ branchVertices H
  hb₂ : b₂ ∈ branchVertices H
  hq : IsBranch H q
  hqf : IsTrackFrom H q b₁ b₂
  hR : IsPathList G R
  hRs : {x : V | x ∈ R} =
    {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)}
  hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ R} = {r₁}
  hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ R} = {r₂}
  hcases :
    ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
      (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
      (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
        (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
        (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
    ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
      (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
      (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
        (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
        (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂}) ∨
        (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
      (Even (pathLength P) ↔ Even (pathLength R))) ∨
    (p₁ = p₂ ∧
      (∀ x ∈ (NSet G H K φ b₁ ∪ NSet G H K φ b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
      (∀ y ∈ K, G.Adj p₁ y →
        y ∈ NSet G H K φ b₁ ∪ NSet G H K φ b₂ ∪ {z : V | z ∈ R}) ∧
      Even (pathLength R)) ∨
    (r₁ = r₂ ∧ (∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
      (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
      (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
        (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
        (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂})) ∧
      Even (pathLength P))

open Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
open Workspace.ProofLemmas.Thm75Claim2Five82Dominance
open Workspace.ProofLemmas.Thm75Claim2Five82DoubleSwap
open Workspace.ProofLemmas.Thm75Claim2Five82SmallerSet

namespace ExactCardFive82Context

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
variable {G : SimpleGraph V} {hG : Berge G} {J : SimpleGraph U} {hJ : IsKConnected J 3}
variable {n : ℕ} {Y : Set V} (ctx : ExactCardFive82Context G hG J hJ n Y)

/-- The original appearance, in the same data format as the replacement. -/
def oldAppearance : BranchAppearance G J where
  m := ctx.m
  H := ctx.H
  K := ctx.K
  φ := ctx.φ
  happ := ctx.happ
  B := ctx.B
  c₁ := ctx.c₁
  c₂ := ctx.c₂
  hbranch := ctx.hbranch
  hfrom := ctx.hfrom
  hodd := ctx.hodd
  hlen := ctx.hlen

/-- PAPER: *"Consequently F ∩ X is empty."* -/
theorem not_mem_X {x : V} (hx : x ∈ ctx.F) : x ∉ ctx.X := by
  intro hxX
  apply ctx.hFdisj x hx
  left; left
  rw [ctx.hX₀]
  exact ⟨hxX, ctx.hFK x hx⟩

/-- No vertex of `F` is a common neighbour of `Y`. -/
theorem not_complete {x : V} (hx : x ∈ ctx.F) : ¬ VertexComplete G x Y := by
  intro hcomplete
  exact ctx.not_mem_X hx (ctx.hX ▸ hcomplete)

/-- The old endpoint cliques lie in `K`. -/
theorem clique_subset_K (c : Fin ctx.m) : NSet G ctx.H ctx.K ctx.φ c ⊆ ctx.K := by
  rintro x ⟨e, he, _, rfl⟩
  exact (ctx.φ ⟨e, he⟩).property

/-- A dominant vertex of `F` would enlarge the maximal anticonnected set `Y`.
This rules out case 3 when the replaced branch is the distinguished branch. -/
theorem not_dominant {x : V} (hx : x ∈ ctx.F) :
    ¬ IsDominantFor G (NSet G ctx.H ctx.K ctx.φ ctx.c₁)
      (NSet G ctx.H ctx.K ctx.φ ctx.c₂) x := by
  intro hdom
  have hxc := ctx.not_complete hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ Y, ¬ G.Adj x y := by
    by_contra hnone
    exact hxc (fun y hy => by
      by_contra hxy
      exact hnone ⟨y, hy, hxy⟩)
  have hne : x ≠ y := by
    intro heq
    exact ctx.hFdisj x hx (Or.inr (heq ▸ hy))
  have hanti := Thm75Claim2Transport.anticonnected_union_singleton G Y ctx.hYanti hy hxy hne
  have heq := ctx.hYmax (Y ∪ {x}) Set.subset_union_left hanti (by
    rintro z (hz | rfl)
    · exact ctx.hYdom z hz
    · exact hdom)
  exact ctx.hFdisj x hx (Or.inr (heq ▸ (show x ∈ Y ∪ {x} from Or.inr rfl)))

/-- PAPER: *"Case 4 is impossible since Bc₁c₂ has length ≥ 3."*
In that case the old rung ends would be a common vertex of its disjoint endpoint cliques. -/
theorem rung_ends_ne_of_same_branch
    (hb₁ : ctx.b₁ = ctx.c₁) (hb₂ : ctx.b₂ = ctx.c₂) : ctx.r₁ ≠ ctx.r₂ := by
  have hr₁ : ctx.r₁ ∈ NSet G ctx.H ctx.K ctx.φ ctx.c₁ := by
    have hmem : ctx.r₁ ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ ∩ {x | x ∈ ctx.R} :=
      ctx.hr₁.symm ▸ Set.mem_singleton ctx.r₁
    simpa only [hb₁] using hmem.1
  have hr₂ : ctx.r₂ ∈ NSet G ctx.H ctx.K ctx.φ ctx.c₂ := by
    have hmem : ctx.r₂ ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₂ ∩ {x | x ∈ ctx.R} :=
      ctx.hr₂.symm ▸ Set.mem_singleton ctx.r₂
    simpa only [hb₂] using hmem.1
  intro heq
  exact Set.disjoint_left.mp (ctx.oldAppearance.cliques_disjoint hJ) hr₁ (heq ▸ hr₂)

/-- PAPER: *"Case 3 is impossible, since then the vertex p₁ would be Bc₁c₂-dominant ...
and therefore would be in either X or Y, a contradiction."* -/
theorem not_case_three_of_same_branch
    (hb₁ : ctx.b₁ = ctx.c₁) (hb₂ : ctx.b₂ = ctx.c₂)
    (hadj : ∀ x ∈ (NSet G ctx.H ctx.K ctx.φ ctx.b₁ ∪
      NSet G ctx.H ctx.K ctx.φ ctx.b₂) \ {ctx.r₁, ctx.r₂}, G.Adj ctx.p₁ x) : False := by
  have hr₁ : ctx.r₁ ∈ NSet G ctx.H ctx.K ctx.φ ctx.c₁ := by
    have hmem := ctx.hr₁.symm ▸ Set.mem_singleton ctx.r₁
    exact hb₁ ▸ hmem.1
  have hr₂ : ctx.r₂ ∈ NSet G ctx.H ctx.K ctx.φ ctx.c₂ := by
    have hmem := ctx.hr₂.symm ▸ Set.mem_singleton ctx.r₂
    exact hb₂ ▸ hmem.1
  have hdisj := Set.disjoint_left.mp (ctx.oldAppearance.cliques_disjoint hJ)
  have hdom : IsDominantFor G (NSet G ctx.H ctx.K ctx.φ ctx.c₁)
      (NSet G ctx.H ctx.K ctx.φ ctx.c₂) ctx.p₁ := by
    apply dominant_of_complete_remainders G
      (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
      {ctx.p₁} ctx.r₁ ctx.r₂ ?_ ?_ ctx.p₁ rfl
    · intro x hx y hy
      have hy' : y = ctx.p₁ := hy
      rw [hy']
      apply SimpleGraph.Adj.symm
      apply hadj x
      refine ⟨Or.inl (hb₁.symm ▸ hx.1), ?_⟩
      rintro (hxr | hxr)
      · exact hx.2 hxr
      · exact hdisj hx.1 (hxr ▸ hr₂)
    · intro x hx y hy
      have hy' : y = ctx.p₁ := hy
      rw [hy']
      apply SimpleGraph.Adj.symm
      apply hadj x
      refine ⟨Or.inr (hb₂.symm ▸ hx.1), ?_⟩
      rintro (hxr | hxr)
      · exact hdisj (hxr ▸ hr₁) hx.1
      · exact hx.2 hxr
  exact ctx.not_dominant
    (ctx.hPF ctx.p₁ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem ctx.hP).1) hdom

end ExactCardFive82Context

/-- The geometric output of replacing a rung. The first location alternative retains the
distinguished rung. The second retains its complement in the old appearance. In both cases
the new appearance meets `F` on the replaced side.

The last field records either the pairs of prisms used by 7.4 or the two explicit endpoint
swaps of case 2. It does not assume dominance or a smaller connected set. -/
structure ReplacementGeometry {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {G : SimpleGraph V} {hG : Berge G} {J : SimpleGraph U} {hJ : IsKConnected J 3}
    {n : ℕ} {Y : Set V} (ctx : ExactCardFive82Context G hG J hJ n Y) where
  appearance : BranchAppearance G J
  hcliques : (appearance.leftClique ∪ appearance.rightClique) ∩ ctx.K ⊆
    NSet G ctx.H ctx.K ctx.φ ctx.c₁ ∪ NSet G ctx.H ctx.K ctx.φ ctx.c₂
  hlocation :
    (appearance.rung = ctx.Rset ∧ ctx.Rset ⊆ appearance.K ∧
      (ctx.F ∩ (appearance.K \ ctx.Rset)).Nonempty) ∨
    (ctx.K \ ctx.Rset ⊆ appearance.K ∧ appearance.rung ∩ ctx.K ⊆ ctx.Rset ∧
      (ctx.F ∩ appearance.rung).Nonempty)
  hcases : OneCliqueReplacement G
      (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
      appearance.leftClique appearance.rightClique ∨
    Nonempty (SameBranchReplacementData G
      (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
      ctx.K ctx.Rset ctx.T ctx.F appearance)

/-- **Remaining gap: case 1 of 5.8.2 when `bᵢ = cᵢ`**, PAPER (printed p. 37):
*"In case 1, let `R'` be the (unique) path from `p₁` to `s₂` in `(V(P) ∪ V(Rb₁b₂)) \ {s₁}` …
So if in `L(H)` we replace `Rb₁b₂` by `R'` we obtain another appearance of `J` in `G`, say
`L(H')`"*, and (printed p. 37) *"case 1 is impossible, by applying 7.4 as before to show that
`Y` remains a maximal anticonnected set of `B'`-dominant vertices, and applying the inductive
hypothesis."*

Here the replacement path reuses the terminal segment of the old rung running from `s₂ = r₂`,
so only the clique at `c₁` changes: the outcome is the `OneCliqueReplacement` alternative that
keeps `Nc₂` and exchanges `r₁` for `p₁` in `Nc₁`, with the paired prisms of 7.4 as witnesses.
What is missing is the construction of `H'` together with its endpoint-clique dictionary and
those prisms. -/
theorem gap_same_branch_case_one {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (hb₁ : ctx.b₁ = ctx.c₁) (hb₂ : ctx.b₂ = ctx.c₂)
    (hcase : (∀ x ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ \ {ctx.r₁}, G.Adj ctx.p₁ x) ∧
      (∃ x ∈ {y : V | y ∈ ctx.R} \ {ctx.r₁}, G.Adj ctx.p₂ x) ∧
      (∀ x ∈ ctx.P, ∀ y ∈ ctx.K, y ≠ ctx.r₁ → G.Adj x y →
        (x = ctx.p₁ ∧ y ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ \ {ctx.r₁}) ∨
        (x = ctx.p₂ ∧ y ∈ {z : V | z ∈ ctx.R} \ {ctx.r₁}))) :
    Nonempty (ReplacementGeometry ctx) := by
  classical
  -- PAPER: *"Bb₁b₂ is the branch Bc₁c₂"* — a subdivision has only one branch between two given
  -- branch-vertices, so the replaced branch is the distinguished one and the two rungs agree.
  have hr₁mem : ctx.r₁ ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ ∩ {x : V | x ∈ ctx.R} := by
    rw [ctx.hr₁]; rfl
  have hqlen2 : 2 ≤ ctx.q.length := by
    have hmem : ctx.r₁ ∈ {x : V | ∃ (e : Sym2 (Fin ctx.m)) (he : e ∈ ctx.H.edgeSet),
        e ∈ trackEdges ctx.q ∧ x = (↑(ctx.φ ⟨e, he⟩) : V)} := ctx.hRs ▸ hr₁mem.2
    obtain ⟨e, -, ⟨i, hi, -⟩, -⟩ := hmem
    omega
  obtain ⟨ιJ, TJ, hιJ, htrackJ, hlenJ, hrevJ, hdisjintJ, hnewJ, hcoverJ, hedgesJ⟩ :=
    ctx.happ.1.1
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hBlen2 : 2 ≤ ctx.B.length := by
    have := ctx.hlen; simp only [trackLength] at this; omega
  have hqB : trackEdges ctx.q = trackEdges ctx.B :=
    Workspace.ProofLemmas.BranchClassification.trackEdges_eq_of_same_ends
      hιJ htrackJ hlenJ hrevJ hdisjintJ hnewJ hcoverJ hedgesJ hdeg
      ctx.hq hqlen2 ctx.hqf ctx.hbranch hBlen2 ctx.hfrom ctx.hb₁ ctx.hb₂
      (Or.inl ⟨hb₁.symm, hb₂.symm⟩)
  have hRsB : {x : V | x ∈ ctx.R} = {x : V | ∃ (e : Sym2 (Fin ctx.m)) (he : e ∈ ctx.H.edgeSet),
      e ∈ trackEdges ctx.B ∧ x = (↑(ctx.φ ⟨e, he⟩) : V)} := by
    rw [ctx.hRs, hqB]
  have hRsetEq : ctx.Rset = {x : V | x ∈ ctx.R} := by rw [ctx.hRset, ctx.hRs, hqB]
  have hPK : ∀ x ∈ ctx.P, x ∉ ctx.K := fun x hx => ctx.hFK x (ctx.hPF x hx)
  obtain ⟨a, hleft, hright, hswap, hKsub, hrungK, hp₁rung⟩ :=
    Workspace.ProofLemmas.Thm75Claim2Five82CaseOne.case_one_outcome
      G hG J hJ ctx.m ctx.H ctx.K ctx.φ ctx.happ ctx.B ctx.c₁ ctx.c₂ ctx.hbranch ctx.hfrom
      ctx.hodd ctx.hlen ctx.R hRsB ctx.r₁ ctx.r₂ (by rw [← hb₁]; exact ctx.hr₁)
      (by rw [← hb₂]; exact ctx.hr₂) ctx.P ctx.p₁ ctx.p₂ ctx.hP hPK
      ⟨by rw [← hb₁]; exact hcase.1, hcase.2.1, by rw [← hb₁]; exact hcase.2.2⟩
  have hp₁F : ctx.p₁ ∈ ctx.F :=
    ctx.hPF ctx.p₁ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem ctx.hP).1
  have hp₁K : ctx.p₁ ∉ ctx.K := ctx.hFK ctx.p₁ hp₁F
  refine ⟨{
    appearance := a
    hcliques := ?_
    hlocation := Or.inr ⟨by rw [hRsetEq]; exact hKsub, by rw [hRsetEq]; exact hrungK,
      ⟨ctx.p₁, hp₁F, hp₁rung⟩⟩
    hcases := Or.inl (Or.inr (Or.inl ⟨hright, hswap⟩)) }⟩
  rintro x ⟨hx, hxK⟩
  rcases hx with hx | hx
  · rw [hleft] at hx
    rcases hx with hx | hx
    · exact Or.inl hx.1
    · exact absurd hxK ((show x = ctx.p₁ from hx) ▸ hp₁K)
  · exact Or.inr (hright ▸ hx)

/-- **Remaining gap: case 2 of 5.8.2 when `bᵢ = cᵢ`**, PAPER (printed pp. 37--38):
*"in the other cases let `R'` be `P`.  So if in `L(H)` we replace `Rb₁b₂` by `R'` we obtain
another appearance of `J` in `G`, say `L(H')` … `N'cᵢ = (Ncᵢ \ {rᵢ}) ∪ {r'ᵢ}` for `i = 1, 2`"*,
together with *"From the minimality of `F`, `r'₁` has no neighbour in `T`"*.

The output is the same-branch witness `SameBranchReplacementData`: the new appearance replaces
both endpoint cliques by exchanging the two old rung ends for the two ends of `P`, and its
distinguished rung is `P` itself.  `P` is even by the case hypothesis (`Rc₁c₂` is even because
`Bc₁c₂` is odd), so the new distinguished branch is again odd, and it has length at least three
because `p₁ ≠ p₂`.  What is missing is the construction of `H'` and its clique dictionary, and
the minimality argument for the attachment-free end. -/
theorem gap_same_branch_case_two {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (hb₁ : ctx.b₁ = ctx.c₁) (hb₂ : ctx.b₂ = ctx.c₂)
    (hcase : (∀ x ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ \ {ctx.r₁}, G.Adj ctx.p₁ x) ∧
      (∀ x ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₂ \ {ctx.r₂}, G.Adj ctx.p₂ x) ∧
      (∀ x ∈ ctx.P, ∀ y ∈ ctx.K, G.Adj x y →
        (x = ctx.p₁ ∧ y ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ \ {ctx.r₁}) ∨
        (x = ctx.p₂ ∧ y ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₂ \ {ctx.r₂}) ∨
        (x = ctx.p₁ ∧ y = ctx.r₁) ∨ (x = ctx.p₂ ∧ y = ctx.r₂)) ∧
      (Even (pathLength ctx.P) ↔ Even (pathLength ctx.R))) :
    ∃ a : BranchAppearance G J, ctx.K \ ctx.Rset ⊆ a.K ∧
      Nonempty (SameBranchReplacementData G
        (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
        ctx.K ctx.Rset ctx.T ctx.F a) := by
  classical
  -- The two endpoint cliques are named by `b₁, b₂` in the case hypothesis and by `c₁, c₂` in
  -- the conclusion; in this branch of the argument they are the same two vertices.
  have hN₁ : NSet G ctx.H ctx.K ctx.φ ctx.c₁ = NSet G ctx.H ctx.K ctx.φ ctx.b₁ := by rw [hb₁]
  have hN₂ : NSet G ctx.H ctx.K ctx.φ ctx.c₂ = NSet G ctx.H ctx.K ctx.φ ctx.b₂ := by rw [hb₂]
  -- The old rung is nonempty, so the replaced branch has at least one edge.
  have hr₁mem : ctx.r₁ ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ ∩ {x : V | x ∈ ctx.R} := by
    rw [ctx.hr₁]; rfl
  have hr₁R : ctx.r₁ ∈ ctx.R := hr₁mem.2
  have hr₂mem : ctx.r₂ ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₂ ∩ {x : V | x ∈ ctx.R} := by
    rw [ctx.hr₂]; rfl
  have hr₂R : ctx.r₂ ∈ ctx.R := hr₂mem.2
  have hqlen2 : 2 ≤ ctx.q.length := by
    have hmem : ctx.r₁ ∈ {x : V | ∃ (e : Sym2 (Fin ctx.m)) (he : e ∈ ctx.H.edgeSet),
        e ∈ trackEdges ctx.q ∧ x = (↑(ctx.φ ⟨e, he⟩) : V)} := ctx.hRs ▸ hr₁R
    obtain ⟨e, -, ⟨i, hi, -⟩, -⟩ := hmem
    omega
  -- PAPER: *"Bb₁b₂ is the branch Bc₁c₂"* — a subdivision has only one branch between two given
  -- branch-vertices, so the replaced branch is the distinguished one and the two rungs agree.
  obtain ⟨ιJ, TJ, hιJ, htrackJ, hlenJ, hrevJ, hdisjintJ, hnewJ, hcoverJ, hedgesJ⟩ :=
    ctx.happ.1.1
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hBlen2 : 2 ≤ ctx.B.length := by
    have := ctx.hlen; simp only [trackLength] at this; omega
  have hqB : trackEdges ctx.q = trackEdges ctx.B :=
    Workspace.ProofLemmas.BranchClassification.trackEdges_eq_of_same_ends
      hιJ htrackJ hlenJ hrevJ hdisjintJ hnewJ hcoverJ hedgesJ hdeg
      ctx.hq hqlen2 ctx.hqf ctx.hbranch hBlen2 ctx.hfrom ctx.hb₁ ctx.hb₂
      (Or.inl ⟨hb₁.symm, hb₂.symm⟩)
  have hRsetEq : ctx.Rset = {x : V | x ∈ ctx.R} := by
    rw [ctx.hRset, ctx.hRs, hqB]
  -- PAPER: *"Bc₁c₂ is odd"*, so its rung is an even path.
  have hReven : Even (pathLength ctx.R) :=
    Workspace.ProofLemmas.RungReplacementRungLength.even_pathLength_of_odd_trackLength
      ctx.φ ctx.B ctx.hbranch.1 ctx.hodd ctx.R ctx.hR (hRsetEq.symm.trans ctx.hRset)
  have hPeven : Even (pathLength ctx.P) := hcase.2.2.2.mpr hReven
  have hp₁F : ctx.p₁ ∈ ctx.F :=
    ctx.hPF ctx.p₁ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem ctx.hP).1
  have hp₂F : ctx.p₂ ∈ ctx.F :=
    ctx.hPF ctx.p₂ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem ctx.hP).2
  -- PAPER: *"p₁ would be Bc₁c₂-dominant"* — if the two ends of `P` coincided, that vertex
  -- would miss at most `r₁` in `Nc₁` and at most `r₂` in `Nc₂`, contradicting maximality of `Y`.
  have hp₁p₂ : ctx.p₁ ≠ ctx.p₂ := by
    intro heq
    refine ctx.not_dominant hp₁F ⟨?_, ?_⟩
    · rintro x ⟨hx, hxn⟩ y ⟨hy, hyn⟩
      have hxr : x = ctx.r₁ := by
        by_contra hxr
        exact hxn (hcase.1 x ⟨hN₁ ▸ hx, hxr⟩)
      have hyr : y = ctx.r₁ := by
        by_contra hyr
        exact hyn (hcase.1 y ⟨hN₁ ▸ hy, hyr⟩)
      rw [hxr, hyr]
    · rintro x ⟨hx, hxn⟩ y ⟨hy, hyn⟩
      have hxr : x = ctx.r₂ := by
        by_contra hxr
        exact hxn (heq ▸ hcase.2.1 x ⟨hN₂ ▸ hx, hxr⟩)
      have hyr : y = ctx.r₂ := by
        by_contra hyr
        exact hyn (heq ▸ hcase.2.1 y ⟨hN₂ ▸ hy, hyr⟩)
      rw [hxr, hyr]
  -- `P` is even and has distinct ends, so it has at least two edges.
  have hPlen : 2 ≤ pathLength ctx.P := by
    have h2 := Workspace.ProofLemmas.RungReplacementRungLength.two_le_length_of_ends_ne
      ctx.hP hp₁p₂
    have hpos : 1 ≤ pathLength ctx.P := by simp only [pathLength]; omega
    rcases hPeven with ⟨k, hk⟩
    omega
  -- The replacement input of §5.1: `R' = P`, disjoint from the retained appearance, attaching
  -- to it exactly at the two clique remainders, and of the same parity as the old rung.
  have hdisj : ∀ x ∈ ctx.P, x ∈ ctx.K → x ∈ ctx.R := fun x hx hxK =>
    absurd hxK (ctx.hFK x (ctx.hPF x hx))
  have hboundary : ∀ x ∈ ctx.P, ∀ y ∈ ctx.K, y ∉ ctx.R →
      (G.Adj x y ↔
        (x = ctx.p₁ ∧ y ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₁ \ {ctx.r₁}) ∨
        (x = ctx.p₂ ∧ y ∈ NSet G ctx.H ctx.K ctx.φ ctx.b₂ \ {ctx.r₂})) := by
    intro x hx y hy hyR
    constructor
    · intro hadj
      rcases hcase.2.2.1 x hx y hy hadj with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h.2 ▸ hr₁R) hyR
      · exact absurd (h.2 ▸ hr₂R) hyR
    · rintro (⟨rfl, hy'⟩ | ⟨rfl, hy'⟩)
      · exact hcase.1 y hy'
      · exact hcase.2.1 y hy'
  obtain ⟨res⟩ := Workspace.ProofLemmas.RungReplacementLabelled.rungReplacement
    G J hJ ctx.H ctx.K ctx.φ ctx.happ ctx.q ctx.b₁ ctx.b₂ ctx.hb₁ ctx.hb₂ ctx.hq ctx.hqf
    ctx.R ctx.hR ctx.hRs ctx.r₁ ctx.r₂ ctx.hr₁ ctx.hr₂
    ctx.P ctx.p₁ ctx.p₂ ctx.hP hdisj hboundary hcase.2.2.2
  -- PAPER: *"From the minimality of F, r'₁ has no neighbour in T."*
  have hsub :=
    Workspace.ProofLemmas.RungReplacementMinimalBridge.t_attachment_vertices_subsingleton_of_minimal_bridge
      (G := G) ctx.S ctx.T ctx.F (ctx.X₀ ∪ ctx.X₁ ∪ Y) ctx.hFconn ctx.hFdisj ctx.hSF ctx.hmin
  have hno_T : (∀ x ∈ ctx.T, ¬ G.Adj ctx.p₁ x) ∨ (∀ x ∈ ctx.T, ¬ G.Adj ctx.p₂ x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨t₁, ht₁, ha₁⟩, ⟨t₂, ht₂, ha₂⟩⟩ := hcon
    exact hp₁p₂ (hsub ⟨hp₁F, t₁, ht₁, ha₁.symm⟩ ⟨hp₂F, t₂, ht₂, ha₂.symm⟩)
  refine ⟨⟨res.m, res.H', res.K', res.φ', res.happ, res.q', res.ι ctx.b₁, res.ι ctx.b₂,
      res.hq', res.hq'from, ?_, ?_⟩, ?_, ⟨?_⟩⟩
  · rw [res.hq'len]; exact hPeven.add_one
  · rw [res.hq'len]; omega
  · rintro x ⟨hxK, hxR⟩
    rw [hRsetEq] at hxR
    show x ∈ res.K'
    rw [res.hK']
    exact Or.inl ⟨hxK, hxR⟩
  · exact {
      r₁ := ctx.r₁
      r₂ := ctx.r₂
      p₁ := ctx.p₁
      p₂ := ctx.p₂
      P := ctx.P
      hP := ctx.hP
      hPF := ctx.hPF
      hr₁ := by rw [hN₁, hRsetEq]; exact ctx.hr₁
      hr₂ := by rw [hN₂, hRsetEq]; exact ctx.hr₂
      h₁ := fun x hx => hcase.1 x ⟨hN₁ ▸ hx.1, hx.2⟩
      h₂ := fun x hx => hcase.2.1 x ⟨hN₂ ▸ hx.1, hx.2⟩
      hno := by
        intro x hx y hy hadj
        rcases hcase.2.2.1 x hx y hy hadj with h | h | h | h
        · exact Or.inl ⟨h.1, hN₁ ▸ h.2⟩
        · exact Or.inr (Or.inl ⟨h.1, hN₂ ▸ h.2⟩)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      hno_T := hno_T
      hleft := by
        show NSet G res.H' res.K' res.φ' (res.ι ctx.b₁) = _
        rw [res.hleft, hN₁]
      hright := by
        show NSet G res.H' res.K' res.φ' (res.ι ctx.b₂) = _
        rw [res.hright, hN₂]
      hrung := res.hrung' }

/-- The geometry of the same-branch case 2 follows from the replaced appearance: the two new
cliques meet `K` inside the two old ones because the ends of `R'` lie in `F`, the old
complement of the rung survives, and `F` meets the new rung because the new rung *is* `R'`. -/
theorem replacement_geometry_of_same_branch_case_two {V U : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (a : BranchAppearance G J) (hK : ctx.K \ ctx.Rset ⊆ a.K)
    (d : SameBranchReplacementData G
      (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
      ctx.K ctx.Rset ctx.T ctx.F a) :
    Nonempty (ReplacementGeometry ctx) := by
  have hp₁F : d.p₁ ∈ ctx.F :=
    d.hPF d.p₁ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem d.hP).1
  have hp₂F : d.p₂ ∈ ctx.F :=
    d.hPF d.p₂ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem d.hP).2
  have hrungF : ∀ x ∈ a.rung, x ∈ ctx.F := by
    intro x hx
    rw [d.hrung] at hx
    exact d.hPF x hx
  refine ⟨{
    appearance := a
    hcliques := ?_
    hlocation := ?_
    hcases := Or.inr ⟨d⟩ }⟩
  · rintro x ⟨hx, hxK⟩
    rcases hx with hx | hx
    · rw [d.hleft] at hx
      rcases hx with hx | hx
      · exact Or.inl hx.1
      · exact absurd hxK (ctx.hFK x (hx ▸ hp₁F))
    · rw [d.hright] at hx
      rcases hx with hx | hx
      · exact Or.inr hx.1
      · exact absurd hxK (ctx.hFK x (hx ▸ hp₂F))
  · refine Or.inr ⟨hK, ?_, ?_⟩
    · rintro x ⟨hx, hxK⟩
      exact absurd hxK (ctx.hFK x (hrungF x hx))
    · refine ⟨d.p₁, hp₁F, ?_⟩
      rw [d.hrung]
      exact (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem d.hP).1

/-- **Remaining gap: the replaced branch is not the distinguished one**, PAPER (printed p. 37):
*"Now suppose that `b₁b₂` and `c₁c₂` are different edges of `J`.  Then `Bc₁c₂` is still a branch
of `H'`, and we claim that every `y ∈ Y` is `Bc₁c₂`-dominant with respect to `L(H')` … Since
`Rb₁b₂ ≠ Rc₁c₂`, it follows that `Rb₁b₂` is incident with at most one of `c₁, c₂`, so these two
prisms are related as in 7.4."*

Here the distinguished branch and both of its endpoint cliques survive the replacement, so the
`OneCliqueReplacement` alternative is the trivial one, and the new appearance keeps the old
distinguished rung while `F` meets the new rung `R'`.  What is missing is the construction of
`H'`, i.e. the subdivision replacement and its clique dictionary. -/
theorem gap_other_branch_geometry {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (hdiff : s(ctx.b₁, ctx.b₂) ≠ s(ctx.c₁, ctx.c₂)) :
    ∃ a : BranchAppearance G J,
      (a.leftClique ∪ a.rightClique) ∩ ctx.K ⊆
        NSet G ctx.H ctx.K ctx.φ ctx.c₁ ∪ NSet G ctx.H ctx.K ctx.φ ctx.c₂ ∧
      OneCliqueReplacement G (NSet G ctx.H ctx.K ctx.φ ctx.c₁)
        (NSet G ctx.H ctx.K ctx.φ ctx.c₂) a.leftClique a.rightClique ∧
      a.rung = ctx.Rset ∧ ctx.Rset ⊆ a.K ∧
      (ctx.F ∩ (a.K \ ctx.Rset)).Nonempty := by
  classical
  have hPK : ∀ x ∈ ctx.P, x ∉ ctx.K := fun x hx => ctx.hFK x (ctx.hPF x hx)
  obtain ⟨a, hcl, hone, hrung, hsub, hp₁mem⟩ :=
    Workspace.ProofLemmas.Thm75Claim2Five82OtherBranch.other_branch_outcome
      G hG J hJ ctx.m ctx.H ctx.K ctx.φ ctx.happ ctx.B ctx.c₁ ctx.c₂ ctx.hbranch ctx.hfrom
      ctx.hodd ctx.hlen ctx.q ctx.b₁ ctx.b₂ ctx.hb₁ ctx.hb₂ ctx.hq ctx.hqf hdiff
      ctx.R ctx.hR ctx.hRs ctx.r₁ ctx.r₂ ctx.hr₁ ctx.hr₂ ctx.P ctx.p₁ ctx.p₂ ctx.hP hPK
      ctx.hcases
  have hp₁F : ctx.p₁ ∈ ctx.F :=
    ctx.hPF ctx.p₁ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem ctx.hP).1
  have hp₁K : ctx.p₁ ∉ ctx.K := ctx.hFK ctx.p₁ hp₁F
  have hRsetK : ctx.Rset ⊆ ctx.K := by
    rw [ctx.hRset]; rintro x ⟨e, he, -, rfl⟩; exact (ctx.φ ⟨e, he⟩).property
  refine ⟨a, hcl, hone, ?_, ?_, ⟨ctx.p₁, hp₁F, hp₁mem, fun hc => hp₁K (hRsetK hc)⟩⟩
  · rw [ctx.hRset]; exact hrung
  · rw [ctx.hRset]; exact hsub

/-- When the replaced branch is not the distinguished one, both endpoint cliques and the
distinguished rung are unchanged, so the replacement is the trivial one-clique replacement and
`F` meets the complement of the rung in the new appearance. -/
theorem replacement_geometry_of_other_branch {V U : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (a : BranchAppearance G J)
    (hleft : a.leftClique = NSet G ctx.H ctx.K ctx.φ ctx.c₁)
    (hright : a.rightClique = NSet G ctx.H ctx.K ctx.φ ctx.c₂)
    (hrung : a.rung = ctx.Rset) (hsub : ctx.Rset ⊆ a.K)
    (hmeet : (ctx.F ∩ (a.K \ ctx.Rset)).Nonempty) :
    Nonempty (ReplacementGeometry ctx) := by
  refine ⟨{
    appearance := a
    hcliques := ?_
    hlocation := Or.inl ⟨hrung, hsub, hmeet⟩
    hcases := Or.inl (Or.inl ⟨hleft, hright⟩) }⟩
  rintro x ⟨hx, -⟩
  rcases hx with hx | hx
  · exact Or.inl (hleft ▸ hx)
  · exact Or.inr (hright ▸ hx)

/-- The general consumer of the other-branch outcome: the distinguished rung survives, and the
two endpoint cliques are related to the old ones by a one-clique replacement. -/
theorem replacement_geometry_of_other_branch_general {V U : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (a : BranchAppearance G J)
    (hcliques : (a.leftClique ∪ a.rightClique) ∩ ctx.K ⊆
      NSet G ctx.H ctx.K ctx.φ ctx.c₁ ∪ NSet G ctx.H ctx.K ctx.φ ctx.c₂)
    (hone : OneCliqueReplacement G (NSet G ctx.H ctx.K ctx.φ ctx.c₁)
      (NSet G ctx.H ctx.K ctx.φ ctx.c₂) a.leftClique a.rightClique)
    (hrung : a.rung = ctx.Rset) (hsub : ctx.Rset ⊆ a.K)
    (hmeet : (ctx.F ∩ (a.K \ ctx.Rset)).Nonempty) :
    Nonempty (ReplacementGeometry ctx) :=
  ⟨{ appearance := a
     hcliques := hcliques
     hlocation := Or.inl ⟨hrung, hsub, hmeet⟩
     hcases := Or.inl hone }⟩

/-- The same context with the two distinguished branch ends exchanged.  PAPER (printed p. 38):
*"(This is without loss of generality, because in this case 2, there is symmetry between
`b₁ = c₁` and `b₂ = c₂`.)"* -/
def revContext {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {G : SimpleGraph V} {hG : Berge G} {J : SimpleGraph U} {hJ : IsKConnected J 3}
    {n : ℕ} {Y : Set V} (ctx : ExactCardFive82Context G hG J hJ n Y) :
    ExactCardFive82Context G hG J hJ n Y where
  m := ctx.m
  H := ctx.H
  K := ctx.K
  φ := ctx.φ
  happ := ctx.happ
  B := ctx.B.reverse
  c₁ := ctx.c₂
  c₂ := ctx.c₁
  hbranch := Workspace.ProofLemmas.Thm57Claim2Structure.isBranch_reverse ctx.hbranch
  hfrom := Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse ctx.hfrom
  hodd := by
    rw [show trackLength ctx.B.reverse = trackLength ctx.B by simp [trackLength]]
    exact ctx.hodd
  hlen := by
    rw [show trackLength ctx.B.reverse = trackLength ctx.B by simp [trackLength]]
    exact ctx.hlen
  hYne := ctx.hYne
  hYanti := ctx.hYanti
  hYdom := fun y hy => ⟨(ctx.hYdom y hy).2, (ctx.hYdom y hy).1⟩
  hYmax := fun Y' h1 h2 h3 =>
    ctx.hYmax Y' h1 h2 (fun y hy => ⟨(h3 y hy).2, (h3 y hy).1⟩)
  X := ctx.X
  X₀ := ctx.X₀
  X₁ := ctx.X₁
  Rset := ctx.Rset
  S := ctx.S
  T := ctx.T
  hX := ctx.hX
  hRset := by
    rw [ctx.hRset, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
  hX₀ := ctx.hX₀
  hX₁ := by rw [ctx.hX₁, Set.union_comm]
  hS := ctx.hS
  hT := ctx.hT
  F := ctx.F
  hFcard := ctx.hFcard
  hFconn := ctx.hFconn
  hFdisj := ctx.hFdisj
  hFK := ctx.hFK
  hSF := ctx.hSF
  hTF := ctx.hTF
  hmin := ctx.hmin
  P := ctx.P
  p₁ := ctx.p₁
  p₂ := ctx.p₂
  hP := ctx.hP
  hPF := ctx.hPF
  b₁ := ctx.b₁
  b₂ := ctx.b₂
  q := ctx.q
  R := ctx.R
  r₁ := ctx.r₁
  r₂ := ctx.r₂
  hb₁ := ctx.hb₁
  hb₂ := ctx.hb₂
  hq := ctx.hq
  hqf := ctx.hqf
  hR := ctx.hR
  hRs := ctx.hRs
  hr₁ := ctx.hr₁
  hr₂ := ctx.hr₂
  hcases := ctx.hcases

/-- Transporting the geometric output back across that exchange. -/
theorem replacementGeometry_of_rev {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {G : SimpleGraph V} {hG : Berge G} {J : SimpleGraph U} {hJ : IsKConnected J 3}
    {n : ℕ} {Y : Set V} (ctx : ExactCardFive82Context G hG J hJ n Y)
    (rep : ReplacementGeometry (revContext ctx)) : Nonempty (ReplacementGeometry ctx) := by
  classical
  set a := rep.appearance with ha
  have hcl := rep.hcliques
  have hloc := rep.hlocation
  have hcs := rep.hcases
  refine ⟨{
    appearance := Workspace.ProofLemmas.Thm75Claim2Five82Reverse.BranchAppearance.rev a
    hcliques := ?_
    hlocation := ?_
    hcases := ?_ }⟩
  · rw [Workspace.ProofLemmas.Thm75Claim2Five82Reverse.rev_leftClique,
      Workspace.ProofLemmas.Thm75Claim2Five82Reverse.rev_rightClique, Set.union_comm]
    intro x hx
    exact (Set.union_comm _ _) ▸ hcl hx
  · rw [Workspace.ProofLemmas.Thm75Claim2Five82Reverse.rev_rung]
    exact hloc
  · rcases hcs with h | h
    · exact Or.inl
        (Workspace.ProofLemmas.Thm75Claim2Five82Reverse.oneCliqueReplacement_swap h)
    · exact Or.inr
        (h.map Workspace.ProofLemmas.Thm75Claim2Five82Reverse.sameBranchReplacementDataRev)

/-- The four cases of 5.8.2 when the replaced branch is the distinguished one, with cases 3 and
4 excluded. -/
theorem geometry_of_same_branch {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (hb₁ : ctx.b₁ = ctx.c₁) (hb₂ : ctx.b₂ = ctx.c₂) :
    Nonempty (ReplacementGeometry ctx) := by
  rcases ctx.hcases with hcase | hcase | hcase | hcase
  · exact gap_same_branch_case_one G hG J hJ n Y ctx hb₁ hb₂ hcase
  · obtain ⟨a, hK, ⟨d⟩⟩ := gap_same_branch_case_two G hG J hJ n Y ctx hb₁ hb₂ hcase
    exact replacement_geometry_of_same_branch_case_two G hG J hJ n Y ctx a hK d
  · exact (ctx.not_case_three_of_same_branch hb₁ hb₂ hcase.2.1).elim
  · exact ((ctx.rung_ends_ne_of_same_branch hb₁ hb₂) hcase.1).elim

/-- The four cases of 5.8.2, with cases 3 and 4 excluded when the replaced branch is the
distinguished one. -/
theorem gap_replacement_geometry {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y) :
    Nonempty (ReplacementGeometry ctx) := by
  by_cases hsame : ctx.b₁ = ctx.c₁ ∧ ctx.b₂ = ctx.c₂
  · exact geometry_of_same_branch G hG J hJ n Y ctx hsame.1 hsame.2
  · by_cases hswap : ctx.b₁ = ctx.c₂ ∧ ctx.b₂ = ctx.c₁
    · -- The replaced branch is the distinguished branch with the two ends named the other way
      -- round; reverse the distinguished branch and its names, and transport the result back.
      obtain ⟨rep⟩ :=
        geometry_of_same_branch G hG J hJ n Y (revContext ctx) hswap.1 hswap.2
      exact replacementGeometry_of_rev ctx rep
    · -- PAPER: *"Now suppose that b₁b₂ and c₁c₂ are different edges of J."*
      have hdiff : s(ctx.b₁, ctx.b₂) ≠ s(ctx.c₁, ctx.c₂) := by
        intro hc
        rcases Sym2.eq_iff.mp hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hsame ⟨h1, h2⟩
        · exact hswap ⟨h1, h2⟩
      obtain ⟨a, hcl, hone, hrung, hsub, hmeet⟩ :=
        gap_other_branch_geometry G hG J hJ n Y ctx hdiff
      exact replacement_geometry_of_other_branch_general G hG J hJ n Y ctx a hcl hone
        hrung hsub hmeet

/-- **Remaining second-clique gap**, PAPER (printed p. 38):
*"We claim also that every vertex of Nc₂ \ {r₂} is in X."*
Its printed proof uses a prism with a prescribed non-complete end, then 2.8 and 2.2.
The disjunction in the hypothesis allows the symmetry explicitly used by the paper to
orient `R'`. The first complete clique is established separately from the absence of an
attachment in `T`. -/
theorem gap_second_clique_complete {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (a : BranchAppearance G J)
    (d : SameBranchReplacementData G
      (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
      ctx.K ctx.Rset ctx.T ctx.F a)
    (hcomplete : (NSet G ctx.H ctx.K ctx.φ ctx.c₁ \ {d.r₁} ⊆ ctx.X) ∨
      (NSet G ctx.H ctx.K ctx.φ ctx.c₂ \ {d.r₂} ⊆ ctx.X)) :
    (NSet G ctx.H ctx.K ctx.φ ctx.c₁ \ {d.r₁} ⊆ ctx.X) ∧
      (NSet G ctx.H ctx.K ctx.φ ctx.c₂ \ {d.r₂} ⊆ ctx.X) := by
  classical
  have hFXnot : ∀ x ∈ ctx.F, x ∉ ctx.X := fun x hx => ctx.not_mem_X hx
  -- PAPER: case 3 is impossible, so the two ends of `R'` are distinct.
  have hp₁₂ : d.p₁ ≠ d.p₂ := by
    intro heq
    refine ctx.not_dominant (d.hPF d.p₁
      (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem d.hP).1) ⟨?_, ?_⟩
    · intro x hx z hz
      have h1 : x = d.r₁ := by
        by_contra hc
        exact hx.2 (d.h₁ x ⟨hx.1, hc⟩)
      have h2 : z = d.r₁ := by
        by_contra hc
        exact hz.2 (d.h₁ z ⟨hz.1, hc⟩)
      rw [h1, h2]
    · intro x hx z hz
      have h1 : x = d.r₂ := by
        by_contra hc
        exact hx.2 (heq ▸ d.h₂ x ⟨hx.1, hc⟩)
      have h2 : z = d.r₂ := by
        by_contra hc
        exact hz.2 (heq ▸ d.h₂ z ⟨hz.1, hc⟩)
      rw [h1, h2]
  rcases hcomplete with hleft | hright
  · exact ⟨hleft,
      Workspace.ProofLemmas.Thm75Claim2Five82SecondClique.secondCliqueComplete
        G hG J hJ ctx.H ctx.K ctx.φ ctx.happ ctx.B ctx.c₁ ctx.c₂ ctx.hbranch ctx.hfrom
        ctx.hodd ctx.hlen Y ctx.hYne ctx.hYanti ctx.hYdom ctx.X ctx.Rset ctx.F ctx.hX
        ctx.hRset hFXnot ctx.hFK d.r₁ d.r₂ d.p₁ d.p₂ d.P d.hP d.hPF hp₁₂ d.hr₁ d.hr₂
        d.h₁ d.h₂ d.hno hleft⟩
  · -- PAPER: *"(This is without loss of generality, because in this case 2, there is symmetry
    -- between `b₁ = c₁` and `b₂ = c₂`.)"*
    have hbr : IsBranch ctx.H ctx.B.reverse :=
      Workspace.ProofLemmas.Thm57Claim2Structure.isBranch_reverse ctx.hbranch
    have hfr : IsTrackFrom ctx.H ctx.B.reverse ctx.c₂ ctx.c₁ :=
      Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse ctx.hfrom
    have htl : trackLength ctx.B.reverse = trackLength ctx.B := by simp [trackLength]
    have hRsetR : ctx.Rset = {x : V | ∃ (e : Sym2 (Fin ctx.m)) (he : e ∈ ctx.H.edgeSet),
        e ∈ trackEdges ctx.B.reverse ∧ x = (↑(ctx.φ ⟨e, he⟩) : V)} := by
      rw [ctx.hRset, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
    refine ⟨Workspace.ProofLemmas.Thm75Claim2Five82SecondClique.secondCliqueComplete
      G hG J hJ ctx.H ctx.K ctx.φ ctx.happ ctx.B.reverse ctx.c₂ ctx.c₁ hbr hfr
      (by rw [htl]; exact ctx.hodd) (by rw [htl]; exact ctx.hlen) Y ctx.hYne ctx.hYanti
      (fun y hy => ⟨(ctx.hYdom y hy).2, (ctx.hYdom y hy).1⟩) ctx.X ctx.Rset ctx.F ctx.hX
      hRsetR hFXnot ctx.hFK d.r₂ d.r₁ d.p₂ d.p₁ d.P.reverse ?_ ?_
      (fun h => hp₁₂ h.symm) d.hr₂ d.hr₁ d.h₂ d.h₁ ?_ hright, hright⟩
    · exact Workspace.ProofLemmas.PathBasics.isPathFrom_reverse d.hP
    · exact fun x hx => d.hPF x (List.mem_reverse.mp hx)
    · intro x hx y hy hadj
      rcases d.hno x (List.mem_reverse.mp hx) y hy hadj with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))

/-- Dominance and maximality follow from the geometric witnesses. -/
theorem replacement_dominance {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (Y : Set V) (ctx : ExactCardFive82Context G hG J hJ n Y)
    (rep : ReplacementGeometry ctx) :
    (∀ y ∈ Y, IsDominantFor G rep.appearance.leftClique rep.appearance.rightClique y) ∧
      (∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
        (∀ y ∈ Y', IsDominantFor G rep.appearance.leftClique rep.appearance.rightClique y) →
        Y' = Y) := by
  rcases rep.hcases with hsingle | ⟨d⟩
  · have hold := ctx.oldAppearance.three_le_cliques hJ
    have hnew := rep.appearance.three_le_cliques hJ
    have hequiv := dominant_iff_of_one_clique_replacement G hG
      (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
      rep.appearance.leftClique rep.appearance.rightClique hold.1 hold.2 hnew.1 hnew.2 hsingle
    refine ⟨fun y hy => (hequiv y).mp (ctx.hYdom y hy), ?_⟩
    intro Y' hYY' hanti hdom
    exact ctx.hYmax Y' hYY' hanti (fun y hy => (hequiv y).mpr (hdom y hy))
  · obtain ⟨d⟩ := d
    have hX₁ : ctx.X₁ ⊆ ctx.X := by rw [ctx.hX₁]; exact Set.inter_subset_left
    have hfirst : (NSet G ctx.H ctx.K ctx.φ ctx.c₁ \ {d.r₁} ⊆ ctx.X) ∨
        (NSet G ctx.H ctx.K ctx.φ ctx.c₂ \ {d.r₂} ⊆ ctx.X) := by
      rcases d.hno_T with hleft | hright
      · exact Or.inl (clique_remainder_subset_of_no_T G
          (NSet G ctx.H ctx.K ctx.φ ctx.c₁) ctx.K ctx.Rset ctx.X ctx.X₁ ctx.T d.r₁ d.p₁
          (ctx.clique_subset_K ctx.c₁) d.hr₁ hX₁ ctx.hT d.h₁ hleft)
      · exact Or.inr (clique_remainder_subset_of_no_T G
          (NSet G ctx.H ctx.K ctx.φ ctx.c₂) ctx.K ctx.Rset ctx.X ctx.X₁ ctx.T d.r₂ d.p₂
          (ctx.clique_subset_K ctx.c₂) d.hr₂ hX₁ ctx.hT d.h₂ hright)
    obtain ⟨hc₁, hc₂⟩ := gap_second_clique_complete G hG J hJ n Y ctx rep.appearance d hfirst
    exact dominance_and_maximality_of_double_swap G hG J hJ
      (NSet G ctx.H ctx.K ctx.φ ctx.c₁) (NSet G ctx.H ctx.K ctx.φ ctx.c₂)
      ctx.K ctx.Rset ctx.T ctx.F Y rep.appearance d
      (ctx.clique_subset_K ctx.c₁) (ctx.clique_subset_K ctx.c₂) ctx.hFK
      (fun _ hx => ctx.not_complete hx) ctx.hYne ctx.hYanti ctx.hYmax
      (fun _ hx => by simpa only [ctx.hX] using hc₁ hx)
      (fun _ hx => by simpa only [ctx.hX] using hc₂ hx)

/-- The old attachment on the retained side remains an attachment, and `F` meets the
opposite new side. All new forbidden vertices are in `X`, which `F` avoids. -/
theorem replacement_bridge {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {G : SimpleGraph V} {hG : Berge G} {J : SimpleGraph U} {hJ : IsKConnected J 3}
    {n : ℕ} {Y : Set V} (ctx : ExactCardFive82Context G hG J hJ n Y)
    (rep : ReplacementGeometry ctx) :
    let X₁' := ctx.X ∩ (rep.appearance.leftClique ∪ rep.appearance.rightClique)
    let S' := rep.appearance.rung \ X₁'
    let T' := (rep.appearance.K \ rep.appearance.rung) \ X₁'
    ((ctx.F ∩ S').Nonempty ∧ ∃ t ∈ T', ∃ f ∈ ctx.F, G.Adj t f) ∨
      ((ctx.F ∩ T').Nonempty ∧ ∃ s ∈ S', ∃ f ∈ ctx.F, G.Adj s f) := by
  dsimp only
  have hX₁old (x : V) (hxK : x ∈ ctx.K)
      (hxnew : x ∈ ctx.X ∩ (rep.appearance.leftClique ∪ rep.appearance.rightClique)) :
      x ∈ ctx.X₁ := by
    rw [ctx.hX₁]
    exact ⟨hxnew.1, rep.hcliques ⟨hxnew.2, hxK⟩⟩
  have hnoX₁ (x : V) (hxF : x ∈ ctx.F) :
      x ∉ ctx.X ∩ (rep.appearance.leftClique ∪ rep.appearance.rightClique) :=
    fun hx => ctx.not_mem_X hxF hx.1
  rcases rep.hlocation with ⟨hR, _, x, hxF, hxK, hxR⟩ | ⟨hK, hR, x, hxF, hxR⟩
  · right
    refine ⟨⟨x, hxF, ⟨hxK, ?_⟩, hnoX₁ x hxF⟩, ?_⟩
    · rwa [hR]
    · obtain ⟨s, hs, f, hf, hsf⟩ := ctx.hSF
      rw [ctx.hS] at hs
      have hsK : s ∈ ctx.K := by
        obtain ⟨e, he, _, hse⟩ := ctx.hRset ▸ hs.1
        rw [hse]
        exact (ctx.φ ⟨e, he⟩).property
      exact ⟨s, ⟨hR.symm ▸ hs.1, fun h => hs.2 (hX₁old s hsK h)⟩, f, hf, hsf⟩
  · left
    refine ⟨⟨x, hxF, hxR, hnoX₁ x hxF⟩, ?_⟩
    obtain ⟨t, ht, f, hf, htf⟩ := ctx.hTF
    rw [ctx.hT] at ht
    refine ⟨t, ⟨⟨hK ht.1, ?_⟩, fun h => ht.2 (hX₁old t ht.1.1 h)⟩, f, hf, htf⟩
    exact fun htR => ht.1.2 (hR ⟨htR, ht.1.1⟩)

/-- PAPER (printed pp. 37--38): after replacing `Rb₁b₂` by `R'`, *"there is a proper subset
`F'` of `F` with attachments in `S` and in the new set `T'` ... it follows that we may apply
the inductive hypothesis"*.  In the same-branch case, the last sentence is *"Hence we can apply
induction on `F`, and the result follows."*

This lemma asserts only the promised smaller induction instance. -/
theorem rungReplacementProducesSmallerInstance {V U : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (n : ℕ) (Y : Set V)
    (ctx : ExactCardFive82Context G hG J hJ n Y) :
    Nonempty (SmallerClaim2Instance G J n Y) := by
  obtain ⟨rep⟩ := gap_replacement_geometry G hG J hJ n Y ctx
  obtain ⟨hdom, hmax⟩ := replacement_dominance G hG J hJ n Y ctx rep
  let a := rep.appearance
  let X₁' := ctx.X ∩ (a.leftClique ∪ a.rightClique)
  let S' := a.rung \ X₁'
  let T' := (a.K \ a.rung) \ X₁'
  have hsmall : (a.leftClique \ ctx.X).Subsingleton ∧
      (a.rightClique \ ctx.X).Subsingleton := by
    rw [ctx.hX]
    exact a.cliques_diff_complete_subsingleton hG hJ Y ctx.hYne ctx.hYanti hdom
  have hanti : Anticomplete G S' T' := a.sides_anticomplete ctx.X hsmall
  obtain ⟨F', hproper, hconn, hSF', hTF'⟩ := smaller_connected_of_meets_either
    G S' T' ctx.F ctx.hFconn hanti (replacement_bridge ctx rep)
  refine ⟨{
    m := a.m
    H := a.H
    K := a.K
    φ := a.φ
    happ := a.happ
    B := a.B
    c₁ := a.c₁
    c₂ := a.c₂
    hbranch := a.hbranch
    hfrom := a.hfrom
    hodd := a.hodd
    hlen := a.hlen
    hYdom := hdom
    hYmax := hmax
    X := ctx.X
    X₀ := ctx.X \ a.K
    X₁ := X₁'
    Rset := a.rung
    S := S'
    T := T'
    F := F'
    hX := ctx.hX
    hRset := rfl
    hX₀ := rfl
    hX₁ := rfl
    hS := rfl
    hT := rfl
    hFcard := ncard_le_of_ssubset ctx.hFcard hproper
    hFconn := hconn
    hFdisj := ?_
    hSF := hSF'
    hTF := hTF'
  }⟩
  intro x hx hbad
  have hxF := hproper.subset hx
  rcases hbad with (hxX₀ | hxX₁) | hxY
  · exact ctx.not_mem_X hxF hxX₀.1
  · exact ctx.not_mem_X hxF hxX₁.1
  · exact ctx.hFdisj x hxF (Or.inr hxY)

/-- **Exact-cardinality 5.8.2 rung-replacement step** (printed pp. 37--38).

The displayed quotation in the module docstring is the precise paper step encoded by this
lemma.  Its additional equation says that the immediate smaller-cardinality use of `ih` has
already been exhausted. -/
theorem exactCardRungReplacementStep {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3) (n : ℕ)
    (ih : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V) (φ : H.lineGraph ≃g G.induce K),
      IsAppearance G J H K →
      ∀ (B : List (Fin m)) (c₁ c₂ : Fin m), IsBranch H B → IsTrackFrom H B c₁ c₂ →
        Odd (trackLength B) → 3 ≤ trackLength B →
      ∀ (Y : Set V), Y.Nonempty → AnticonnectedSet G Y →
        (∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) →
        (∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
          (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y) →
      ∀ (X X₀ X₁ Rset S T F : Set V),
        X = {x : V | VertexComplete G x Y} →
        Rset = {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
          e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)} →
        X₀ = X \ K →
        X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂) →
        S = Rset \ X₁ →
        T = (K \ Rset) \ X₁ →
        F.ncard ≤ n → ConnectedSet G F → (∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y) →
        (∃ s ∈ S, ∃ f ∈ F, G.Adj s f) → (∃ t ∈ T, ∃ f ∈ F, G.Adj t f) →
        ((∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
            ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
              IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H') ∨
          AdmitsBalancedSkewPartition G))
    (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List (Fin m)) (c₁ c₂ : Fin m)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y)
    (hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
      (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y)
    (X X₀ X₁ Rset S T : Set V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₀ : X₀ = X \ K)
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hS : S = Rset \ X₁) (hT : T = (K \ Rset) \ X₁)
    (F : Set V) (hFcard : F.ncard = n + 1) (hFconn : ConnectedSet G F)
    (hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y) (hFK : ∀ x ∈ F, x ∉ K)
    (hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f) (hTF : ∃ t ∈ T, ∃ f ∈ F, G.Adj t f)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ConnectedSet G F' →
      (∀ x ∈ F', x ∉ X₀ ∪ X₁ ∪ Y) → (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) →
      (∃ t ∈ T, ∃ f ∈ F', G.Adj t f) → False)
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPF : ∀ x ∈ P, x ∈ F)
    (b₁ b₂ : Fin m) (q : List (Fin m)) (R : List V) (r₁ r₂ : V)
    (hb₁ : b₁ ∈ branchVertices H) (hb₂ : b₂ ∈ branchVertices H)
    (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (hR : IsPathList G R)
    (hRs : {x : V | x ∈ R} =
      {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ R} = {r₁})
    (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ R} = {r₂})
    (hcases :
      ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
      ((∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂}) ∨
          (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
        (Even (pathLength P) ↔ Even (pathLength R))) ∨
      (p₁ = p₂ ∧
        (∀ x ∈ (NSet G H K φ b₁ ∪ NSet G H K φ b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
        (∀ y ∈ K, G.Adj p₁ y →
          y ∈ NSet G H K φ b₁ ∪ NSet G H K φ b₂ ∪ {z : V | z ∈ R}) ∧
        Even (pathLength R)) ∨
      (r₁ = r₂ ∧ (∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂})) ∧
        Even (pathLength P))) :
    ((∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
        ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
          IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H') ∨
      AdmitsBalancedSkewPartition G) := by
  let ctx : ExactCardFive82Context G hG J hJ n Y := {
    m := m
    H := H
    K := K
    φ := φ
    happ := happ
    B := B
    c₁ := c₁
    c₂ := c₂
    hbranch := hbranch
    hfrom := hfrom
    hodd := hodd
    hlen := hlen
    hYne := hYne
    hYanti := hYanti
    hYdom := hYdom
    hYmax := hYmax
    X := X
    X₀ := X₀
    X₁ := X₁
    Rset := Rset
    S := S
    T := T
    hX := hX
    hRset := hRset
    hX₀ := hX₀
    hX₁ := hX₁
    hS := hS
    hT := hT
    F := F
    hFcard := hFcard
    hFconn := hFconn
    hFdisj := hFdisj
    hFK := hFK
    hSF := hSF
    hTF := hTF
    hmin := hmin
    P := P
    p₁ := p₁
    p₂ := p₂
    hP := hP
    hPF := hPF
    b₁ := b₁
    b₂ := b₂
    q := q
    R := R
    r₁ := r₁
    r₂ := r₂
    hb₁ := hb₁
    hb₂ := hb₂
    hq := hq
    hqf := hqf
    hR := hR
    hRs := hRs
    hr₁ := hr₁
    hr₂ := hr₂
    hcases := hcases
  }
  obtain ⟨inst⟩ := rungReplacementProducesSmallerInstance G hG J hJ n Y ctx
  exact ih inst.m inst.H inst.K inst.φ inst.happ inst.B inst.c₁ inst.c₂ inst.hbranch
    inst.hfrom inst.hodd inst.hlen Y hYne hYanti inst.hYdom inst.hYmax inst.X inst.X₀
    inst.X₁ inst.Rset inst.S inst.T inst.F inst.hX inst.hRset inst.hX₀ inst.hX₁ inst.hS
    inst.hT inst.hFcard inst.hFconn inst.hFdisj inst.hSF inst.hTF

end Workspace.ProofLemmas.Thm75Claim2Five82ExactCard
