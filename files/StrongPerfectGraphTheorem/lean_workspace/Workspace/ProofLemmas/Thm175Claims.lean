import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.AnticompleteUnionComponents
import Workspace.ProofLemmas.Thm175Optimal
import Workspace.ProofLemmas.Thm175Symmetry
import Workspace.ProofLemmas.Thm175Claim2Main
import Workspace.ProofLemmas.Thm175Claim3Main
import Workspace.ProofLemmas.Thm175Claim5Main
import Workspace.ProofLemmas.Thm175Claim4Main

/-!
# The numbered claims in the proof of 17.5

This file gives Lean interfaces to claims (2)--(5) in the printed proof.  It
also proves the two finite choices made between those claims: the first missed
vertex of the second antipath block and the last path neighbour of `x₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claims

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm175Minimal
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex has a nonneighbour in a set. -/
def HasNonneighborIn (G : SimpleGraph V) (v : V) (Y : Set V) : Prop :=
  ∃ y ∈ Y, ¬ G.Adj v y

/-- The set of complete edges counted on a path list. -/
def completePathEdges (G : SimpleGraph V) (X : Set V) (p : List V) : Set (Sym2 V) :=
  {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p,
    e = s(u, v) ∧ EdgeComplete G X u v}

/-- The conclusion of printed claim (2). -/
def Claim2Conclusion {G : SimpleGraph V} {z : V} (c : Counterexample G z) : Prop :=
  ∀ x₁ ∈ c.X, ∀ x₂ ∈ c.X, x₁ ≠ x₂ →
    AnticonnectedSet G (c.X \ {x₁}) →
    AnticonnectedSet G (c.X \ {x₂}) →
    Disjoint c.X c.Y ∧
      ((∀ x ∈ c.X, (HasNonneighborIn G x c.Y ↔ x = x₁)) ∨
       (∀ x ∈ c.X, (HasNonneighborIn G x c.Y ↔ x = x₂)))

/-- If two anticonnected sets have a union that is not anticonnected, they are
disjoint and complete to each other.  This is the elementary first step of
claim (2), applied in the complement graph. -/
private theorem disjoint_complete_of_not_anticonnected_union
    (G : SimpleGraph V) (A B : Set V)
    (hA : AnticonnectedSet G A) (hB : AnticonnectedSet G B)
    (hAB : ¬ AnticonnectedSet G (A ∪ B)) :
    Disjoint A B ∧ Complete G A B := by
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    apply hAB
    exact ConnectedSetUnionAttach.connectedSet_union hA hB
      (Or.inl ⟨x, hxA, hxB⟩)
  refine ⟨hdisj, ?_⟩
  intro a ha b hb
  by_contra hnab
  apply hAB
  apply ConnectedSetUnionAttach.connectedSet_union hA hB
  right
  refine ⟨a, ha, b, hb, ?_⟩
  rw [SimpleGraph.compl_adj]
  exact ⟨fun hab => Set.disjoint_left.mp hdisj ha (hab ▸ hb), hnab⟩

/-- The first paragraph of claim (2): if deleting `xᵢ` makes the union with
`Y` non-anticonnected, then `xᵢ` is the unique vertex of `X` with a
nonneighbour in `Y`. -/
private theorem claim2_bad_union
    (G : SimpleGraph V) {z : V} (c : Counterexample G z)
    (xᵢ : V) (hxᵢ : xᵢ ∈ c.X)
    (hdel : AnticonnectedSet G (c.X \ {xᵢ}))
    (hbad : ¬ AnticonnectedSet G ((c.X \ {xᵢ}) ∪ c.Y)) :
    Disjoint c.X c.Y ∧
      ∀ x ∈ c.X, (HasNonneighborIn G x c.Y ↔ x = xᵢ) := by
  classical
  obtain ⟨hdelY, hcompDel⟩ :=
    disjoint_complete_of_not_anticonnected_union G (c.X \ {xᵢ}) c.Y
      hdel c.hYa hbad
  have hYne : c.Y.Nonempty := by
    by_contra hneY
    have hYempty : c.Y = ∅ := Set.not_nonempty_iff_eq_empty.mp hneY
    have hp₁mem : c.core.p₁ ∈ c.core.p :=
      PathBasics.head_mem c.core.hp.2.1
    have hpₙmem : c.core.pₙ ∈ c.core.p :=
      PathBasics.getLast_mem c.core.hp.2.2
    have hp₁Y : VertexComplete G c.core.p₁ c.Y := by
      simp [hYempty, VertexComplete]
    have hp₁eq := (c.core.hYuniq c.core.p₁ hp₁mem).mp hp₁Y
    exact (PathBasics.isPathFrom_ends_ne c.core.hp
      (Nat.le_of_lt c.core.hlong)) hp₁eq
  have hxᵢY : xᵢ ∉ c.Y := by
    intro hxY
    apply hbad
    have heq : (c.X \ {xᵢ}) ∪ c.Y = c.X ∪ c.Y := by
      ext x
      constructor
      · rintro (hx | hy)
        · exact Or.inl hx.1
        · exact Or.inr hy
      · rintro (hx | hy)
        · by_cases hxi : x = xᵢ
          · exact Or.inr (hxi ▸ hxY)
          · exact Or.inl ⟨hx, hxi⟩
        · exact Or.inr hy
    rw [heq]
    exact c.hXYa
  have hXYdisj : Disjoint c.X c.Y := by
    rw [Set.disjoint_left]
    intro x hxX hxY
    by_cases hxi : x = xᵢ
    · exact hxᵢY (hxi ▸ hxY)
    · exact Set.disjoint_left.mp hdelY ⟨hxX, hxi⟩ hxY
  have hXne : c.X.Nonempty := ⟨xᵢ, hxᵢ⟩
  have hxᵢNotComplete : ¬ VertexComplete G xᵢ c.Y := by
    intro hxᵢComp
    have hXYcomp : Complete G c.X c.Y := by
      intro x hxX
      by_cases hxi : x = xᵢ
      · simpa [hxi] using hxᵢComp
      · exact hcompDel x ⟨hxX, hxi⟩
    have hanti : Anticomplete Gᶜ c.X c.Y := by
      intro x hxX y hyY hadj
      rw [SimpleGraph.compl_adj] at hadj
      exact hadj.2 (hXYcomp x hxX y hyY)
    exact (Workspace.Types.AnticompleteUnionComponents.anticompleteUnionComponents
      Gᶜ c.X c.Y hXYdisj hXne hYne hanti).1 c.hXYa
  have hxᵢMiss : HasNonneighborIn G xᵢ c.Y := by
    by_contra hnone
    apply hxᵢNotComplete
    intro y hyY
    by_contra hxy
    exact hnone ⟨y, hyY, hxy⟩
  refine ⟨hXYdisj, ?_⟩
  intro x hxX
  constructor
  · rintro ⟨y, hyY, hxy⟩
    by_contra hxi
    exact hxy (hcompDel x ⟨hxX, hxi⟩ y hyY)
  · rintro rfl
    exact hxᵢMiss

/-- Removing one of the two non-cut vertices gives an odd complete-edge count.
Otherwise it would be a counterexample with the same path and a smaller union,
or with the same union and smaller total side size. -/
private theorem odd_edges_after_delete
    (G : SimpleGraph V) {z : V} (c : Counterexample G z)
    (hopt : IsOptimal c) (x : V) (hxX : x ∈ c.X)
    (hdel : AnticonnectedSet G (c.X \ {x}))
    (hunion : AnticonnectedSet G ((c.X \ {x}) ∪ c.Y)) :
    Odd (completePathEdges G (c.X \ {x}) c.core.p).ncard := by
  classical
  by_contra hnotOdd
  have heven : Even (completePathEdges G (c.X \ {x}) c.core.p).ncard :=
    Nat.not_odd_iff_even.mp hnotOdd
  let dcore : EvenRRConfig G (c.X \ {x}) c.Y z :=
    { p := c.core.p
      p₁ := c.core.p₁
      pₙ := c.core.pₙ
      hp := c.core.hp
      hodd := c.core.hodd
      hlong := c.core.hlong
      houtX := fun w hw hx => c.core.houtX w hw hx.1
      houtY := c.core.houtY
      hp₁X := fun y hy => c.core.hp₁X y hy.1
      hYuniq := c.core.hYuniq
      hzP := c.core.hzP
      hzanti := c.core.hzanti
      heven := by simpa [completePathEdges] using heven }
  let d : Counterexample G z :=
    { X := c.X \ {x}
      Y := c.Y
      core := dcore
      hXa := hdel
      hYa := c.hYa
      hXYa := hunion
      hz := by
        rintro (hx | hy)
        · exact c.hz (Or.inl hx.1)
        · exact c.hz (Or.inr hy)
      hzXY := by
        rintro y (hy | hy)
        · exact c.hzXY y (Or.inl hy.1)
        · exact c.hzXY y (Or.inr hy) }
  have hsub : d.X ∪ d.Y ⊆ c.X ∪ c.Y := by
    rintro y (hy | hy)
    · exact Or.inl hy.1
    · exact Or.inr hy
  by_cases heq : (d.X ∪ d.Y).ncard = (c.X ∪ c.Y).ncard
  · apply hopt.2.2 d
    · rfl
    · exact heq
    · have hdiff : (c.X \ {x}).ncard = c.X.ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hxX
      have hpos : 0 < c.X.ncard := (Set.ncard_pos (Set.toFinite c.X)).mpr ⟨x, hxX⟩
      dsimp [d]
      rw [hdiff]
      omega
  · apply hopt.2.1 d rfl
    exact Set.ncard_lt_ncard
      (Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => heq (congrArg Set.ncard h)⟩)
      (Set.toFinite _)

/-- The remaining line argument in printed claim (2), after both
`(X\{xᵢ})∪Y` have been shown anticonnected and optimality has supplied the two
odd complete-edge counts.

PAPER: *"So we may assume that `(X\{xᵢ})∪Y` is anticonnected for
`i=1,2`. … This proves (2)."* -/
theorem claim2_line_argument
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁))
    (x₁ x₂ : V) (hx₁ : x₁ ∈ c.X) (hx₂ : x₂ ∈ c.X)
    (hne : x₁ ≠ x₂)
    (hdel₁ : AnticonnectedSet G (c.X \ {x₁}))
    (hdel₂ : AnticonnectedSet G (c.X \ {x₂}))
    (hunion₁ : AnticonnectedSet G ((c.X \ {x₁}) ∪ c.Y))
    (hunion₂ : AnticonnectedSet G ((c.X \ {x₂}) ∪ c.Y))
    (hodd₁ : Odd (completePathEdges G (c.X \ {x₁}) c.core.p).ncard)
    (hodd₂ : Odd (completePathEdges G (c.X \ {x₂}) c.core.p).ncard) :
    Disjoint c.X c.Y ∧
      ((∀ x ∈ c.X, (HasNonneighborIn G x c.Y ↔ x = x₁)) ∨
       (∀ x ∈ c.X, (HasNonneighborIn G x c.Y ↔ x = x₂))) := by
  exact (Thm175Claim2Main.line_argument_absurd G hG z c hopt hfirst
    x₁ x₂ hx₁ hx₂ hne hdel₁ hdel₂ hunion₁ hunion₂ hodd₁ hodd₂).elim

/-- **17.5, claim (2).**

PAPER: *"Suppose that `x₁,x₂ ∈ X` are distinct and such that
`X \ {xᵢ}` is anticonnected for `i=1,2`. Then `X ∩ Y = ∅`, and one of
`x₁,x₂` is the unique vertex of `X` with a nonneighbour in `Y`."* -/
theorem claim2
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁)) :
    Claim2Conclusion c := by
  intro x₁ hx₁ x₂ hx₂ hne hdel₁ hdel₂
  by_cases hunion₁ : AnticonnectedSet G ((c.X \ {x₁}) ∪ c.Y)
  · by_cases hunion₂ : AnticonnectedSet G ((c.X \ {x₂}) ∪ c.Y)
    · have hodd₁ := odd_edges_after_delete G c hopt x₁ hx₁ hdel₁ hunion₁
      have hodd₂ := odd_edges_after_delete G c hopt x₂ hx₂ hdel₂ hunion₂
      exact claim2_line_argument G hG z c hopt hfirst x₁ x₂ hx₁ hx₂ hne
        hdel₁ hdel₂ hunion₁ hunion₂ hodd₁ hodd₂
    · obtain ⟨hdisj, huniq⟩ :=
        claim2_bad_union G c x₂ hx₂ hdel₂ hunion₂
      exact ⟨hdisj, Or.inr huniq⟩
  · obtain ⟨hdisj, huniq⟩ :=
      claim2_bad_union G c x₁ hx₁ hdel₁ hunion₁
    exact ⟨hdisj, Or.inl huniq⟩

/-- The block form of printed claim (3).  The concatenation `qX ++ qY` is the
paper's antipath `x₁-⋯-x_s-y₁-⋯-y_t`; the two list vertex sets are exactly
`X` and `Y`, and both blocks contain at least two vertices. -/
structure AntipathBlocks (G : SimpleGraph V) (X Y : Set V) where
  qX : List V
  qY : List V
  x₁ : V
  yₜ : V
  hXlong : 1 < qX.length
  hYlong : 1 < qY.length
  hxhead : qX.head? = some x₁
  hylast : qY.getLast? = some yₜ
  hanti : IsAntipathFrom G (qX ++ qY) x₁ yₜ
  hXverts : ∀ x : V, x ∈ qX ↔ x ∈ X
  hYverts : ∀ y : V, y ∈ qY ↔ y ∈ Y

/-- The structural part of claim (3), after claim (2) has been applied on both
sides using the `X,Y` symmetry.

PAPER: *"There is an antipath `x₁-⋯-x_s-y₁-⋯-y_t` such that
`s,t>1` and `X={x₁,…,x_s}`, and `Y={y₁,…,y_t}`."* -/
theorem claim3_from_symmetric_claim2
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁))
    (hclaim2 : Claim2Conclusion c)
    (hswapOpt : IsOptimal (swapCounterexample G z c hfirst))
    (hswapFirst : ∀ w ∈ (swapCounterexample G z c hfirst).core.p,
      (VertexComplete G w (swapCounterexample G z c hfirst).X ↔
        w = (swapCounterexample G z c hfirst).core.p₁))
    (hswapClaim2 : Claim2Conclusion (swapCounterexample G z c hfirst)) :
    Nonempty (AntipathBlocks G c.X c.Y) := by
  obtain ⟨p, q, a, b, hp, hq, hh, ht, hanti, hX, hY⟩ :=
    Thm175Claim3Main.blocks G hG z c hfirst hswapFirst hclaim2 hswapClaim2
  exact ⟨⟨p, q, a, b, hp, hq, hh, ht, hanti, hX, hY⟩⟩

/-- **17.5, claim (3).**  Claim (1) makes the counterexample symmetric under
reversing its path and exchanging `X,Y`; claim (2) is therefore available on
both sides before the structural conclusion is invoked. -/
theorem claim3
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁))
    (hclaim2 : Claim2Conclusion c) :
    Nonempty (AntipathBlocks G c.X c.Y) := by
  let cs := swapCounterexample G z c hfirst
  have hsopt : IsOptimal cs := swap_isOptimal G z c hopt hfirst
  have hsfirst := first_unique_of_optimal G hG z cs hsopt
  have hsclaim2 := claim2 G hG z cs hsopt hsfirst
  exact claim3_from_symmetric_claim2 G hG z c hopt hfirst hclaim2
    hsopt hsfirst hsclaim2

/-- The first vertex `y_{t₀}` in the second block missed by `p₁`.  Indices in
this structure are zero-based. -/
structure FirstMissContext {G : SimpleGraph V} {X Y : Set V}
    (p₁ : V) (b : AntipathBlocks G X Y) where
  t₀ : ℕ
  ht₀ : t₀ < b.qY.length
  hmiss : ¬ G.Adj p₁ (b.qY[t₀]'ht₀)
  hbefore : ∀ j (hj : j < t₀),
    G.Adj p₁ (b.qY[j]'(lt_trans hj ht₀))

/-- The paper's set
`W=(X\{x₁})∪{y₁,…,y_{t₀-1}}`, using zero-based list operations. -/
def W {G : SimpleGraph V} {X Y : Set V} {p₁ : V}
    (b : AntipathBlocks G X Y) (t : FirstMissContext p₁ b) : Set V :=
  (X \ {b.x₁}) ∪ {y : V | y ∈ b.qY.take t.t₀}

/-- The unnumbered choice immediately before claim (4): take the first vertex
of the `Y` block that is nonadjacent to `p₁`. -/
theorem exists_first_miss
    (G : SimpleGraph V) {z : V} (c : Counterexample G z)
    (b : AntipathBlocks G c.X c.Y) :
    Nonempty (FirstMissContext c.core.p₁ b) := by
  classical
  have hp₁mem : c.core.p₁ ∈ c.core.p :=
    PathBasics.head_mem c.core.hp.2.1
  have hpₙmem : c.core.pₙ ∈ c.core.p :=
    PathBasics.getLast_mem c.core.hp.2.2
  have hp₁nepₙ : c.core.p₁ ≠ c.core.pₙ :=
    PathBasics.isPathFrom_ends_ne c.core.hp (Nat.le_of_lt c.core.hlong)
  have hp₁notY : ¬ VertexComplete G c.core.p₁ c.Y := by
    intro hcomp
    exact hp₁nepₙ ((c.core.hYuniq c.core.p₁ hp₁mem).mp hcomp)
  have hexY : ∃ y ∈ c.Y, ¬ G.Adj c.core.p₁ y := by
    by_contra hnone
    apply hp₁notY
    intro y hy
    by_contra hnadj
    exact hnone ⟨y, hy, hnadj⟩
  obtain ⟨y, hyY, hmiss⟩ := hexY
  have hyq : y ∈ b.qY := (b.hYverts y).mpr hyY
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hyq
  let Bad : ℕ → Prop := fun k => ∃ hk : k < b.qY.length,
    ¬ G.Adj c.core.p₁ (b.qY[k]'hk)
  have hexBad : ∃ k, Bad k := ⟨j, hj, hjy ▸ hmiss⟩
  let t₀ := Nat.find hexBad
  obtain ⟨ht₀, ht₀miss⟩ := Nat.find_spec hexBad
  refine ⟨⟨t₀, ht₀, ht₀miss, ?_⟩⟩
  intro k hk
  by_contra hkmiss
  have hle : t₀ ≤ k := Nat.find_min' hexBad ⟨lt_trans hk ht₀, hkmiss⟩
  omega

/-- The exact universal parity assertion in printed claim (4), with a subpath
represented by its two inclusive indices in `c.core.p`. -/
def Claim4Conclusion {G : SimpleGraph V} {z : V}
    (c : Counterexample G z) (b : AntipathBlocks G c.X c.Y)
    (t : FirstMissContext c.core.p₁ b) : Prop :=
  ∀ a d (had : a < d) (hd : d < c.core.p.length),
    G.Adj b.x₁ (c.core.p[a]'(lt_trans had hd)) →
    G.Adj b.x₁ (c.core.p[d]'hd) →
    Even (completePathEdges G (W b t)
      ((c.core.p.drop a).take (d - a + 1))).ncard

/-- **17.5, claim (4).**

PAPER: *"For every subpath `P'` of `P`, if the ends of `P'` are
adjacent to `x₁`, then there are an even number of `W`-complete edges in
`P'`."* -/
theorem claim4
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁))
    (b : AntipathBlocks G c.X c.Y)
    (t : FirstMissContext c.core.p₁ b) :
    Claim4Conclusion c b t := by
  let s : Thm175Claim4Setup.Setup c :=
    ⟨b.qX, b.qY, b.x₁, b.yₜ, b.hXlong, b.hYlong, b.hxhead, b.hylast,
      b.hanti, b.hXverts, b.hYverts, t.t₀, t.ht₀, t.hmiss, t.hbefore⟩
  exact Thm175Claim4Main.main hG s hopt hfirst

/-- The maximum-indexed neighbour of `x₁` on `P`. -/
structure LastNeighborContext {G : SimpleGraph V} {X Y : Set V} {z : V}
    (c : Counterexample G z) (b : AntipathBlocks G X Y) where
  h : ℕ
  hlt : h < c.core.p.length
  hadj : G.Adj b.x₁ (c.core.p[h]'hlt)
  hmax : ∀ j (hj : j < c.core.p.length),
    G.Adj b.x₁ (c.core.p[j]'hj) → j ≤ h

/-- The unnumbered choice after claim (4): choose the last neighbour of `x₁`
on `P`. -/
theorem exists_last_neighbor
    (G : SimpleGraph V) {z : V} (c : Counterexample G z)
    (b : AntipathBlocks G c.X c.Y) :
    Nonempty (LastNeighborContext c b) := by
  classical
  have hp₁mem : c.core.p₁ ∈ c.core.p :=
    PathBasics.head_mem c.core.hp.2.1
  have hx₁q : b.x₁ ∈ b.qX := List.mem_of_mem_head? b.hxhead
  have hx₁X : b.x₁ ∈ c.X := (b.hXverts b.x₁).mp hx₁q
  have hp₁x₁ : G.Adj c.core.p₁ b.x₁ := c.core.hp₁X b.x₁ hx₁X
  have hpos : 0 < c.core.p.length := PathBasics.path_length_pos c.core.hp.1
  have hp0 : c.core.p[0]'hpos = c.core.p₁ :=
    PathBasics.getElem_zero_of_head? c.core.hp.2.1 hpos
  let S : Finset (Fin c.core.p.length) :=
    Finset.univ.filter (fun j => G.Adj b.x₁ c.core.p[j.1])
  have hSne : S.Nonempty := by
    refine ⟨⟨0, hpos⟩, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hp0]
    exact hp₁x₁.symm
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S (fun k => k.1) hSne
  refine ⟨⟨j.1, j.2, ?_, ?_⟩⟩
  · exact (Finset.mem_filter.mp hjS).2
  · intro k hk hadj
    exact hjmax ⟨k, hk⟩ (by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hadj)

/-- **17.5, claim (5).**  In the paper's one-based indexing this is `h>1`;
with Lean's zero-based indices it is `0<h`.

PAPER: *"(5) `h>1`."* -/
theorem claim5
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁))
    (b : AntipathBlocks G c.X c.Y)
    (t : FirstMissContext c.core.p₁ b)
    (h4 : Claim4Conclusion c b t)
    (last : LastNeighborContext c b) :
    0 < last.h := by
  by_contra hn
  have hh : last.h = 0 := by omega
  let s : Thm175Claim4Setup.Setup c :=
    ⟨b.qX, b.qY, b.x₁, b.yₜ, b.hXlong, b.hYlong, b.hxhead, b.hylast,
      b.hanti, b.hXverts, b.hYverts, t.t₀, t.ht₀, t.hmiss, t.hbefore⟩
  apply Thm175Claim5Main.not_unique_neighbor hG s hopt hfirst
  intro v hv hadj
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
  have hk0 : k = 0 := by have := last.hmax k hk hadj; omega
  subst k
  exact PathBasics.getElem_zero_of_head? c.core.hp.2.1 hk

end Workspace.ProofLemmas.Thm175Claims
