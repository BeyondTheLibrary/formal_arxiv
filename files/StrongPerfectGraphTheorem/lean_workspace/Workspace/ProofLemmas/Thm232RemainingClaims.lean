import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions
import Workspace.Types.Pseudowheels
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PseudowheelBuilder
import Workspace.Statements.S02.Thm_2_11
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.Thm232Final
import Workspace.ProofLemmas.Thm232ClosingAttachmentPath
import Workspace.ProofLemmas.Thm232ClosingOrientation
import Workspace.ProofLemmas.Thm232Claim5SecondOutcome
import Workspace.ProofLemmas.Thm232Claim5Path
import Workspace.ProofLemmas.Thm232Claim3C2

/-!
# 23.2 — isolated obligations after claim (3)

The proof of 23.2 has three distinct tasks after claim (3).  We record their exact outputs here
so that the assembly in `Thm232Endgame` does not hide them inside one large assertion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232RemainingClaims

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The data about `z-y-p₁-⋯-p_k` used in the proof of claim (5). -/
structure Claim5PathData (G : SimpleGraph V) (C : List V) (Y : Set V) (x₀ z x₁ y : V)
    (T : List V) where
  P : List V
  pn : V
  path : IsPathFrom G P z pn
  second : P.tail.head? = some y
  outside : ∀ v ∈ P, v ∉ Y ∧ v ∉ ({x₀, x₁} : Set V)
  long : 4 ≤ pathLength P
  hubComplete : ∀ v ∈ P, VertexComplete G v Y ↔ v = z ∨ v = pn
  pnNotPairComplete : ¬ VertexComplete G pn ({x₀, x₁} : Set V)
  pnInA : pn ∈ ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V))
  interiorAllowed : ∀ v ∈ SPGT.interior P,
    v ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)) ∪
      {q : V | q ∈ SPGT.interior T}
  tailContains : ∀ v ∈ SPGT.interior T, v ∈ P.tail

/-- **PAPER (23.2, claims (4)–(5), printed p. 140):**
*"Let `P` be a path `y-p₁-⋯-p_k` from `y` to some `Y`-complete vertex `p_k ∈ A₀`, with
interior in `A₀ ∪ {v₁,…,v_n}`, such that `p_k` is the only `Y`-complete vertex in `P`. …
From (4), `k ≥ 3`."*

The structure uses the path with `z` prepended.  Its `tailContains` field is the printed
inclusion `{y,v₁,…,v_n} ⊆ {y,p₁,…,p_{k-1}}`. -/
theorem claim5_path_gap (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hnbc : KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hpath : IsPathFrom G T z w) (hwC : w ∈ C) (hwz : w ≠ z)
    (hw0 : w ≠ x₀) (hw1 : w ≠ x₁)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁))
    (h3 : VertexAnticomplete G y
      ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)))
    (hattach : ∀ (i : ℕ) (hi : i + 2 < T.length),
      VertexAnticomplete G (T[i]'(by omega))
        ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V))) :
    Nonempty (Claim5PathData G C Y x₀ z x₁ y T) := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hCY : ∀ v ∈ C, v ∉ Y := hw.2.1.2.2
  obtain ⟨-, hc2C, -, -⟩ := KiteTailBasics.hole_triple hC ⟨k + d, hpre2⟩
  have p0 : C[(k + 0) % C.length]'(Nat.mod_lt _ hn) = x₀ :=
    (Thm232Claim3C2.prefix_getElem hn hpre1 (i := 0) (j := k + 0) (by simp) rfl).symm
  have p1 : C[(k + 1) % C.length]'(Nat.mod_lt _ hn) = z :=
    (Thm232Claim3C2.prefix_getElem hn hpre1 (i := 1) (j := k + 1) (by simp) rfl).symm
  have p2 : C[(k + 2) % C.length]'(Nat.mod_lt _ hn) = x₁ :=
    (Thm232Claim3C2.prefix_getElem hn hpre1 (i := 2) (j := k + 2) (by simp) rfl).symm
  have pd1 : C[(k + (d + 1)) % C.length]'(Nat.mod_lt _ hn) = c₂ :=
    (Thm232Claim3C2.prefix_getElem hn hpre2 (i := 1) (j := k + (d + 1)) (by simp)
      (by omega)).symm
  have hmodne : ∀ i : ℕ, i ≤ 2 → i % C.length ≠ (d + 1) % C.length := by
    intro i hi
    rw [Thm232Claim3C2.mod_le_self hn (by omega),
      Thm232Claim3C2.mod_le_self hn (by omega)]
    split_ifs <;> omega
  have hc2A : c₂ ∈ ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)) := by
    refine ⟨hc2C, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro he
      exact Thm232Claim3C2.pos_ne hC.2.1 hn k 1 (d + 1) (hmodne 1 (by omega))
        (by rw [p1, pd1, he])
    · intro he
      exact Thm232Claim3C2.pos_ne hC.2.1 hn k 0 (d + 1) (hmodne 0 (by omega))
        (by rw [p0, pd1, he])
    · intro he
      exact Thm232Claim3C2.pos_ne hC.2.1 hn k 2 (d + 1) (hmodne 2 (by omega))
        (by rw [p2, pd1, he])
  have hwA : w ∈ ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)) := by
    refine ⟨hwC, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hwz, hw0, hw1⟩
  -- claim (4) of the paper, in the shape `exists_claim5_path` consumes it
  have hclaim4 : T.length = 4 → ∀ v ∈ SPGT.interior T, v ≠ y →
      ∀ u ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)), G.Adj v u →
        ¬ VertexComplete G u Y := by
    intro hlen4 v hv hvy u hu hadj
    have hRlen : R.length = 2 := by rw [hTeq] at hlen4; simpa using hlen4
    obtain ⟨v₁, w', hR⟩ : ∃ a b, R = [a, b] := by
      match R, hRlen with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    subst hR
    have hTeq4 : T = [z, y, v₁, w'] := hTeq
    have hww : w' = w := by
      have := hpath.2.2
      rw [hTeq4] at this
      simpa using this
    subst hww
    have hv' : v = v₁ := by
      rw [hTeq4] at hv
      simp [SPGT.interior] at hv
      rcases hv with hv | hv
      · exact absurd hv hvy
      · exact hv
    subst hv'
    exact Thm232Claim5Path.claim4_gap G hG hbsp C Y hopt x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn
      hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hnbc hexh T y v w' hTeq4 hpath hwA
      havoid hint h2 h3 u hu hadj
  obtain ⟨P, pn, hpathP, hsecond, houtside, hlong, hhub, hpnpair, hpnA, hinterior,
    htail⟩ :=
    Thm232Claim5Path.exists_claim5_path G C Y hC hn6 hCY x₀ z x₁ c₂ k hpre1 hnb hzY
      hc2A hc2Y T R y w hTeq hpath hwA havoid hint hattach h3 hclaim4
  exact ⟨⟨P, pn, hpathP, hsecond, houtside, hlong, hhub, hpnpair, hpnA, hinterior,
    htail⟩⟩

/-- The path supplied for claim (5) has even length.  This is the printed parenthetical
*"and therefore has even length by 13.6"*: if its length were odd, 13.6 would either give a
`Y`-complete edge, although only its nonadjacent ends are `Y`-complete, or say its length is
three, although it has length at least four. -/
theorem claim5_path_even (G : SimpleGraph V) (hG : InF8 G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ y : V) (T : List V) (data : Claim5PathData G C Y x₀ z x₁ y T) :
    Even (pathLength data.P) := by
  classical
  rcases Nat.even_or_odd (pathLength data.P) with heven | hodd
  · exact heven
  · exfalso
    have hYP : Y ⊆ {v : V | v ∈ data.P}ᶜ := by
      intro v hvY hvP
      exact (data.outside v hvP).1 hvY
    have hYanti : AnticonnectedSet G Y := hopt.1.2.1.2.1
    have hzY : VertexComplete G z Y := by
      have hzmem : z ∈ data.P := PathBasics.head_mem data.path.2.1
      exact (data.hubComplete z hzmem).mpr (Or.inl rfl)
    have hpnY : VertexComplete G data.pn Y := by
      have hpnmem : data.pn ∈ data.P := PathBasics.getLast_mem data.path.2.2
      exact (data.hubComplete data.pn hpnmem).mpr (Or.inr rfl)
    have hlen : 5 ≤ data.P.length := by
      have hlong := data.long
      rw [PathBasics.pathLength_eq] at hlong
      omega
    have hzn : ¬ G.Adj z data.pn := by
      have hfirst : data.P[0]'(by omega) = z :=
        PathBasics.getElem_zero_of_head? data.path.2.1 (by omega)
      have hlast : data.P[data.P.length - 1]'(by omega) = data.pn :=
        PathBasics.getElem_last_of_getLast? data.path.2.2 (by omega)
      intro hadj
      apply PathBasics.path_ends_not_adj data.path.1 (by omega)
      simpa only [hfirst, hlast] using hadj
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1.1 data.P z data.pn
        data.path hodd Y hYP hYanti hzY hpnY with hedge | hthree
    · obtain ⟨u, hu, v, hv, huv⟩ := hedge
      have hue := (data.hubComplete u hu).mp huv.2.1
      have hve := (data.hubComplete v hv).mp huv.2.2
      rcases hue with rfl | rfl <;> rcases hve with rfl | rfl
      · exact G.irrefl huv.1
      · exact hzn huv.1
      · exact hzn huv.1.symm
      · exact G.irrefl huv.1
    · have hlong := data.long
      omega

/-- **PAPER (23.2, claim (5), printed p. 140):** *"By 2.11 … it follows that one of `x₀, x₁`
is nonadjacent to all of `y, p₁, …, p_{k-1}`."*

In the second outcome of 2.11 the path is `a-y-p₁-⋯-p_k-b` with `{a,b} = {x₀,x₁}`, and the
vertex with that property is `b`: by inducedness its only neighbour on `y-p₁-⋯-p_k` is `p_k`,
which is `Y`-complete, whereas no vertex of the interior of `T` is.  (The earlier `False`
conclusion here was stronger than the paper's, which never excludes the second outcome.) -/
theorem claim5_second_alternative_gap (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hnbc : KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hTpath : IsPathFrom G T z w) (hwC : w ∈ C) (hwz : w ≠ z)
    (hw0 : w ≠ x₀) (hw1 : w ≠ x₁)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁))
    (h3 : VertexAnticomplete G y
      ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)))
    (data : Claim5PathData G C Y x₀ z x₁ y T)
    (a : V) (ha : a ∈ ({x₀, x₁} : Set V))
    (b : V) (hb : b ∈ ({x₀, x₁} : Set V))
    (hab : ¬ G.Adj a b)
    (hpath : IsPathList G (a :: (data.P.tail ++ [b]))) :
    VertexAnticomplete G b {v : V | v ∈ SPGT.interior T} := by
  have hlen : 5 ≤ data.P.length := by
    have hlong := data.long
    rw [PathBasics.pathLength_eq] at hlong
    omega
  have hpnY : VertexComplete G data.pn Y :=
    (data.hubComplete data.pn (PathBasics.getLast_mem data.path.2.2)).mpr (Or.inr rfl)
  exact Thm232Claim5SecondOutcome.second_outcome_anticomplete (by omega) data.path.2.2
    hpnY data.tailContains (fun v hv => (hint v hv).2) hpath

/-- **PAPER (23.2), claim (5):** one of `x₀,x₁` has no neighbours in the interior of `T`,
which is the paper's set `{y,v₁,…,v_n}`. -/
theorem claim5 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hnbc : KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hpath : IsPathFrom G T z w) (hwC : w ∈ C) (hwz : w ≠ z)
    (hw0 : w ≠ x₀) (hw1 : w ≠ x₁)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁))
    (h3 : VertexAnticomplete G y
      ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)))
    (hattach : ∀ (i : ℕ) (hi : i + 2 < T.length),
      VertexAnticomplete G (T[i]'(by omega))
        ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V))) :
    VertexAnticomplete G x₀ {v : V | v ∈ SPGT.interior T} ∨
      VertexAnticomplete G x₁ {v : V | v ∈ SPGT.interior T} := by
  classical
  let pair : Set V := {x₀, x₁}
  have hwheel : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hwheel.1.1
  obtain ⟨hx₀C, hzC, hx₁C, -⟩ :=
    KiteTailBasics.hole_triple hC ⟨k, hpre1⟩
  have hYne : Y.Nonempty := hwheel.2.1.1
  have hYanti : AnticonnectedSet G Y := hwheel.2.1.2.1
  have hCY : ∀ v ∈ C, v ∉ Y := hwheel.2.1.2.2
  have hpairNe : pair.Nonempty := ⟨x₀, by simp [pair]⟩
  have hpairNadj : ¬ G.Adj x₀ x₁ :=
    KiteTailBasics.rimNeighbours_not_adj hC hzC hnb
  have hsingle : AnticonnectedSet G ({x₀} : Set V) := by
    intro p q
    exact (Subtype.ext (p.2.trans q.2.symm) ▸ SimpleGraph.Reachable.refl p)
  have hpairAnti : AnticonnectedSet G pair := by
    have heq : pair = ({x₀} : Set V) ∪ {x₁} := by
      ext v
      simp [pair, or_comm]
    rw [heq]
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hsingle
      ⟨x₀, rfl, by
        rw [SimpleGraph.compl_adj]
        exact ⟨hnb.1.symm, fun h => hpairNadj h.symm⟩⟩
  have hdisj : Disjoint Y pair := by
    rw [Set.disjoint_left]
    intro v hvY hvp
    simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hvp
    rcases hvp with hvp | hvp
    · exact hCY v (hvp.symm ▸ hx₀C) hvY
    · exact hCY v (hvp.symm ▸ hx₁C) hvY
  have hYpair : Complete G Y pair := by
    intro a ha b hb
    simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact (h0Y a ha).symm
    · exact (h1Y a ha).symm
  have hpairY : Complete G pair Y := by
    intro a ha b hb
    simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact h0Y b hb
    · exact h1Y b hb
  have hzPair : VertexComplete G z pair := by
    intro v hv
    simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hnb.2.2.2.1
    · exact hnb.2.2.2.2.1
  have hyNotPair : ¬ VertexComplete G y pair := by
    intro hy
    apply h2
    exact ⟨hy x₀ (by simp [pair]), hy x₁ (by simp [pair])⟩
  obtain ⟨data⟩ := claim5_path_gap G hG hbsp C Y hopt x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn
    hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hnbc hexh T R y w hTeq hpath
    hwC hwz hw0 hw1 havoid hint h2 h3 hattach
  have hlen : 5 ≤ data.P.length := by
    have hlong := data.long
    rw [PathBasics.pathLength_eq] at hlong
    omega
  have hzmem : z ∈ data.P := PathBasics.head_mem data.path.2.1
  have hpairUnique : ∀ v ∈ data.P, VertexComplete G v pair ↔ v = z :=
    PseudowheelBuilder.unique_vertexComplete_of_no_pseudowheel
      hG.2.1 hdisj hYne hpairNe hYanti hpairAnti hYpair data.path data.second
      data.outside hlen data.hubComplete hzmem hzPair hyNotPair data.pnNotPairComplete
  have heven := claim5_path_even G hG C Y hopt x₀ z x₁ y T data
  have h211 := _root_.Workspace.Statements.S02.SPGT.thm_2_11 G hG.1.1.1.1.1 pair Y
    hdisj.symm hpairNe hYne hpairAnti hYanti hpairY data.P z data.pn data.path.1
    (fun v hv hmem => hmem.elim (data.outside v hv).2 (data.outside v hv).1)
    heven data.long data.path.2.1 data.path.2.2 hpairUnique data.hubComplete
  rcases h211 with ⟨a, ha, hanti⟩ | ⟨a, ha, b, hb, hab, habPath⟩
  · simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · left
      intro v hv
      exact hanti v (data.tailContains v hv)
    · right
      intro v hv
      exact hanti v (data.tailContains v hv)
  · have hanti := claim5_second_alternative_gap G hG hbsp C Y hopt x₀ z x₁ c₁ c₂ c₃ k d
      hd2 hdn hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hnbc hexh T R y w hTeq
      hpath hwC hwz hw0 hw1 havoid hint h2 h3 data a ha b hb hab habPath
    simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact Or.inl hanti
    · exact Or.inr hanti

/-- The full collection of hypotheses available after claim (3) in the proof of 23.2.  Keeping
them together ensures that each closing gap below states the corresponding paper sentence in
its real context. -/
structure EndgameContext (G : SimpleGraph V) (C : List V) (Y : Set V)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ) (T R : List V) (y w : V) where
  hG : InF8 G
  hbsp : ¬ AdmitsBalancedSkewPartition G
  hopt : OptimalWheel G C Y
  hmin : ∀ C' : List V, IsWheel G C' Y → yEdgeCount G Y C ≤ yEdgeCount G Y C'
  hd2 : 2 ≤ d
  hdn : d + 2 ≤ C.length
  hpre1 : [x₀, z, x₁] <+: C.rotate k
  hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d)
  h0Y : VertexComplete G x₀ Y
  hzY : VertexComplete G z Y
  h1Y : VertexComplete G x₁ Y
  hc1Y : VertexComplete G c₁ Y
  hc2Y : VertexComplete G c₂ Y
  hc3Y : VertexComplete G c₃ Y
  hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁
  hnbc : KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃
  hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
    ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
    ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃}
  hTeq : T = z :: y :: R
  hpath : IsPathFrom G T z w
  hwC : w ∈ C
  hwz : w ≠ z
  hw0 : w ≠ x₀
  hw1 : w ≠ x₁
  havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁
  hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y
  h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁)
  h3 : VertexAnticomplete G y ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V))

/-- **Remaining gap, PAPER (23.2, first half of the closing paragraph, printed pp. 140–141):**
if `x₀` has no neighbour in `F`, the path `S`, 2.10, 13.6, and 17.1 force `x₀ = c₃`.
After exchanging `x₀,x₁`, the other side has an attachment in `F`.  The second disjunct is the
same statement with the two sides exchanged. -/
theorem closing_orientation_gap (G : SimpleGraph V) (C : List V) (Y : Set V)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ) (T R : List V) (y w : V)
    (ctx : EndgameContext G C Y x₀ z x₁ c₁ c₂ c₃ k d T R y w)
    (hF : VertexAnticomplete G x₀ {v : V | v ∈ SPGT.interior T} ∨
      VertexAnticomplete G x₁ {v : V | v ∈ SPGT.interior T}) :
    (VertexAnticomplete G x₀ {v : V | v ∈ SPGT.interior T} ∧ x₀ = c₃ ∧
        ∃ v ∈ SPGT.interior T, G.Adj x₁ v) ∨
      (VertexAnticomplete G x₁ {v : V | v ∈ SPGT.interior T} ∧ x₁ = c₁ ∧
        ∃ v ∈ SPGT.interior T, G.Adj x₀ v) := by
  exact Workspace.ProofLemmas.Thm232ClosingOrientation.orientation G ctx.hG C Y ctx.hopt.1
    x₀ z x₁ c₁ c₂ c₃ k d ctx.hd2 ctx.hdn ctx.hpre1 ctx.hpre2
    ctx.h0Y ctx.hzY ctx.h1Y ctx.hnb ctx.hexh T R y w ctx.hTeq ctx.hpath
    ctx.hwC ctx.hwz ctx.havoid ctx.hint ctx.h3 hF

/-- **Remaining gap, PAPER (23.2, closing paragraph, printed p. 141):**
*"There are therefore two attachments of `F` in `C` with opposite wheel-parity, and two that
are nonadjacent. By (1), 16.2, 22.3 and the optimality of the wheel … there is a path `R`
between `z,c₂` with interior in `F`, and no vertex of `C` has neighbours in the interior of
`R` except `z,c₂`."* -/
theorem attachment_path_gap (G : SimpleGraph V) (C : List V) (Y : Set V)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ) (T R : List V) (y w : V)
    (ctx : EndgameContext G C Y x₀ z x₁ c₁ c₂ c₃ k d T R y w)
    (horient :
      (VertexAnticomplete G x₀ {v : V | v ∈ SPGT.interior T} ∧ x₀ = c₃ ∧
          ∃ v ∈ SPGT.interior T, G.Adj x₁ v) ∨
        (VertexAnticomplete G x₁ {v : V | v ∈ SPGT.interior T} ∧ x₁ = c₁ ∧
          ∃ v ∈ SPGT.interior T, G.Adj x₀ v)) :
    ∃ Q : List V, IsPathFrom G Q z c₂ ∧
      (∀ v ∈ SPGT.interior Q, v ∈ SPGT.interior T) ∧
      (∀ c ∈ C, ∀ v ∈ SPGT.interior Q, G.Adj c v → c = z ∨ c = c₂) := by
  exact Workspace.ProofLemmas.Thm232ClosingAttachmentPath.attachment_path G ctx.hG C Y ctx.hopt
    x₀ z x₁ c₁ c₂ c₃ k d ctx.hd2 ctx.hdn ctx.hpre1 ctx.hpre2
    ctx.h0Y ctx.hzY ctx.h1Y ctx.hc1Y ctx.hc2Y ctx.hc3Y ctx.hnb ctx.hnbc ctx.hexh
    T w ctx.hpath ctx.hwC ctx.hwz ctx.havoid ctx.hint
    (horient.elim (fun h => Or.inl ⟨h.1, h.2.1⟩) (fun h => Or.inr ⟨h.1, h.2.1⟩))

/-- **Remaining gap, PAPER (23.2, final sentence, printed p. 141):**
*"But then the hole formed by the union of `R` and the path `C \ x₀` is the rim of an odd
wheel with hub `Y`, a contradiction."*

The two alternatives record which symmetric rim vertex is deleted. -/
theorem final_odd_wheel_gap (G : SimpleGraph V) (C : List V) (Y : Set V)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ) (T R : List V) (y w : V)
    (ctx : EndgameContext G C Y x₀ z x₁ c₁ c₂ c₃ k d T R y w)
    (Q : List V)
    (horient :
      (VertexAnticomplete G x₀ {v : V | v ∈ SPGT.interior T} ∧ x₀ = c₃ ∧
          ∃ v ∈ SPGT.interior T, G.Adj x₁ v) ∨
        (VertexAnticomplete G x₁ {v : V | v ∈ SPGT.interior T} ∧ x₁ = c₁ ∧
          ∃ v ∈ SPGT.interior T, G.Adj x₀ v))
    (hQ : IsPathFrom G Q z c₂)
    (hQF : ∀ v ∈ SPGT.interior Q, v ∈ SPGT.interior T)
    (hQiso : ∀ c ∈ C, ∀ v ∈ SPGT.interior Q, G.Adj c v → c = z ∨ c = c₂) :
    False := by
  exact Workspace.ProofLemmas.Thm232Final.closing G C Y ctx.hopt.1 ctx.hmin
    x₀ z x₁ c₁ c₂ c₃ k d ctx.hd2 ctx.hdn ctx.hpre1 ctx.hpre2
    ctx.h0Y ctx.hzY ctx.h1Y ctx.hc1Y ctx.hc2Y ctx.hc3Y ctx.hnb ctx.hnbc
    (horient.elim (fun h => Or.inl h.2.1) (fun h => Or.inr h.2.1))
    Q hQ (fun v hv => (ctx.hint v (hQF v hv)).1)
    (fun v hv => (ctx.hint v (hQF v hv)).2) hQiso

end Workspace.ProofLemmas.Thm232RemainingClaims
