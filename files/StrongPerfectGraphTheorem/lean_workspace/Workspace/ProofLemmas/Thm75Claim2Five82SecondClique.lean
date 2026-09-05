import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75Claim1
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.Thm75PrismThroughBranch
import Workspace.ProofLemmas.Thm75DominantOutsideLineGraph
import Workspace.ProofLemmas.Thm75DominanceTriangles
import Workspace.ProofLemmas.Thm75Endgame
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_8

/-!
# `Nc₂ \ {r₂} ⊆ X` in the `bᵢ = cᵢ` branch of 7.5 claim (2)

PAPER (proof of 7.5, claim (2), printed p. 38):

> *"We claim also that every vertex of `Nc₂ \ {r₂}` is in `X`.  For if not, then `r₂ ∈ X`, and
> by 7.1 there is a prism `Rc₁c₂, P₁, P₂` say, in `L(H)`, where each `Pᵢ` has an end
> `aᵢ ∈ Nc₁` and an end `bᵢ ∈ Nc₂`, and `b₂ ∉ X`.  (Consequently `r₂, b₁ ∈ X`.)  Hence at most
> one vertex of the triangle `{r′₂, b₁, b₂}` is in `X`, and some vertex in `X` (namely `a₁`)
> has no neighbour in this triangle, so by 2.8, `Y` cannot be linked onto this triangle.  In
> particular, no vertex of `P₂` is in `X` except `a₂`.  But then `a₂-P₂-b₂-r₂` is an odd path
> between members of `X`, and none of its internal vertices are in `X`, and `a₁` has no
> neighbour in its interior, contrary to 2.2.  This proves that every vertex of `Nc₂ \ {r₂}`
> is in `X`."*

The prism is produced by `Thm75PrismThroughBranch.thm75PrismThroughBranch`, which lets the
caller prescribe the two ends in the clique at the *first* named end of the branch.  The paper
prescribes the `Nc₂`-end `b₂`, so the prism lemma is applied to the reversed branch
`B.reverse`, whose named ends are `c₂, c₁`; this is why the local names below are the paper's
with `1` and `2` exchanged: `β₁, β₂ ∈ Nc₂` and `α₁, α₂ ∈ Nc₁`.

Instead of the printed *"at most one vertex of the triangle is in `X`"* count, the linkage is
refuted by lengths: the three linkage paths have lengths `k ≥ 1`, `0` and `pathLength P + 1 ≥ 2`,
and every alternative of 2.8 forces two of the three lengths to be `0`, or forces two of them to
be `0` and `1`.  This uses `p₁ ≠ p₂`, which the caller gets from the exclusion of case 3.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm75Claim2Five82SecondClique

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.TrackToRungPath

/-- Every vertex of a path with at least two vertices has a neighbour on the path. -/
theorem exists_adj_mem_of_mem {V : Type*} {G : SimpleGraph V} {p : List V}
    (h : IsPathList G p) (hlen : 2 ≤ p.length) {x : V} (hx : x ∈ p) :
    ∃ y ∈ p, G.Adj x y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rcases lt_or_ge (i + 1) p.length with hlt | hge
  · exact ⟨p[i + 1]'hlt, List.getElem_mem _, path_adj_succ h hlt⟩
  · have hi1 : 0 < i := by omega
    refine ⟨p[i - 1]'(by omega), List.getElem_mem _, ?_⟩
    have hh := path_adj_succ h (show (i - 1) + 1 < p.length by omega)
    have heq : p[(i - 1) + 1]'(show (i-1)+1 < p.length by omega) = p[i]'hi := by
      congr 1
      omega
    rw [heq] at hh
    exact hh.symm


/-- **Every vertex of `Nc₂ \ {r₂}` is in `X`** (printed p. 38), in the `bᵢ = cᵢ` case of
7.5 claim (2).  `hN₁X` is the `i = 1` half, which the caller gets from the minimality of `F`. -/
theorem secondCliqueComplete {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y)
    (X Rset F : Set V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hFX : ∀ x ∈ F, x ∉ X) (hFK : ∀ x ∈ F, x ∉ K)
    (r₁ r₂ p₁ p₂ : V) (P : List V)
    (hP : IsPathFrom G P p₁ p₂) (hPF : ∀ x ∈ P, x ∈ F) (hp₁₂ : p₁ ≠ p₂)
    (hr₁ : NSet G H K φ c₁ ∩ Rset = {r₁}) (hr₂ : NSet G H K φ c₂ ∩ Rset = {r₂})
    (h₁ : ∀ x ∈ NSet G H K φ c₁ \ {r₁}, G.Adj p₁ x)
    (h₂ : ∀ x ∈ NSet G H K φ c₂ \ {r₂}, G.Adj p₂ x)
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ y ∈ NSet G H K φ c₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ NSet G H K φ c₂ \ {r₂}) ∨
      (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂))
    (hN₁X : NSet G H K φ c₁ \ {r₁} ⊆ X) :
    NSet G H K φ c₂ \ {r₂} ⊆ X := by
  classical
  set N₁ := NSet G H K φ c₁ with hN₁def
  set N₂ := NSet G H K φ c₂ with hN₂def
  -- basic facts about the branch ends
  obtain ⟨hcne, hc₁b, hc₂b, hcnadj⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H happ.1.1 B c₁ c₂
      hbranch hfrom (by omega)
  have hdisj12 : ∀ x, x ∈ N₁ → x ∉ N₂ :=
    Thm75EndgameHelpers.nset_disjoint G K φ hcne hcnadj
  have hN₁K : N₁ ⊆ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₁
  have hN₂K : N₂ ⊆ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₂
  have hYK : ∀ y ∈ Y, y ∉ K := fun y hy =>
    Workspace.ProofLemmas.Thm75DominantOutsideLineGraph.thm75DominantOutsideLineGraph
      G J hJ H K φ happ B c₁ c₂ hbranch hfrom hlen y (hYdom y hy)
  have hclaim1 := Workspace.ProofLemmas.Thm75Claim1.thm75Claim1 G hG J hJ H K φ happ
    B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom
  have hsub2 : (N₂ \ X).Subsingleton := by rw [hX]; exact hclaim1.2
  have hr₂N : r₂ ∈ N₂ := by
    have : r₂ ∈ N₂ ∩ Rset := by rw [hr₂]; rfl
    exact this.1
  have hr₁N : r₁ ∈ N₁ := by
    have : r₁ ∈ N₁ ∩ Rset := by rw [hr₁]; rfl
    exact this.1
  -- the contradiction hypothesis
  rintro n₂ ⟨hn₂N, hn₂r⟩
  by_contra hn₂X
  have hn₂rne : n₂ ≠ r₂ := hn₂r
  have hr₂X : r₂ ∈ X := by
    by_contra hc
    exact hn₂rne (hsub2 ⟨hn₂N, hn₂X⟩ ⟨hr₂N, hc⟩)
  have huniq : ∀ z ∈ N₂, z ∉ X → z = n₂ := fun z hz hzX => hsub2 ⟨hz, hzX⟩ ⟨hn₂N, hn₂X⟩
  -- the reversed branch, so that the prism lemma prescribes the two `Nc₂`-ends
  have hbranchR : IsBranch H B.reverse :=
    Workspace.ProofLemmas.Thm57Claim2Structure.isBranch_reverse hbranch
  have hfromR : IsTrackFrom H B.reverse c₂ c₁ :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hfrom
  have htlR : trackLength B.reverse = trackLength B := by
    simp [trackLength]
  have hoddR : Odd (trackLength B.reverse) := by rw [htlR]; exact hodd
  have hlenR : 3 ≤ trackLength B.reverse := by rw [htlR]; exact hlen
  obtain ⟨ρ₂, ρ₁, hρ₂N, hρ₁N, hρ₂R, hρ₁R, hmain⟩ :=
    Workspace.ProofLemmas.Thm75PrismThroughBranch.thm75PrismThroughBranch G hG J hJ H K φ happ
      B.reverse c₂ c₁ hbranchR hfromR hoddR hlenR
  have hrungRset : ∀ x, x ∈ trackRung φ B.reverse hfromR.1 → x ∈ Rset := by
    intro x hx
    obtain ⟨e, he, heB, rfl⟩ :=
      (Workspace.ProofLemmas.ThreeTracksLineGraphPrism.mem_trackRung_iff φ hfromR.1).mp hx
    rw [hRset]
    exact ⟨e, he, by rwa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at heB,
      rfl⟩
  have hρ₂eq : ρ₂ = r₂ := by
    have : ρ₂ ∈ N₂ ∩ Rset := ⟨hρ₂N, hrungRset ρ₂ hρ₂R⟩
    rw [hr₂] at this; exact this
  have hρ₁eq : ρ₁ = r₁ := by
    have : ρ₁ ∈ N₁ ∩ Rset := ⟨hρ₁N, hrungRset ρ₁ hρ₁R⟩
    rw [hr₁] at this; exact this
  rw [hρ₂eq] at hρ₂N hρ₂R
  rw [hρ₁eq] at hρ₁N hρ₁R
  rw [hρ₂eq, hρ₁eq] at hmain
  -- a third vertex of `Nc₂`, distinct from `r₂` and from the missing vertex `n₂`
  have hN₂card : 3 ≤ N₂.ncard :=
    Thm75DominanceTriangles.three_le_nset_ncard G H K φ c₂ hc₂b
  obtain ⟨β₁, hβ₁⟩ : (N₂ \ ({r₂, n₂} : Set V)).Nonempty := by
    rw [Set.diff_nonempty]
    intro hsub
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hpair := Set.ncard_pair (show r₂ ≠ n₂ from fun h => hn₂rne h.symm)
    omega
  have hβ₁N : β₁ ∈ N₂ := hβ₁.1
  have hβ₁r : β₁ ≠ r₂ := fun h => hβ₁.2 (Or.inl h)
  have hβ₁n : β₁ ≠ n₂ := fun h => hβ₁.2 (Or.inr h)
  obtain ⟨α₁, α₂, Pr₁, Pr₂, Pr₃, hα₁N, hα₂N, hprism, hevA, hevB, hevC, hlA, hlB, hlC,
    hKA, hKB, hKC⟩ := hmain β₁ n₂ hβ₁N hn₂N hβ₁r hn₂rne hβ₁n
  obtain ⟨htriA, htriB, hAB, hpath1, hpath2, hpath3, e12, e13, e23⟩ := hprism
  have hp1 : IsPathFrom G Pr₁ β₁ α₁ := by simpa using hpath1
  have hp2 : IsPathFrom G Pr₂ n₂ α₂ := by simpa using hpath2
  have hp3 : IsPathFrom G Pr₃ r₂ r₁ := by simpa using hpath3
  have E12 : ∀ u ∈ Pr₁, ∀ v ∈ Pr₂,
      (G.Adj u v ↔ (u = β₁ ∧ v = n₂) ∨ (u = α₁ ∧ v = α₂)) := by simpa using e12
  have E13 : ∀ u ∈ Pr₁, ∀ v ∈ Pr₃,
      (G.Adj u v ↔ (u = β₁ ∧ v = r₂) ∨ (u = α₁ ∧ v = r₁)) := by simpa using e13
  have E23 : ∀ u ∈ Pr₂, ∀ v ∈ Pr₃,
      (G.Adj u v ↔ (u = n₂ ∧ v = r₂) ∨ (u = α₂ ∧ v = r₁)) := by simpa using e23
  have hα₁α₂ : α₁ ≠ α₂ := (show G.Adj α₁ α₂ by simpa using htriB 0 1 (by decide)).ne
  have hα₁r₁ : α₁ ≠ r₁ := (show G.Adj α₁ r₁ by simpa using htriB 0 2 (by decide)).ne
  have hα₂r₁ : α₂ ≠ r₁ := (show G.Adj α₂ r₁ by simpa using htriB 1 2 (by decide)).ne
  have hβ₁α₁ : β₁ ≠ α₁ := by simpa using hAB 0 0
  have hn₂α₁ : n₂ ≠ α₁ := by simpa using hAB 1 0
  have hn₂α₂ : n₂ ≠ α₂ := by simpa using hAB 1 1
  have hr₂α₂ : r₂ ≠ α₂ := by simpa using hAB 2 1
  have hr₂r₁ : r₂ ≠ r₁ := by simpa using hAB 2 2
  have hβ₁α₂ : β₁ ≠ α₂ := by simpa using hAB 0 1
  have hβ₁mem : β₁ ∈ Pr₁ := (isPathFrom_ends_mem hp1).1
  have hα₁mem : α₁ ∈ Pr₁ := (isPathFrom_ends_mem hp1).2
  have hn₂mem : n₂ ∈ Pr₂ := (isPathFrom_ends_mem hp2).1
  have hα₂mem : α₂ ∈ Pr₂ := (isPathFrom_ends_mem hp2).2
  have hr₂mem : r₂ ∈ Pr₃ := (isPathFrom_ends_mem hp3).1
  have hPr₁len : 2 ≤ Pr₁.length := by
    have := hlA; simp only [pathLength] at this; omega
  -- `Pr₂` meets the two cliques only in its two ends
  have hPr₂N₁ : ∀ u ∈ Pr₂, u ∈ N₁ → u = α₂ := by
    intro u hu huN
    by_cases hcase : u = α₁
    · exfalso
      subst hcase
      obtain ⟨y, hy, hadj⟩ := exists_adj_mem_of_mem hp1.1 hPr₁len hα₁mem
      have := (E12 y hy u hu).mp hadj.symm
      rcases this with ⟨-, h⟩ | ⟨-, h⟩
      · exact hn₂α₁ h.symm
      · exact hα₁α₂ h
    · have hadj : G.Adj α₁ u :=
        Thm75EndgameHelpers.nset_clique G H K φ c₁ α₁ hα₁N u huN (fun h => hcase h.symm)
      rcases (E12 α₁ hα₁mem u hu).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm hβ₁α₁
      · exact h
  have hPr₂N₂ : ∀ u ∈ Pr₂, u ∈ N₂ → u = n₂ := by
    intro u hu huN
    by_cases hcase : u = β₁
    · exfalso
      subst hcase
      obtain ⟨y, hy, hadj⟩ := exists_adj_mem_of_mem hp1.1 hPr₁len hβ₁mem
      have := (E12 y hy u hu).mp hadj.symm
      rcases this with ⟨-, h⟩ | ⟨-, h⟩
      · exact hβ₁n h
      · exact hβ₁α₂ h
    · have hadj : G.Adj β₁ u :=
        Thm75EndgameHelpers.nset_clique G H K φ c₂ β₁ hβ₁N u huN (fun h => hcase h.symm)
      rcases (E12 β₁ hβ₁mem u hu).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hβ₁α₁
  have hr₁nPr₂ : r₁ ∉ Pr₂ := fun h => hα₂r₁ (hPr₂N₁ r₁ h hr₁N).symm
  have hr₂nPr₂ : r₂ ∉ Pr₂ := fun h => hn₂rne (hPr₂N₂ r₂ h hr₂N).symm
  have hα₁adj : ∀ v ∈ Pr₂, (G.Adj α₁ v ↔ v = α₂) := by
    intro v hv
    rw [E12 α₁ hα₁mem v hv]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hβ₁α₁.symm
      · exact h
    · intro h; exact Or.inr ⟨rfl, h⟩
  -- membership in `X`
  have hα₁X : α₁ ∈ X := hN₁X ⟨hα₁N, hα₁r₁⟩
  have hα₂X : α₂ ∈ X := hN₁X ⟨hα₂N, hα₂r₁⟩
  have hβ₁X : β₁ ∈ X := by
    by_contra hc
    exact hβ₁n (huniq β₁ hβ₁N hc)
  -- indices along `Pr₂`
  have hLpos : 0 < Pr₂.length := path_length_pos hp2.1
  have hzero : Pr₂[0]'hLpos = n₂ := getElem_zero_of_head? hp2.2.1 hLpos
  have hlast : Pr₂[Pr₂.length - 1]'(by omega) = α₂ := getElem_last_of_getLast? hp2.2.2 hLpos
  have hLen3 : 3 ≤ Pr₂.length := by have := hlB; simp only [pathLength] at this; omega
  have hexdec : ∃ i, ∃ h : i < Pr₂.length, Pr₂[i]'h ∈ X :=
    ⟨Pr₂.length - 1, by omega, by rw [hlast]; exact hα₂X⟩
  obtain ⟨k, ⟨hkL, hkX⟩, hkmin⟩ :
      ∃ k, (∃ h : k < Pr₂.length, Pr₂[k]'h ∈ X) ∧
        ∀ i, i < k → ¬ ∃ h : i < Pr₂.length, Pr₂[i]'h ∈ X :=
    ⟨Nat.find hexdec, Nat.find_spec hexdec, fun i hi => Nat.find_min hexdec hi⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      apply hn₂X
      rw [← hzero]
      subst hk
      exact hkX
    · exact hk
  -- vertices of `Pr₂ ∪ {r₂}` are in `K`, hence outside `Y`
  have hQmem : ∀ w ∈ Pr₂.reverse ++ [r₂], w ∈ K := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hKB w (List.mem_reverse.mp h)
    · rw [List.mem_singleton] at h; exact h ▸ hN₂K hr₂N
  have hα₂r₂adj : ¬ G.Adj α₂ r₂ := by
    intro hadj
    rcases (E23 α₂ hα₂mem r₂ hr₂mem).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
    · exact hn₂α₂ h.symm
    · exact hr₂r₁ h
  rcases eq_or_lt_of_le (show k ≤ Pr₂.length - 1 by omega) with hkcase | hkcase
  · -- PAPER: *"no vertex of `P₂` is in `X` except `a₂`.  But then `a₂-P₂-b₂-r₂` is an odd path
    -- between members of `X` … contrary to 2.2."*
    have honly : ∀ u ∈ Pr₂, u ∈ X → u = α₂ := by
      intro u hu huX
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
      have hik : ¬ i < k := fun h => hkmin i h ⟨hi, huX⟩
      have heq : Pr₂[i]'hi = Pr₂[Pr₂.length - 1]'(by omega) := by
        congr 1
        omega
      rw [heq, hlast]
    have hQ : IsPathFrom G (Pr₂.reverse ++ [r₂]) α₂ r₂ := by
      refine Workspace.ProofLemmas.PathGlue.glue_path (isPathFrom_reverse hp2)
        ⟨isPathList_singleton G r₂, rfl, rfl⟩ ?_ ?_
      · intro x hx hx2
        rw [List.mem_singleton] at hx2
        exact hr₂nPr₂ (hx2 ▸ (List.mem_reverse.mp hx))
      · intro x hx y hy
        rw [List.mem_singleton] at hy
        subst hy
        rw [E23 x (List.mem_reverse.mp hx) y hr₂mem]
        constructor
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact ⟨h, rfl⟩
          · exact absurd h hr₂r₁
        · rintro ⟨h, -⟩; exact Or.inl ⟨h, rfl⟩
      
    have hQodd : Odd (pathLength (Pr₂.reverse ++ [r₂])) := by
      have hlenQ : pathLength (Pr₂.reverse ++ [r₂]) = Pr₂.length := by
        simp [pathLength]
      rw [hlenQ, Nat.odd_iff]
      have hev := hevB
      rw [Nat.even_iff] at hev
      simp only [pathLength] at hev
      omega
    have hnotY : ∀ w ∈ Pr₂.reverse ++ [r₂], w ∉ Y := fun w hw hwY => hYK w hwY (hQmem w hw)
    have hXQ : ∀ w ∈ Pr₂.reverse ++ [r₂], w ∈ X → (w = α₂ ∨ w = r₂) := by
      intro w hw hwX
      rcases List.mem_append.mp hw with h | h
      · exact Or.inl (honly w (List.mem_reverse.mp h) hwX)
      · rw [List.mem_singleton] at h; exact Or.inr h
    have hnoedge : ¬ ∃ u ∈ Pr₂.reverse ++ [r₂], ∃ v ∈ Pr₂.reverse ++ [r₂],
        EdgeComplete G Y u v := by
      rintro ⟨u, hu, v, hv, hadj, huc, hvc⟩
      have huX : u ∈ X := by rw [hX]; exact huc
      have hvX : v ∈ X := by rw [hX]; exact hvc
      rcases hXQ u hu huX with rfl | rfl <;> rcases hXQ v hv hvX with rfl | rfl
      · exact G.irrefl hadj
      · exact hα₂r₂adj hadj
      · exact hα₂r₂adj hadj.symm
      · exact G.irrefl hadj
    have hα₂c : VertexComplete G α₂ Y := by rw [hX] at hα₂X; exact hα₂X
    have hr₂c : VertexComplete G r₂ Y := by rw [hX] at hr₂X; exact hr₂X
    have hα₁c : VertexComplete G α₁ Y := by rw [hX] at hα₁X; exact hα₁X
    obtain ⟨u, huint, hadj⟩ :=
      Workspace.Statements.S02.SPGT.thm_2_2 G hG Y hYanti (Pr₂.reverse ++ [r₂]) α₂ r₂ hQ
        hnotY hQodd hα₂c hr₂c hnoedge α₁ hα₁c
    rw [mem_interior_iff_of_pathFrom hQ] at huint
    obtain ⟨huQ, huα₂, hur₂⟩ := huint
    have huPr₂ : u ∈ Pr₂ := by
      rcases List.mem_append.mp huQ with h | h
      · exact List.mem_reverse.mp h
      · rw [List.mem_singleton] at h; exact absurd h hur₂
    exact huα₂ ((hα₁adj u huPr₂).mp hadj)
  · -- PAPER: *"Hence at most one vertex of the triangle `{r′₂, b₁, b₂}` is in `X` … so by 2.8,
    -- `Y` cannot be linked onto this triangle."*  The triangle is `{p₂, β₁, n₂}`.
    have hβ₁nPr₂ : β₁ ∉ Pr₂ := fun h => hβ₁n (hPr₂N₂ β₁ h hβ₁N)
    have hα₁nPr₂ : α₁ ∉ Pr₂ := fun h => hα₁α₂ (hPr₂N₁ α₁ h hα₁N)
    have hS1sub : ∀ x ∈ (Pr₂.drop 0).take (k - 0 + 1), x ∈ Pr₂ := by
      intro x hx
      rw [mem_slice_iff Pr₂ (Nat.zero_le k) hkL] at hx
      obtain ⟨i, hi, -, -, rfl⟩ := hx
      exact List.getElem_mem _
    have hS1neα₂ : ∀ x ∈ (Pr₂.drop 0).take (k - 0 + 1), x ≠ α₂ := by
      intro x hx
      rw [mem_slice_iff Pr₂ (Nat.zero_le k) hkL] at hx
      obtain ⟨i, hi, -, hik, rfl⟩ := hx
      rw [← hlast]
      exact path_ne_of_ne_index hp2.1 hi (by omega) (by omega)
    have hn₂S1 : n₂ ∈ (Pr₂.drop 0).take (k - 0 + 1) := by
      rw [mem_slice_iff Pr₂ (Nat.zero_le k) hkL]
      exact ⟨0, hLpos, Nat.le_refl 0, Nat.zero_le k, hzero⟩
    have hwS1 : (Pr₂[k]'hkL) ∈ (Pr₂.drop 0).take (k - 0 + 1) := by
      rw [mem_slice_iff Pr₂ (Nat.zero_le k) hkL]
      exact ⟨k, hkL, Nat.zero_le k, Nat.le_refl k, rfl⟩
    have hS1path : IsPathFrom G ((Pr₂.drop 0).take (k - 0 + 1)) n₂ (Pr₂[k]'hkL) := by
      refine ⟨isPathList_slice hp2.1 hk0 hkL, ?_, getLast?_slice Pr₂ (le_of_lt hk0) hkL⟩
      rw [head?_slice Pr₂ (le_of_lt hk0) hkL]
      exact congrArg some hzero
    -- the third linkage path leaves `p₂` along `P` and ends at `α₁ ∈ X`
    have hα₁nP : α₁ ∉ P := fun h => hFK α₁ (hPF α₁ h) (hN₁K hα₁N)
    have hp₁α₁ : G.Adj p₁ α₁ := h₁ α₁ ⟨hα₁N, hα₁r₁⟩
    have hcrossP : ∀ x ∈ P.reverse, ∀ y ∈ ([α₁] : List V),
        (G.Adj x y ↔ (x = p₁ ∧ y = α₁)) := by
      intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rw [List.mem_reverse] at hx
      constructor
      · intro hadj
        refine ⟨?_, rfl⟩
        rcases hno x hx y (hN₁K hα₁N) hadj with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact absurd h.1 (hdisj12 y hα₁N)
        · exact h
        · exact absurd (h ▸ hr₂N) (hdisj12 y hα₁N)
      · rintro ⟨rfl, -⟩
        exact hp₁α₁
    have hP₃path : IsPathFrom G (P.reverse ++ [α₁]) p₂ α₁ := by
      refine Workspace.ProofLemmas.PathGlue.glue_path (isPathFrom_reverse hP)
        ⟨isPathList_singleton G α₁, rfl, rfl⟩ ?_ hcrossP
      intro x hx hx2
      rw [List.mem_singleton] at hx2
      rw [List.mem_reverse] at hx
      exact hα₁nP (hx2 ▸ hx)
    have hP₃mem : ∀ y ∈ P.reverse ++ [α₁], y ∈ P ∨ y = α₁ := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact Or.inl (List.mem_reverse.mp h)
      · exact Or.inr (List.mem_singleton.mp h)
    have hp₂P₃ : p₂ ∈ P.reverse ++ [α₁] := (isPathFrom_ends_mem hP₃path).1
    have hα₁P₃ : α₁ ∈ P.reverse ++ [α₁] := (isPathFrom_ends_mem hP₃path).2
    have hα₁p₂ : α₁ ≠ p₂ := fun h => hFK p₂ (hPF p₂ (isPathFrom_ends_mem hP).2) (h ▸ hN₁K hα₁N)
    -- the three edge conditions of the linkage
    have c12 : ∀ x ∈ (Pr₂.drop 0).take (k - 0 + 1), ∀ y ∈ ([β₁] : List V),
        (G.Adj x y ↔ (x = n₂ ∧ y = β₁)) := by
      intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rw [SimpleGraph.adj_comm, E12 y hβ₁mem x (hS1sub x hx)]
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact ⟨h, rfl⟩
        · exact absurd h hβ₁α₁
      · rintro ⟨h, -⟩; exact Or.inl ⟨rfl, h⟩
    have c13 : ∀ x ∈ (Pr₂.drop 0).take (k - 0 + 1), ∀ y ∈ P.reverse ++ [α₁],
        (G.Adj x y ↔ (x = n₂ ∧ y = p₂)) := by
      intro x hx y hy
      have hxPr₂ := hS1sub x hx
      have hxK : x ∈ K := hKB x hxPr₂
      rcases hP₃mem y hy with hyP | rfl
      · constructor
        · intro hadj
          rcases hno y hyP x hxK hadj.symm with ⟨-, h⟩ | ⟨h, h'⟩ | ⟨-, h⟩ | ⟨-, h⟩
          · exact absurd (hPr₂N₁ x hxPr₂ h.1) (hS1neα₂ x hx)
          · exact ⟨hPr₂N₂ x hxPr₂ h'.1, h⟩
          · exact absurd (h ▸ hxPr₂) hr₁nPr₂
          · exact absurd (h ▸ hxPr₂) hr₂nPr₂
        · rintro ⟨rfl, rfl⟩
          exact (h₂ x ⟨hn₂N, hn₂r⟩).symm
      · constructor
        · intro hadj
          exact absurd ((hα₁adj x hxPr₂).mp hadj.symm) (hS1neα₂ x hx)
        · rintro ⟨-, h⟩; exact absurd h hα₁p₂
    have c23 : ∀ x ∈ ([β₁] : List V), ∀ y ∈ P.reverse ++ [α₁],
        (G.Adj x y ↔ (x = β₁ ∧ y = p₂)) := by
      intro x hx y hy
      rw [List.mem_singleton] at hx
      subst hx
      rcases hP₃mem y hy with hyP | rfl
      · constructor
        · intro hadj
          refine ⟨rfl, ?_⟩
          rcases hno y hyP x (hN₂K hβ₁N) hadj.symm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
          · exact absurd h.1 (fun hh => hdisj12 x hh hβ₁N)
          · exact h
          · exact absurd (h ▸ hr₁N) (fun hh => hdisj12 x hh hβ₁N)
          · exact absurd h hβ₁r
        · rintro ⟨-, rfl⟩
          exact (h₂ x ⟨hβ₁N, hβ₁r⟩).symm
      · constructor
        · intro hadj
          exfalso
          have hends : ¬ G.Adj (Pr₁[0]'(by omega)) (Pr₁[Pr₁.length - 1]'(by omega)) :=
            path_ends_not_adj hp1.1 (by have := hlA; simp only [pathLength] at this; omega)
          apply hends
          rw [getElem_zero_of_head? hp1.2.1 (by omega),
            getElem_last_of_getLast? hp1.2.2 (by omega)]
          exact hadj
        · rintro ⟨-, h⟩; exact absurd h hα₁p₂
    have hβ₁c : VertexComplete G β₁ Y := by rw [hX] at hβ₁X; exact hβ₁X
    have hα₁c : VertexComplete G α₁ Y := by rw [hX] at hα₁X; exact hα₁X
    have hwc : VertexComplete G (Pr₂[k]'hkL) Y := by rw [hX] at hkX; exact hkX
    have hu₁ : ∀ v ∈ (Pr₂.drop 0).take (k - 0 + 1),
        (VertexComplete G v Y ↔ v = Pr₂[k]'hkL) := by
      intro v hv
      constructor
      · intro hvc
        have hvX : v ∈ X := by rw [hX]; exact hvc
        rw [mem_slice_iff Pr₂ (Nat.zero_le k) hkL] at hv
        obtain ⟨i, hi, -, hik, rfl⟩ := hv
        have hnlt : ¬ i < k := fun h => hkmin i h ⟨hi, hvX⟩
        congr 1
        omega
      · rintro rfl; exact hwc
    have hu₂ : ∀ v ∈ ([β₁] : List V), (VertexComplete G v Y ↔ v = β₁) := by
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨fun _ => rfl, fun _ => hβ₁c⟩
    have hu₃ : ∀ v ∈ P.reverse ++ [α₁], (VertexComplete G v Y ↔ v = α₁) := by
      intro v hv
      rcases hP₃mem v hv with hvP | rfl
      · constructor
        · intro hvc
          exact absurd (show v ∈ X by rw [hX]; exact hvc) (hFX v (hPF v hvP))
        · rintro rfl; exact absurd (hPF v hvP) (fun hh => hFK v hh (hN₁K hα₁N))
      · exact ⟨fun _ => rfl, fun _ => hα₁c⟩
    have hlink : SetLinkedOntoTriangle G Y n₂ β₁ p₂
        ((Pr₂.drop 0).take (k - 0 + 1)) [β₁] (P.reverse ++ [α₁]) := by
      refine ⟨⟨hS1path.1, isPathList_singleton G β₁, hP₃path.1⟩, ⟨?_, ?_, ?_⟩,
        ⟨Or.inl hS1path.2.1, Or.inl rfl, Or.inl hP₃path.2.1⟩, ⟨c12, c13, c23⟩,
        ⟨Pr₂[k]'hkL, hwS1, hwc⟩, ⟨β₁, List.mem_singleton_self β₁, hβ₁c⟩,
        ⟨α₁, hα₁P₃, hα₁c⟩⟩
      · intro x hx hx2
        rw [List.mem_singleton] at hx2
        exact hβ₁nPr₂ (hx2 ▸ hS1sub x hx)
      · intro x hx hx2
        rcases hP₃mem x hx2 with hxP | rfl
        · exact hFK x (hPF x hxP) (hKB x (hS1sub x hx))
        · exact hα₁nPr₂ (hS1sub x hx)
      · intro x hx hx2
        rw [List.mem_singleton] at hx
        subst hx
        rcases hP₃mem x hx2 with hxP | rfl
        · exact hFK x (hPF x hxP) (hN₂K hβ₁N)
        · exact hβ₁α₁ rfl
    have hconc := Workspace.Statements.S02.SPGT.thm_2_8 G hG Y hYanti n₂ β₁ p₂
      (Pr₂[k]'hkL) β₁ α₁ ((Pr₂.drop 0).take (k - 0 + 1)) [β₁] (P.reverse ++ [α₁])
      hlink hS1path ⟨isPathList_singleton G β₁, rfl, rfl⟩ hP₃path hu₁ hu₂ hu₃
    have hPlen : 2 ≤ P.length := by
      by_contra hc
      have h1 : P.length = 1 := by have := path_length_pos hP.1; omega
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
      rw [ha] at hP
      have e1 : a = p₁ := by simpa using hP.2.1
      have e2 : a = p₂ := by simpa using hP.2.2
      exact hp₁₂ (e1.symm.trans e2)
    have hA : pathLength ((Pr₂.drop 0).take (k - 0 + 1)) = k := by
      simp only [pathLength, length_slice Pr₂ (Nat.zero_le k) hkL]
      omega
    have hC : 2 ≤ pathLength (P.reverse ++ [α₁]) := by
      simp only [pathLength, List.length_append, List.length_reverse, List.length_singleton]
      omega
    have hB : pathLength ([β₁] : List V) = 0 := rfl
    rcases hconc with (⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩) |
      (⟨q1, q2, q3, -⟩ | ⟨q1, q2, q3, -⟩ | ⟨q1, q2, q3, -⟩) <;> omega




end Workspace.ProofLemmas.Thm75Claim2Five82SecondClique
