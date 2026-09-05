import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75Endgame
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.Thm75PrismThroughBranch
import Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism

/-!
# The matched prisms of case 1 of 5.8.2, when the replaced branch is the distinguished one

PAPER (proof of 7.5, claim (2), printed p. 37): *"There also correspond three tracks in `H′`,
yielding a prism in `L(H′)` … these two prisms are related as in 7.4."*

In this case the replacement removes the rung end `r₁` from the clique at `c₁` and inserts the
first vertex `p₁` of the replacement path `R′`.  The two prisms are obtained from a **single**
application of 7.1 to the old appearance: 7.1 gives, for any two distinct
`x, z ∈ Nc₁ \ {r₁}`, a prism whose three paths are the distinguished rung `Rc₁c₂` (from `r₁` to
`r₂`) and two paths `P₁` from `x` and `P₂` from `z`.  Replacing the first of those three paths
by `R′` gives a second prism with the *same* other two paths and the *same* opposite triangle,
because the boundary condition on `R′` says exactly that `R′` attaches to the rest of the
appearance only at `p₁` (into `Nc₁ \ {r₁}`) and at `r₂` (into `Nc₂ \ {r₂}`).

The only work is checking that `P₁` and `P₂` avoid the old rung, so that the boundary condition
applies to their vertices.  That is proved here from the prism itself: `r₁` and `r₂` are not on
`P₁` or `P₂`, and a vertex of `P₁` next to a rung vertex would have to be one of those two.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82CaseGapPrism

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism

variable {V : Type*}

/-- **Neither end of one prism path lies on another prism path.**

If the only edges between `P` and `Rg` are `u₀v₀` and `u₁v₁`, and `Rg` is a path from `v₀` to
`v₁` with at least three vertices, then `v₀ ∉ P` and `v₁ ∉ P`: the vertex of `Rg` next to `v₀`
would give a second edge out of `v₀` into `Rg`. -/
theorem ends_notMem_of_cross {G : SimpleGraph V} {P Rg : List V} {u₀ u₁ v₀ v₁ : V}
    (hRg : IsPathFrom G Rg v₀ v₁) (h3 : 3 ≤ Rg.length)
    (e : ∀ u ∈ P, ∀ v ∈ Rg, (G.Adj u v ↔ (u = u₀ ∧ v = v₀) ∨ (u = u₁ ∧ v = v₁)))
    (h00 : v₀ ≠ u₀) (h01 : v₀ ≠ u₁) (h10 : v₁ ≠ u₀) (h11 : v₁ ≠ u₁) :
    v₀ ∉ P ∧ v₁ ∉ P := by
  have hz : Rg[0]'(by omega) = v₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hRg.2.1 (by omega)
  have hl : Rg[Rg.length - 1]'(by omega) = v₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hRg.2.2 (by omega)
  constructor
  · intro hmem
    have hadj : G.Adj (Rg[0]'(by omega)) (Rg[1]'(by omega)) :=
      Workspace.ProofLemmas.PathBasics.path_adj_succ hRg.1 (by omega)
    rw [hz] at hadj
    rcases (e v₀ hmem (Rg[1]'(by omega)) (List.getElem_mem _)).mp hadj with ⟨h, -⟩ | ⟨h, -⟩
    · exact h00 h
    · exact h01 h
  · intro hmem
    have hadj : G.Adj (Rg[Rg.length - 2]'(by omega)) (Rg[Rg.length - 2 + 1]'(by omega)) :=
      Workspace.ProofLemmas.PathBasics.path_adj_succ hRg.1 (by omega)
    have heq : Rg[Rg.length - 2 + 1]'(by omega) = Rg[Rg.length - 1]'(by omega) := by
      congr 1
      omega
    rw [heq, hl] at hadj
    rcases (e v₁ hmem (Rg[Rg.length - 2]'(by omega)) (List.getElem_mem _)).mp hadj.symm with
      ⟨h, -⟩ | ⟨h, -⟩
    · exact h10 h
    · exact h11 h

/-- A path all of whose vertices stay out of `S` once its first vertex does and the property
propagates along the path. -/
theorem path_avoid_of_head_avoid {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    (S : Set V) (hhead : ∀ h : 0 < P.length, (P[0]'h) ∉ S)
    (hstep : ∀ (i : ℕ) (h : i + 1 < P.length),
      (P[i]'(Nat.lt_of_succ_lt h)) ∉ S → (P[i + 1]'h) ∉ S) :
    ∀ v ∈ P, v ∉ S := by
  have key : ∀ i, ∀ h : i < P.length, (P[i]'h) ∉ S := by
    intro i
    induction i with
    | zero => intro h; exact hhead h
    | succ n ih => intro h; exact hstep n h (ih (by omega))
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  exact key i hi


/-- **The two matched prisms of case 1.**

For distinct `x, z` in `Nc₁ \ {r₁}` this produces one opposite triangle `{r₂, β₁, β₂} ⊆ Nc₂`
and two paths `P₁, P₂` that serve **both** prisms: `Rc₁c₂, P₁, P₂` is a prism with triangle
`{r₁, x, z}`, and `R′, P₁, P₂` is a prism with triangle `{p₁, x, z}`. -/
theorem swap_prism_pair {U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (r₁ r₂ p₁ : V)
    (hr₁ : NSet G H K φ c₁ ∩ {x : V | x ∈ trackRung φ B hbranch.1} = {r₁})
    (hr₂ : NSet G H K φ c₂ ∩ {x : V | x ∈ trackRung φ B hbranch.1} = {r₂})
    (hp₁K : p₁ ∉ K)
    (R' : List V) (hR' : IsPathFrom G R' p₁ r₂)
    (hboundary : ∀ x ∈ R', ∀ y ∈ K, y ∉ trackRung φ B hbranch.1 →
      (G.Adj x y ↔ (x = p₁ ∧ y ∈ NSet G H K φ c₁ \ {r₁}) ∨
        (x = r₂ ∧ y ∈ NSet G H K φ c₂ \ {r₂})))
    (x z : V) (hx : x ∈ NSet G H K φ c₁ \ {r₁}) (hz : z ∈ NSet G H K φ c₁ \ {r₁})
    (hxz : x ≠ z) :
    ∃ (bb : Fin 3 → V) (Rg P₁ P₂ : List V),
      bb 0 = r₂ ∧ bb 1 ∈ NSet G H K φ c₂ ∧ bb 2 ∈ NSet G H K φ c₂ ∧
      bb 0 ≠ bb 1 ∧ bb 0 ≠ bb 2 ∧ bb 1 ≠ bb 2 ∧
      FormPrism G ![r₁, x, z] bb Rg P₁ P₂ ∧
      Even (pathLength Rg) ∧ Even (pathLength P₁) ∧ Even (pathLength P₂) ∧
      2 ≤ pathLength Rg ∧ 2 ≤ pathLength P₁ ∧ 2 ≤ pathLength P₂ ∧
      IsPathFrom G Rg r₁ r₂ ∧
      FormPrism G ![p₁, x, z] bb R' P₁ P₂ := by
  classical
  have hBtwo : 2 ≤ B.length := by simp only [trackLength] at hlen; omega
  -- the canonical rung and the identification of its two ends
  have hfirst : firstRungVertex φ B hbranch.1 hBtwo = r₁ := by
    have hmem : firstRungVertex φ B hbranch.1 hBtwo ∈
        NSet G H K φ c₁ ∩ {v : V | v ∈ trackRung φ B hbranch.1} :=
      ⟨⟨firstTrackEdge B hBtwo, firstTrackEdge_mem hbranch.1 hBtwo,
          ⟨firstTrackEdge_mem hbranch.1 hBtwo, firstTrackEdge_contains hfrom hBtwo⟩, rfl⟩,
        firstRungVertex_mem φ hbranch.1 hBtwo⟩
    rw [hr₁] at hmem
    exact hmem
  have hlast : lastRungVertex φ B hbranch.1 hBtwo = r₂ := by
    have hmem : lastRungVertex φ B hbranch.1 hBtwo ∈
        NSet G H K φ c₂ ∩ {v : V | v ∈ trackRung φ B hbranch.1} :=
      ⟨⟨lastTrackEdge B hBtwo, lastTrackEdge_mem hbranch.1 hBtwo,
          ⟨lastTrackEdge_mem hbranch.1 hBtwo, lastTrackEdge_contains hfrom hBtwo⟩, rfl⟩,
        lastRungVertex_mem φ hbranch.1 hBtwo⟩
    rw [hr₂] at hmem
    exact hmem
  -- a vertex of `Nc₁` other than `r₁` is off the rung
  have hoffQ : ∀ v : V, v ∈ NSet G H K φ c₁ → v ≠ r₁ → v ∉ trackRung φ B hbranch.1 := by
    intro v hv hvr hvQ
    have : v ∈ NSet G H K φ c₁ ∩ {w : V | w ∈ trackRung φ B hbranch.1} := ⟨hv, hvQ⟩
    rw [hr₁] at this
    exact hvr this
  have hxQ : x ∉ trackRung φ B hbranch.1 := hoffQ x hx.1 hx.2
  have hzQ : z ∉ trackRung φ B hbranch.1 := hoffQ z hz.1 hz.2
  have hxK : x ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₁ hx.1
  have hzK : z ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₁ hz.1
  have hr₁N : r₁ ∈ NSet G H K φ c₁ := by
    have : r₁ ∈ NSet G H K φ c₁ ∩ {v : V | v ∈ trackRung φ B hbranch.1} := by rw [hr₁]; rfl
    exact this.1
  have hr₂N : r₂ ∈ NSet G H K φ c₂ := by
    have : r₂ ∈ NSet G H K φ c₂ ∩ {v : V | v ∈ trackRung φ B hbranch.1} := by rw [hr₂]; rfl
    exact this.1
  -- 7.1 through the distinguished branch
  obtain ⟨ρ₁, ρ₂, hρ₁N, hρ₂N, hρ₁Q, hρ₂Q, hmain⟩ :=
    Workspace.ProofLemmas.Thm75PrismThroughBranch.thm75PrismThroughBranch
      G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen
  have hρ₁ : ρ₁ = r₁ := by
    have hm : ρ₁ ∈ NSet G H K φ c₁ ∩ {v : V | v ∈ trackRung φ B hbranch.1} := ⟨hρ₁N, hρ₁Q⟩
    rw [hr₁] at hm
    exact hm
  have hρ₂ : ρ₂ = r₂ := by
    have hm : ρ₂ ∈ NSet G H K φ c₂ ∩ {v : V | v ∈ trackRung φ B hbranch.1} := ⟨hρ₂N, hρ₂Q⟩
    rw [hr₂] at hm
    exact hm
  rw [hρ₁] at hmain
  rw [hρ₂] at hmain
  obtain ⟨β₁, β₂, P₁, P₂, Rg, hβ₁N, hβ₂N, hprism, hev1, hev2, hev3, hl1, hl2, hl3,
    hK1, hK2, hK3⟩ := hmain x z hx.1 hz.1 hx.2 hz.2 hxz
  obtain ⟨hA, hBt, hAB, hq1, hq2, hq3, e12, e13, e23⟩ := hprism
  -- unpack the `Fin 3`-indexed data
  have axz : G.Adj x z := by simpa using hA 0 1 (by decide)
  have axr : G.Adj x r₁ := by simpa using hA 0 2 (by decide)
  have azr : G.Adj z r₁ := by simpa using hA 1 2 (by decide)
  have bβ : G.Adj β₁ β₂ := by simpa using hBt 0 1 (by decide)
  have bβ₁r : G.Adj β₁ r₂ := by simpa using hBt 0 2 (by decide)
  have bβ₂r : G.Adj β₂ r₂ := by simpa using hBt 1 2 (by decide)
  have nxβ₁ : x ≠ β₁ := by simpa using hAB 0 0
  have nxβ₂ : x ≠ β₂ := by simpa using hAB 0 1
  have nxr₂ : x ≠ r₂ := by simpa using hAB 0 2
  have nzβ₁ : z ≠ β₁ := by simpa using hAB 1 0
  have nzβ₂ : z ≠ β₂ := by simpa using hAB 1 1
  have nzr₂ : z ≠ r₂ := by simpa using hAB 1 2
  have nr₁β₁ : r₁ ≠ β₁ := by simpa using hAB 2 0
  have nr₁β₂ : r₁ ≠ β₂ := by simpa using hAB 2 1
  have nr₁r₂ : r₁ ≠ r₂ := by simpa using hAB 2 2
  have hp1 : IsPathFrom G P₁ x β₁ := by simpa using hq1
  have hp2 : IsPathFrom G P₂ z β₂ := by simpa using hq2
  have hp3 : IsPathFrom G Rg r₁ r₂ := by simpa using hq3
  have E12 : ∀ u ∈ P₁, ∀ v ∈ P₂, (G.Adj u v ↔ (u = x ∧ v = z) ∨ (u = β₁ ∧ v = β₂)) := by
    simpa using e12
  have E13 : ∀ u ∈ P₁, ∀ v ∈ Rg, (G.Adj u v ↔ (u = x ∧ v = r₁) ∨ (u = β₁ ∧ v = r₂)) := by
    simpa using e13
  have E23 : ∀ u ∈ P₂, ∀ v ∈ Rg, (G.Adj u v ↔ (u = z ∧ v = r₁) ∨ (u = β₂ ∧ v = r₂)) := by
    simpa using e23
  have hRg3 : 3 ≤ Rg.length := by
    have := hl3
    simp only [pathLength] at this
    omega
  -- the ends of the rung are on neither of the other two paths
  obtain ⟨hr₁P₁, hr₂P₁⟩ :=
    ends_notMem_of_cross hp3 hRg3 E13 axr.ne' nr₁β₁ (Ne.symm nxr₂) (Ne.symm bβ₁r.ne)
  obtain ⟨hr₁P₂, hr₂P₂⟩ :=
    ends_notMem_of_cross hp3 hRg3 E23 azr.ne' nr₁β₂ (Ne.symm nzr₂) (Ne.symm bβ₂r.ne)
  -- neither of the other two paths meets the rung at all
  have hstep : ∀ (P : List V), IsPathList G P → (∀ v ∈ P, v ∈ K) →
      r₁ ∉ P → r₂ ∉ P →
      ∀ (i : ℕ) (h : i + 1 < P.length),
        (P[i]'(Nat.lt_of_succ_lt h)) ∉ {w : V | w ∈ trackRung φ B hbranch.1} →
        (P[i + 1]'h) ∉ {w : V | w ∈ trackRung φ B hbranch.1} := by
    intro P hP hPK hr₁P hr₂P i h hi hmem
    have hadj : G.Adj (P[i]'(Nat.lt_of_succ_lt h)) (P[i + 1]'h) :=
      Workspace.ProofLemmas.PathBasics.path_adj_succ hP h
    have hb := Workspace.ProofLemmas.Thm75Claim2Five82RungBoundary.rung_boundary
      φ hbranch hfrom hBtwo (x := P[i + 1]'h) (y := P[i]'(Nat.lt_of_succ_lt h))
      hmem (hPK _ (List.getElem_mem _)) hi
    rw [hfirst, hlast] at hb
    rcases hb.mp hadj.symm with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hr₁P (h1 ▸ List.getElem_mem _)
    · exact hr₂P (h1 ▸ List.getElem_mem _)
  have hP₁avoid : ∀ v ∈ P₁, v ∉ {w : V | w ∈ trackRung φ B hbranch.1} := by
    refine path_avoid_of_head_avoid hp1.1 _ ?_ (hstep P₁ hp1.1 hK1 hr₁P₁ hr₂P₁)
    intro h
    rw [Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp1.2.1 h]
    exact hxQ
  have hP₂avoid : ∀ v ∈ P₂, v ∉ {w : V | w ∈ trackRung φ B hbranch.1} := by
    refine path_avoid_of_head_avoid hp2.1 _ ?_ (hstep P₂ hp2.1 hK2 hr₁P₂ hr₂P₂)
    intro h
    rw [Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp2.2.1 h]
    exact hzQ
  -- `P₁` meets `Nc₁` only at `x` and `Nc₂` only at `β₁`; same for `P₂` with `z, β₂`
  have hr₁Rg : r₁ ∈ Rg := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hp3).1
  have hr₂Rg : r₂ ∈ Rg := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hp3).2
  have hP₁N₁ : ∀ v ∈ P₁, v ∈ NSet G H K φ c₁ \ {r₁} ↔ v = x := by
    intro v hv
    constructor
    · rintro ⟨hvN, hvr⟩
      have hadj : G.Adj v r₁ :=
        Thm75EndgameHelpers.nset_clique G H K φ c₁ v hvN r₁ hr₁N hvr
      rcases (E13 v hv r₁ hr₁Rg).mp hadj with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 nr₁r₂
    · rintro rfl; exact hx
  have hP₁N₂ : ∀ v ∈ P₁, v ∈ NSet G H K φ c₂ \ {r₂} ↔ v = β₁ := by
    intro v hv
    constructor
    · rintro ⟨hvN, hvr⟩
      have hadj : G.Adj v r₂ :=
        Thm75EndgameHelpers.nset_clique G H K φ c₂ v hvN r₂ hr₂N hvr
      rcases (E13 v hv r₂ hr₂Rg).mp hadj with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact absurd h1.symm nr₁r₂
      · exact h2
    · rintro rfl; exact ⟨hβ₁N, bβ₁r.ne⟩
  have hP₂N₁ : ∀ v ∈ P₂, v ∈ NSet G H K φ c₁ \ {r₁} ↔ v = z := by
    intro v hv
    constructor
    · rintro ⟨hvN, hvr⟩
      have hadj : G.Adj v r₁ :=
        Thm75EndgameHelpers.nset_clique G H K φ c₁ v hvN r₁ hr₁N hvr
      rcases (E23 v hv r₁ hr₁Rg).mp hadj with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 nr₁r₂
    · rintro rfl; exact hz
  have hP₂N₂ : ∀ v ∈ P₂, v ∈ NSet G H K φ c₂ \ {r₂} ↔ v = β₂ := by
    intro v hv
    constructor
    · rintro ⟨hvN, hvr⟩
      have hadj : G.Adj v r₂ :=
        Thm75EndgameHelpers.nset_clique G H K φ c₂ v hvN r₂ hr₂N hvr
      rcases (E23 v hv r₂ hr₂Rg).mp hadj with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact absurd h1.symm nr₁r₂
      · exact h2
    · rintro rfl; exact ⟨hβ₂N, bβ₂r.ne⟩
  -- the new attachments of `R'`
  have hp₁R' : p₁ ∈ R' := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR').1
  have hp₁x : G.Adj p₁ x := (hboundary p₁ hp₁R' x hxK hxQ).mpr (Or.inl ⟨rfl, hx⟩)
  have hp₁z : G.Adj p₁ z := (hboundary p₁ hp₁R' z hzK hzQ).mpr (Or.inl ⟨rfl, hz⟩)
  have hp₁ne : ∀ w : V, w ∈ K → p₁ ≠ w := fun w hw h => hp₁K (h ▸ hw)
  have hβ₁K : β₁ ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₂ hβ₁N
  have hβ₂K : β₂ ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₂ hβ₂N
  have hr₂K : r₂ ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₂ hr₂N
  refine ⟨![r₂, β₁, β₂], Rg, P₁, P₂, rfl, hβ₁N, hβ₂N, ?_, ?_, ?_, ?_, hev3, hev1, hev2,
    hl3, hl1, hl2, hp3, ?_⟩
  · simpa using bβ₁r.symm.ne
  · simpa using bβ₂r.symm.ne
  · simpa using bβ.ne
  · exact Workspace.ProofLemmas.PrismBasics.formPrism_of_data
      axr.symm azr.symm axz bβ₁r.symm bβ₂r.symm bβ
      nr₁r₂ nr₁β₁ nr₁β₂ nxr₂ nxβ₁ nxβ₂ nzr₂ nzβ₁ nzβ₂ hp3 hp1 hp2
      (fun u hu v hv => by
        rw [SimpleGraph.adj_comm, E13 v hv u hu]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h2, h1⟩
          · exact Or.inr ⟨h2, h1⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h2, h1⟩
          · exact Or.inr ⟨h2, h1⟩)
      (fun u hu v hv => by
        rw [SimpleGraph.adj_comm, E23 v hv u hu]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h2, h1⟩
          · exact Or.inr ⟨h2, h1⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h2, h1⟩
          · exact Or.inr ⟨h2, h1⟩)
      E12
  · refine Workspace.ProofLemmas.PrismBasics.formPrism_of_data
      hp₁x hp₁z axz bβ₁r.symm bβ₂r.symm bβ
      (hp₁ne r₂ hr₂K) (hp₁ne β₁ hβ₁K) (hp₁ne β₂ hβ₂K) nxr₂ nxβ₁ nxβ₂ nzr₂ nzβ₁ nzβ₂
      hR' hp1 hp2 ?_ ?_ E12
    · intro u hu v hv
      rw [hboundary u hu v (hK1 v hv) (hP₁avoid v hv)]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₁N₁ v hv).mp h2⟩
        · exact Or.inr ⟨h1, (hP₁N₂ v hv).mp h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₁N₁ v hv).mpr h2⟩
        · exact Or.inr ⟨h1, (hP₁N₂ v hv).mpr h2⟩
    · intro u hu v hv
      rw [hboundary u hu v (hK2 v hv) (hP₂avoid v hv)]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₂N₁ v hv).mp h2⟩
        · exact Or.inr ⟨h1, (hP₂N₂ v hv).mp h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₂N₁ v hv).mpr h2⟩
        · exact Or.inr ⟨h1, (hP₂N₂ v hv).mpr h2⟩

end Workspace.ProofLemmas.Thm75Claim2Five82CaseGapPrism
