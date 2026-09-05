/-  **12.4, claims (2) and (3)** — proof bodies transplanted verbatim from
    `ProofAttempts/thm_12_4/Claims_2_and_3.lean` (which compiles clean) into the frozen
    module `Workspace.ProofLemmas.Thm124Claims`.  Statements byte-identical. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.Thm124Setup
import Workspace.ProofLemmas.Thm124SAdjT
import Workspace.ProofLemmas.Thm124NoCompleteInRungTwo
import Workspace.ProofLemmas.Thm124Endgame
import Workspace.ProofLemmas.StaircaseStepBanisterOddPrism
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S10.Thm_10_4
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S12.Thm_12_1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm124Claims

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Claim (2) -/

/-- Claim (2) on the `A` side. -/
theorem claim2A {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) :
    ∀ v ∈ A, VertexComplete G v Q := by
  classical
  by_contra hcon
  -- PAPER: *"For suppose some vertex in `A` say is not `Q`-complete."*
  have hex : ∃ a' ∈ A, ¬ VertexComplete G a' Q := by
    by_contra h2
    exact hcon fun v hv => not_not.mp fun hn => h2 ⟨v, hv, hn⟩
  obtain ⟨a', ha'A, ha'nc⟩ := hex
  -- PAPER: *"Choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂` such that `a₁` is `Q`-complete and `a₂` is
  -- not."*
  obtain ⟨aC, haCA, haCQ⟩ := h.existsAComplete
  set X : Set V := {a ∈ A | VertexComplete G a Q} with hXdef
  set Y : Set V := {a ∈ A | ¬ VertexComplete G a Q} with hYdef
  have hXY : X ∪ Y = A := by
    ext x
    simp only [hXdef, hYdef, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx; by_cases hq : VertexComplete G x Q
      · exact Or.inl ⟨hx, hq⟩
      · exact Or.inr ⟨hx, hq⟩
  have hXYd : Disjoint X Y := by
    rw [Set.disjoint_left]
    rintro x ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hX1, hY2⟩ :=
    h.stepConnected.2.2.2.2 X Y (Or.inl hXY) hXYd ⟨aC, haCA, haCQ⟩ ⟨a', ha'A, ha'nc⟩
  have hABd : Disjoint A B := h.stepConnected.1.1
  have hrung₁ : IsRungOfStrip G A C B a₁ R₁ b₁ := hstep.1
  have hrung₂ : IsRungOfStrip G A C B a₂ R₂ b₂ := hstep.2.1
  have ha₁mem : a₁ ∈ X := by
    rcases hX1 with h1 | h1
    · exact h1
    · exact absurd (Set.disjoint_left.mp hABd h1.1 hrung₁.2.2.1) not_false
  have ha₂mem : a₂ ∈ Y := by
    rcases hY2 with h1 | h1
    · exact h1
    · exact absurd (Set.disjoint_left.mp hABd h1.1 hrung₂.2.2.1) not_false
  obtain ⟨ha₁A, ha₁Q⟩ := ha₁mem
  obtain ⟨ha₂A, ha₂Q⟩ := ha₂mem
  have ha₂A' : a₂ ∈ A := hrung₂.2.1
  have hb₂B : b₂ ∈ B := hrung₂.2.2.1
  have hR₁path : IsPathFrom G R₁ a₁ b₁ := hrung₁.1
  have hR₂path : IsPathFrom G R₂ a₂ b₂ := hrung₂.1
  -- The prism `R₀, R₁, R₂` (11.3 gives that all three rungs are odd).
  obtain ⟨hprism, hoddR₀', hoddR₁, hoddR₂⟩ :=
    StaircaseStepBanisterOddPrism.staircaseStepBanisterOddPrism G A C B a₀ b₀ a₁ b₁ a₂ b₂
      R₀ R₁ R₂ h.staircase hstep h.berge h.noPrism
  have hc02 : ∀ u ∈ R₀, ∀ v ∈ R₂,
      (G.Adj u v ↔ (u = a₀ ∧ v = a₂) ∨ (u = b₀ ∧ v = b₂)) := by
    have := hprism.2.2.2.2.2.2.2.1
    simpa using this
  have hc12 : ∀ u ∈ R₁, ∀ v ∈ R₂,
      (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)) := by
    have := hprism.2.2.2.2.2.2.2.2
    simpa using this
  have ha₁R₁ : a₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hR₁path).1
  have ha₂R₂ : a₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hR₂path).1
  have hb₂R₂ : b₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hR₂path).2
  have ha₁b₁ : a₁ ≠ b₁ := fun he => Set.disjoint_left.mp hABd ha₁A (he ▸ hrung₁.2.2.1)
  have ha₁R₂ : ∀ v ∈ R₂, (G.Adj a₁ v ↔ v = a₂) := by
    intro v hv
    rw [hc12 a₁ ha₁R₁ v hv]
    constructor
    · rintro (⟨-, rfl⟩ | ⟨he, -⟩)
      · rfl
      · exact absurd he ha₁b₁
    · rintro rfl; exact Or.inl ⟨rfl, rfl⟩
  -- every vertex of `R₂` lies in `V(S)`
  have hR₂sub : ∀ w ∈ R₂, w ∈ A ∪ B ∪ C := by
    intro w hw
    by_cases hwa : w = a₂
    · exact Or.inl (Or.inl (hwa ▸ ha₂A'))
    by_cases hwb : w = b₂
    · exact Or.inl (Or.inr (hwb ▸ hb₂B))
    · exact Or.inr (hrung₂.2.2.2.2.2 w
        ((PathBasics.mem_interior_iff_of_pathFrom hR₂path).mpr ⟨hw, hwa, hwb⟩))
  have hdisj : ∀ x ∈ R₀, x ∉ R₂ := fun x hx hx2 => h.outsideStrip x hx (hR₂sub x hx2)
  have ha₁R₀mem : a₁ ∉ R₀ := h.notMemR₀_of_memStrip a₁ (Or.inl (Or.inl ha₁A))
  have ha₁R₂mem : a₁ ∉ R₂ := hstep.2.2.1 a₁ ha₁R₁
  have hR₀Q : ∀ w ∈ R₀, w ∉ Q := h.notMemQ_of_mem
  have hR₂Q : ∀ w ∈ R₂, w ∉ Q := fun w hw => h.notMemQ_of_memStrip w (hR₂sub w hw)
  have ha₁Q0 : a₁ ∉ Q := h.notMemQ_of_memStrip a₁ (Or.inl (Or.inl ha₁A))
  have ha₁R₀ : ∀ (k : ℕ) (hk : k < R₀.length), (G.Adj a₁ (R₀[k]'hk) ↔ k = 0) :=
    fun k hk => h.adj_mem_A_iff ha₁A k hk
  -- claim (1)
  obtain ⟨iS, iT, hiS, hiT, hiS0, hiTlast, hlt, hsQ, htQ, hminS, hmaxT, hoddS, hoddT⟩ :=
    Thm124Setup.claim1 h
  have hta₁ : ¬ G.Adj (R₀[iT]'hiT) a₁ := by
    intro hadj
    have := (h.adj_mem_A_iff ha₁A iT hiT).mp hadj.symm
    omega
  have hta₂ : ¬ G.Adj (R₀[iT]'hiT) a₂ := by
    intro hadj
    have := (h.adj_mem_A_iff ha₂A' iT hiT).mp hadj.symm
    omega
  -- PAPER: *"Hence there is no `Q`-complete vertex in `R₂`."*
  have hR₂nc : ∀ w ∈ R₂, ¬ VertexComplete G w Q :=
    Thm124NoCompleteInRungTwo.no_complete_in_R₂ G h.berge Q h.anticonnQ a₀ a₁ a₂ b₀ b₂ R₀ R₂
      h.pathFrom hR₂path hc02 ha₁R₀ ha₁R₂ ha₁R₀mem ha₁R₂mem hdisj hR₀Q hR₂Q ha₁Q0
      iS iT hiS hiT hiS0 (by omega) (by omega) hminS hsQ htQ hta₁ hta₂ ha₁Q ha₂Q
  -- PAPER: *"So `s`, `t` are adjacent."*
  have hst : G.Adj (R₀[iS]'hiS) (R₀[iT]'hiT) :=
    Thm124SAdjT.s_adj_t G h.berge Q h.anticonnQ a₀ a₁ a₂ b₀ b₂ R₀ R₂
      h.pathFrom hR₂path hc02 ha₁R₀ hdisj hR₀Q hR₂Q hR₂nc ha₁Q
      iS iT hiS hiT hiS0 hiTlast hlt hminS hmaxT hsQ htQ hoddS hoddT h.oddR₀ hoddR₂
  -- PAPER: *"Hence the hole `a₀-R₀-b₀-b₂-R₂-a₂-a₀` has length ≥ 6, and the only `Q`-complete
  -- vertices in it are the adjacent vertices `s`, `t`."*
  have hlenGe := h.lengthGe
  have hR₂len : 2 ≤ R₂.length := by
    have h1 : Odd (pathLength R₂) := hoddR₂
    obtain ⟨k, hk⟩ := h1
    have := PathBasics.pathLength_eq R₂
    have hpos := PathBasics.path_length_pos hR₂path.1
    omega
  have hR₂rev : IsPathFrom G R₂.reverse b₂ a₂ := PathBasics.isPathFrom_reverse hR₂path
  have hdisj' : ∀ x ∈ R₀, x ∉ R₂.reverse := fun x hx hx2 => hdisj x hx (List.mem_reverse.mp hx2)
  have hcross : ∀ x ∈ R₀, ∀ y ∈ R₂.reverse,
      (G.Adj x y ↔ (x = b₀ ∧ y = b₂) ∨ (x = a₀ ∧ y = a₂)) := by
    intro x hx y hy
    rw [hc02 x hx y (List.mem_reverse.mp hy)]
    tauto
  have hhole : IsHoleList G (R₀ ++ R₂.reverse) :=
    PathGlue.glue_hole h.pathFrom hR₂rev hdisj' hcross (by simp; omega)
  have hmemc : ∀ x : V, x ∈ R₀ ++ R₂.reverse ↔ (x ∈ R₀ ∨ x ∈ R₂) := by
    intro x; simp [List.mem_append, List.mem_reverse]
  have hcQ : ∀ w ∈ R₀ ++ R₂.reverse, w ∉ Q := by
    intro w hw
    rcases (hmemc w).mp hw with hw' | hw'
    · exact hR₀Q w hw'
    · exact hR₂Q w hw'
  have hclen : 4 < holeLength (R₀ ++ R₂.reverse) := by
    have : holeLength (R₀ ++ R₂.reverse) = R₀.length + R₂.length := by
      simp [holeLength]
    omega
  -- `t` immediately follows `s` on `R₀`.
  have hiTeq : iT = iS + 1 := by
    have := (PathBasics.path_adj_iff h.pathList hiS hiT).mp hst
    omega
  have hsR₀ : (R₀[iS]'hiS) ∈ R₀ := List.getElem_mem hiS
  have htR₀ : (R₀[iT]'hiT) ∈ R₀ := List.getElem_mem hiT
  have honly : ∀ w ∈ R₀ ++ R₂.reverse, VertexComplete G w Q →
      w = (R₀[iS]'hiS) ∨ w = (R₀[iT]'hiT) := by
    intro w hw hwQ
    rcases (hmemc w).mp hw with hw' | hw'
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw'
      rcases lt_trichotomy k iS with hlt' | heq | hgt
      · exact absurd hwQ (hminS k hk hlt')
      · exact Or.inl (by subst heq; rfl)
      · rcases Nat.lt_or_ge iT k with hgt' | hle
        · exact absurd hwQ (hmaxT k hk hgt')
        · have : k = iT := by omega
          exact Or.inr (by subst this; rfl)
    · exact absurd hwQ (hR₂nc w hw')
  -- PAPER: *"By 2.10 `Q` contains a hat or a leap; and in either case there is a vertex
  -- `q ∈ Q` with no neighbours in `R₂`."*
  have hsne : (R₀[iS]'hiS) ≠ a₀ ∧ (R₀[iS]'hiS) ≠ b₀ := by
    constructor
    · rw [← h.getElem_zero]
      exact PathBasics.path_ne_of_ne_index h.pathList hiS h.lengthPos (by omega)
    · rw [← h.getElem_last]
      exact PathBasics.path_ne_of_ne_index h.pathList hiS (by omega) (by omega)
  have htne : (R₀[iT]'hiT) ≠ a₀ ∧ (R₀[iT]'hiT) ≠ b₀ := by
    constructor
    · rw [← h.getElem_zero]
      exact PathBasics.path_ne_of_ne_index h.pathList hiT h.lengthPos (by omega)
    · rw [← h.getElem_last]
      exact PathBasics.path_ne_of_ne_index h.pathList hiT (by omega) (by omega)
  have leapkey : ∀ u v aa bb : V,
      (u ∈ R₀ ∧ u ≠ a₀ ∧ u ≠ b₀) → (v ∈ R₀ ∧ v ≠ a₀ ∧ v ≠ b₀) → aa ∈ Q →
      IsLeapForHole G (R₀ ++ R₂.reverse) u v aa bb → ∀ x ∈ R₂, ¬ G.Adj aa x := by
    rintro u v aa bb ⟨huR, hua, hub⟩ ⟨hvR, hva, hvb⟩ haaQ ⟨-, i, hhead, hlast, hlp⟩ x hx hadj
    obtain ⟨hpl, hplen, -, -, hadja, -⟩ := hlp
    set p : List V := (R₀ ++ R₂.reverse).rotate i with hpdef
    have hplen0 : 0 < p.length := PathBasics.path_length_pos hpl
    have hp0 : p[0]'hplen0 = v := PathBasics.getElem_zero_of_head? hhead hplen0
    have hpn : p[p.length - 1]'(by omega) = u :=
      PathBasics.getElem_last_of_getLast? hlast hplen0
    have haaR₀ : aa ∉ R₀ := fun hm => hR₀Q aa hm haaQ
    have haau : aa ≠ u := fun he => haaR₀ (he ▸ huR)
    have haav : aa ≠ v := fun he => haaR₀ (he ▸ hvR)
    have hxR₀ : x ∉ R₀ := fun hm => hdisj x hm hx
    have hxp : x ∈ p := by
      rw [hpdef, List.mem_rotate]
      exact (hmemc x).mpr (Or.inr hx)
    obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hxp
    have hdadj : (G.deleteEdges {s(u, v)}).Adj aa x := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hadj, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact haau rfl
      · exact haav rfl
    have := (hadja j hj).mp (by rw [hxj]; exact hdadj)
    rcases this with hj0 | hj1 | hjn
    · subst hj0; rw [hp0] at hxj; exact hxR₀ (hxj ▸ hvR)
    · -- `p[1]` is a neighbour of `p[0] = v` on the hole, so it cannot lie in `R₂`.
      have h1lt : 1 < p.length := by
        have : p.length = (R₀ ++ R₂.reverse).length := by rw [hpdef, List.length_rotate]
        simp at this; omega
      have hadj01 : (G.deleteEdges {s(u, v)}).Adj (p[0]'hplen0) (p[1]'h1lt) :=
        PathBasics.path_adj_succ hpl h1lt
      have hGadj : G.Adj v x := by
        have := (SimpleGraph.deleteEdges_le (G := G) {s(u, v)}) hadj01
        rw [hp0] at this
        subst hj1; rw [hxj] at this; exact this
      rcases (hc02 v hvR x hx).mp hGadj with ⟨he, -⟩ | ⟨he, -⟩
      · exact hva he
      · exact hvb he
    · subst hjn; rw [hpn] at hxj; exact hxR₀ (hxj ▸ huR)
  have hqex : ∃ q ∈ Q, ∀ x ∈ R₂, ¬ G.Adj q x := by
    rcases Workspace.Statements.S02.SPGT.thm_2_10 G h.berge Q h.anticonnQ (R₀ ++ R₂.reverse)
        hhole hcQ hclen (R₀[iS]'hiS) (R₀[iT]'hiT)
        ((hmemc _).mpr (Or.inl hsR₀)) ((hmemc _).mpr (Or.inl htR₀)) hst hsQ htQ honly with
      ⟨hh, hhQ, hhat⟩ | ⟨aa, haaQ, bb, hbbQ, hleap⟩
    · refine ⟨hh, hhQ, ?_⟩
      intro x hx
      refine hhat.2.2.2.2.2.2 x ((hmemc x).mpr (Or.inr hx)) ?_ ?_
      · exact fun he => hdisj x (he ▸ hsR₀) hx
      · exact fun he => hdisj x (he ▸ htR₀) hx
    · refine ⟨aa, haaQ, ?_⟩
      rcases hleap with hl | hl
      · exact leapkey _ _ _ _ ⟨hsR₀, hsne.1, hsne.2⟩ ⟨htR₀, htne.1, htne.2⟩ haaQ hl
      · exact leapkey _ _ _ _ ⟨htR₀, htne.1, htne.2⟩ ⟨hsR₀, hsne.1, hsne.2⟩ haaQ hl
  obtain ⟨q, hqQ, hqR₂⟩ := hqex
  -- PAPER: *"But `q` is adjacent to `s` and `a₁`, contrary to 10.4 applied to the prism formed
  -- by `R₀`, `R₁`, `R₂`."*
  have hR₁sub : ∀ w ∈ R₁, w ∈ A ∪ B ∪ C := by
    intro w hw
    by_cases hwa : w = a₁
    · exact Or.inl (Or.inl (hwa ▸ ha₁A))
    by_cases hwb : w = b₁
    · exact Or.inl (Or.inr (hwb ▸ hrung₁.2.2.1))
    · exact Or.inr (hrung₁.2.2.2.2.2 w
        ((PathBasics.mem_interior_iff_of_pathFrom hR₁path).mpr ⟨hw, hwa, hwb⟩))
  have hqOut : q ∉ staircaseVertices A C B R₀ := h.outsideQ q hqQ
  have hqR₀ : q ∉ R₀ := fun hm => hqOut (Or.inl hm)
  have hqS : q ∉ A ∪ B ∪ C := fun hm => hqOut (Or.inr hm)
  set K : Set V := {v : V | v ∈ R₀} ∪ {v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} with hKdef
  have hFK : ({q} : Set V) ⊆ Kᶜ := by
    rintro y rfl
    rintro (⟨hy | hy⟩ | hy)
    · exact hqR₀ hy
    · exact hqS (hR₁sub y hy)
    · exact hqS (hR₂sub y hy)
  have hFconn : ConnectedSet G ({q} : Set V) := by
    intro u v
    have : u = v := Subtype.ext (by rw [u.2, v.2])
    rw [this]
  have hsK : (R₀[iS]'hiS) ∈ K := Or.inl (Or.inl hsR₀)
  have ha₁K : a₁ ∈ K := Or.inl (Or.inr ha₁R₁)
  have hsatt : (R₀[iS]'hiS) ∈ attachments G ({q} : Set V) K :=
    ⟨hsK, q, rfl, hsQ q hqQ⟩
  have ha₁att : a₁ ∈ attachments G ({q} : Set V) K :=
    ⟨ha₁K, q, rfl, ha₁Q q hqQ⟩
  have hsR₁ : (R₀[iS]'hiS) ∉ R₁ := fun hm => h.outsideStrip _ hsR₀ (hR₁sub _ hm)
  have hsR₂ : (R₀[iS]'hiS) ∉ R₂ := hdisj _ hsR₀
  have hsA : (R₀[iS]'hiS) ∉ A := fun hm => h.outsideStrip _ hsR₀ (Or.inl (Or.inl hm))
  have hsB : (R₀[iS]'hiS) ∉ B := fun hm => h.outsideStrip _ hsR₀ (Or.inl (Or.inr hm))
  have hFloc : ¬ LocalForPrism (![a₀, a₁, a₂] : Fin 3 → V) (![b₀, b₁, b₂] : Fin 3 → V)
      R₀ R₁ R₂ (attachments G ({q} : Set V) K) := by
    rintro (hL | hL | hL | hL | hL)
    · exact ha₁R₀mem (hL ha₁att)
    · exact hsR₁ (hL hsatt)
    · exact hsR₂ (hL hsatt)
    · have := hL hsatt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with he | he | he
      · exact hsne.1 he
      · exact hsA (he ▸ ha₁A)
      · exact hsA (he ▸ ha₂A')
    · have := hL hsatt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with he | he | he
      · exact hsne.2 he
      · exact hsB (he ▸ hrung₁.2.2.1)
      · exact hsB (he ▸ hb₂B)
  have hR₃ : ∀ v ∈ attachments G ({q} : Set V) K, v ∉ (![R₀, R₁, R₂] : Fin 3 → List V) 2 := by
    intro v hv hvR
    obtain ⟨-, f, hf, hadj⟩ := hv
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact hqR₂ v (by simpa using hvR) hadj.symm
  have h104 := Workspace.Statements.S10.SPGT.thm_10_4 G h.berge
    (by rintro ⟨n, H, K', happ, -⟩; exact h.noK4 ⟨n, H, K', happ⟩)
    (![a₀, a₁, a₂] : Fin 3 → V) (![b₀, b₁, b₂] : Fin 3 → V)
    (![R₀, R₁, R₂] : Fin 3 → List V) K ({q} : Set V)
    (by simpa using hprism) (by simp [hKdef]) hFK hFconn
    (fun hev => absurd ⟨_, _, _, _, _, hev⟩ h.noPrism)
    (by simpa using hFloc) hR₃
  exact absurd h104.1 (Set.not_nontrivial_singleton)

/-- **12.4 (2)** *"Every vertex in `A ∪ B` is `Q`-complete."* -/
theorem claim2 {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) :
    ∀ v ∈ A ∪ B, VertexComplete G v Q := by
  rintro v (hv | hv)
  · exact claim2A h v hv
  · exact claim2A (Thm124Setup.Setup.swap h) v hv

/-! ### Ingredients of claim (3) -/

/-- From step-connectedness: every vertex of `B` has a nonneighbour in `A`. -/
theorem exists_A_nonadj {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) (b : V) (hb : b ∈ B) :
    ∃ a ∈ A, ¬ G.Adj a b := by
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hmem⟩ :=
    h.stepConnected.2.2.2.1 b (Or.inl (Or.inr hb))
  have hABd : Disjoint A B := h.stepConnected.1.1
  have hrung₁ : IsRungOfStrip G A C B a₁ R₁ b₁ := hstep.1
  have hrung₂ : IsRungOfStrip G A C B a₂ R₂ b₂ := hstep.2.1
  have ha₁R₁ : a₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hrung₁.1).1
  have ha₂R₂ : a₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hrung₂.1).1
  have ha₁b₁ : a₁ ≠ b₁ := fun he => Set.disjoint_left.mp hABd hrung₁.2.1 (he ▸ hrung₁.2.2.1)
  have ha₂b₂ : a₂ ≠ b₂ := fun he => Set.disjoint_left.mp hABd hrung₂.2.1 (he ▸ hrung₂.2.2.1)
  rcases hmem with hbR | hbR
  · -- `b` is the `B`-end of `R₁`; then `a₂ ∈ A` is a nonneighbour of `b`
    have hbeq : b = b₁ := hrung₁.2.2.2.2.1 b hbR hb
    refine ⟨a₂, hrung₂.2.1, ?_⟩
    intro hadj
    rcases (hstep.2.2.2 b hbR a₂ ha₂R₂).mp hadj.symm with ⟨he, -⟩ | ⟨-, he⟩
    · exact ha₁b₁ (he.symm.trans hbeq)
    · exact ha₂b₂ he
  · -- `b` is the `B`-end of `R₂`; then `a₁ ∈ A` is a nonneighbour of `b`
    have hbeq : b = b₂ := hrung₂.2.2.2.2.1 b hbR hb
    refine ⟨a₁, hrung₁.2.1, ?_⟩
    intro hadj
    rcases (hstep.2.2.2 a₁ ha₁R₁ b hbR).mp hadj with ⟨-, he⟩ | ⟨he, -⟩
    · exact ha₂b₂ (he.symm.trans hbeq)
    · exact ha₁b₁ he

/-- From step-connectedness: every vertex of `A` has a nonneighbour in `B`. -/
theorem exists_B_nonadj {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) (a : V) (ha : a ∈ A) :
    ∃ b ∈ B, ¬ G.Adj a b := by
  obtain ⟨b, hb, hnadj⟩ := exists_A_nonadj (Thm124Setup.Setup.swap h) a ha
  exact ⟨b, hb, fun hadj => hnadj hadj.symm⟩

/-! ## Claim (3) -/

/-- **12.4 (3)** *"Every major vertex is either in `Q` or complete to `Q`."* -/
theorem claim3 {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) (v : V)
    (hvmaj : MajorForStaircase G A C B a₀ R₀ b₀ v) :
    v ∈ Q ∨ VertexComplete G v Q := by
  classical
  by_contra hcon
  obtain ⟨hvQ, hvnc⟩ := not_or.mp hcon
  obtain ⟨hvK, ⟨xA, hxA, hvxA⟩, ⟨yB, hyB, hvyB⟩, ⟨zR, hzR, hvzR⟩⟩ := hvmaj
  have hABd : Disjoint A B := h.stepConnected.1.1
  -- PAPER: *"suppose `v ∉ Q`, and `Q₀` is anticonnected, where `Q₀ = Q ∪ {v}`."*
  have hQ₀anti : AnticonnectedSet G (Q ∪ {v}) := by
    have hex : ∃ q ∈ Q, Gᶜ.Adj v q := by
      by_contra hno
      refine hvnc ?_
      intro q hq
      by_contra hadj
      exact hno ⟨q, hq, by
        rw [SimpleGraph.compl_adj]
        exact ⟨fun he => hvQ (he ▸ hq), hadj⟩⟩
    exact ConnectedSetUnionAttach.connectedSet_union_singleton h.anticonnQ hex
  -- PAPER: *"From 12.1, `v` is either left- or right-diagonal, or central"*
  obtain ⟨i, hi, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1 G h.berge h.noK4 h.noPrism
    h.noBreaker A C B a₀ b₀ R₀ h.maximal v hvK
  have hdiag : LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
      CentralForStaircase G A C B a₀ R₀ b₀ v := by
    fin_cases i
    · -- alternative 1: `v` is minor — impossible for a major vertex
      exfalso
      obtain ⟨⟨-, hloc⟩, -⟩ := hi
      have hxAmem : xA ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ :=
        ⟨hvxA, Or.inr (Or.inl (Or.inl hxA))⟩
      have hyBmem : yB ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ :=
        ⟨hvyB, Or.inr (Or.inl (Or.inr hyB))⟩
      have hzRmem : zR ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ :=
        ⟨hvzR, Or.inl hzR⟩
      have ha₀R₀ : a₀ ∈ R₀ := (PathBasics.isPathFrom_ends_mem h.pathFrom).1
      have hb₀R₀ : b₀ ∈ R₀ := (PathBasics.isPathFrom_ends_mem h.pathFrom).2
      rcases hloc with hL | hL | hL | hL
      · exact h.outsideStrip zR hzR (hL hzRmem)
      · exact h.notMemR₀_of_memStrip xA (Or.inl (Or.inl hxA)) (hL hxAmem)
      · rcases hL hyBmem with hy | hy
        · exact Set.disjoint_left.mp hABd hy hyB
        · rw [Set.mem_singleton_iff] at hy
          exact h.outsideStrip a₀ ha₀R₀ (hy ▸ Or.inl (Or.inr hyB))
      · rcases hL hxAmem with hx | hx
        · exact Set.disjoint_left.mp hABd hxA hx
        · rw [Set.mem_singleton_iff] at hx
          exact h.outsideStrip b₀ hb₀R₀ (hx ▸ Or.inl (Or.inl hxA))
    · exact hi.2
    · -- alternative 3: `v` is a left- or right-star — impossible for a major vertex
      exfalso
      rcases hi with ⟨hstar, -⟩ | ⟨hstar, -⟩
      · exact hstar.2.2 yB (Or.inl hyB) hvyB
      · exact hstar.2.2 xA (Or.inl hxA) hvxA
  -- PAPER: *"in either case it has neighbours `a₁ ∈ A` and `b₁ ∈ B` that are nonadjacent."*
  obtain ⟨a₁, ha₁A, b₁, hb₁B, hva₁, hvb₁, hnab⟩ :
      ∃ a₁ ∈ A, ∃ b₁ ∈ B, G.Adj v a₁ ∧ G.Adj v b₁ ∧ ¬ G.Adj a₁ b₁ := by
    rcases hdiag with hd | hd | hd
    · obtain ⟨a₁, ha₁A, hna⟩ := exists_A_nonadj h yB hyB
      exact ⟨a₁, ha₁A, yB, hyB, hd.2 a₁ (Or.inl ha₁A), hvyB, hna⟩
    · obtain ⟨b₁, hb₁B, hnb⟩ := exists_B_nonadj h xA hxA
      exact ⟨xA, hxA, b₁, hb₁B, hvxA, hd.2 b₁ (Or.inl hb₁B), hnb⟩
    · obtain ⟨b₁, hb₁B, hnb⟩ := exists_B_nonadj h xA hxA
      exact ⟨xA, hxA, b₁, hb₁B, hvxA, hd.2.1 b₁ (Or.inr hb₁B), hnb⟩
  -- PAPER: *"It follows that `a₁-a₀-R₀-b₀-b₁` is an odd path of length ≥ 5, and its ends are
  -- `Q₀`-complete."*
  have hvA : v ∉ A := fun hm => hvK (Or.inr (Or.inl (Or.inl hm)))
  have hvB : v ∉ B := fun hm => hvK (Or.inr (Or.inl (Or.inr hm)))
  have hvR₀ : v ∉ R₀ := fun hm => hvK (Or.inl hm)
  have ha₁R₀ : a₁ ∉ R₀ := h.notMemR₀_of_memStrip a₁ (Or.inl (Or.inl ha₁A))
  have hb₁R₀ : b₁ ∉ R₀ := h.notMemR₀_of_memStrip b₁ (Or.inl (Or.inr hb₁B))
  have ha₁b₁ne : a₁ ≠ b₁ := fun he => Set.disjoint_left.mp hABd ha₁A (he ▸ hb₁B)
  have ha₁a₀ : G.Adj a₁ a₀ := (h.leftStar.2.1 a₁ ha₁A).symm
  have hb₁b₀ : G.Adj b₁ b₀ := (h.rightStar.2.1 b₁ hb₁B).symm
  have hlenR₀ := h.lengthGe
  have hpath : IsPathFrom G (a₁ :: (R₀ ++ [b₁])) a₁ b₁ :=
    PathAttach.isPathFrom_cons_concat h.pathFrom ha₁a₀ hb₁b₀ hnab ha₁b₁ne ha₁R₀ hb₁R₀
      (by
        intro x hx hxa₀ hadj
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        have hk0 := (h.adj_mem_A_iff ha₁A k hk).mp hadj
        subst hk0
        exact hxa₀ h.getElem_zero)
      (by
        intro x hx hxb₀ hadj
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        have hk0 := (h.adj_mem_B_iff hb₁B k hk).mp hadj
        subst hk0
        exact hxb₀ h.getElem_last)
  have hplen : (a₁ :: (R₀ ++ [b₁])).length = R₀.length + 2 :=
    PathAttach.length_cons_append_singleton a₁ b₁ R₀
  have hpl : pathLength (a₁ :: (R₀ ++ [b₁])) = R₀.length + 1 :=
    PathAttach.pathLength_cons_append_singleton a₁ b₁ R₀
  have hodd : Odd (pathLength (a₁ :: (R₀ ++ [b₁]))) := by
    rw [hpl]
    obtain ⟨k, hk⟩ := h.oddR₀
    rw [PathBasics.pathLength_eq] at hk
    exact ⟨k + 1, by omega⟩
  have h5le : 5 ≤ pathLength (a₁ :: (R₀ ++ [b₁])) := by rw [hpl]; omega
  have hcompl : ∀ w : V, VertexComplete G w Q → G.Adj w v → VertexComplete G w (Q ∪ {v}) := by
    intro w hwQ hwv x hx
    rcases hx with hx | hx
    · exact hwQ x hx
    · rw [Set.mem_singleton_iff] at hx; exact hx ▸ hwv
  have ha₁Q₀ : VertexComplete G a₁ (Q ∪ {v}) :=
    hcompl a₁ (claim2 h a₁ (Or.inl ha₁A)) hva₁.symm
  have hb₁Q₀ : VertexComplete G b₁ (Q ∪ {v}) :=
    hcompl b₁ (claim2 h b₁ (Or.inr hb₁B)) hvb₁.symm
  have hpQ₀ : ∀ w ∈ (a₁ :: (R₀ ++ [b₁])), w ∉ Q ∪ {v} := by
    intro w hw
    rw [PathAttach.mem_cons_append_singleton] at hw
    rintro (hq | hq)
    · rcases hw with rfl | hw | rfl
      · exact h.notMemQ_of_memStrip _ (Or.inl (Or.inl ha₁A)) hq
      · exact h.notMemQ_of_mem _ hw hq
      · exact h.notMemQ_of_memStrip _ (Or.inl (Or.inr hb₁B)) hq
    · rw [Set.mem_singleton_iff] at hq
      rcases hw with he | hw | he
      · exact hvA (by rw [← hq, he]; exact ha₁A)
      · exact hvR₀ (by rw [← hq]; exact hw)
      · exact hvB (by rw [← hq, he]; exact hb₁B)
  -- PAPER: *"From the maximality of `Q`, none of its internal vertices are `Q₀`-complete"*
  have hsub : Q ⊆ Q ∪ {v} := Set.subset_union_left
  have hR₀nc : ∀ w ∈ R₀, ¬ VertexComplete G w (Q ∪ {v}) := by
    intro w hw hwc
    have h2b : IsTwoBreaker G A C B a₀ R₀ b₀ (Q ∪ {v}) := by
      refine ⟨h.stronglyMaximal, ⟨?_, hQ₀anti⟩, ⟨⟨a₁, ha₁A, ha₁Q₀⟩, ⟨b₁, hb₁B, hb₁Q₀⟩⟩,
        ⟨?_, ?_⟩, ⟨w, hw, hwc⟩⟩
      · rintro q (hq | hq)
        · exact h.outsideQ q hq
        · rw [Set.mem_singleton_iff] at hq; exact hq ▸ hvK
      · exact fun hc => h.a₀NotComplete fun x hx => hc x (hsub hx)
      · exact fun hc => h.b₀NotComplete fun x hx => hc x (hsub hx)
    have heq := h.qmax (Q ∪ {v}) hsub h2b
    exact hvQ (heq ▸ (show v ∈ Q ∪ {v} from Or.inr rfl))
  have hnoedge : ¬ ∃ u ∈ (a₁ :: (R₀ ++ [b₁])), ∃ w ∈ (a₁ :: (R₀ ++ [b₁])),
      EdgeComplete G (Q ∪ {v}) u w := by
    rintro ⟨u, hu, w, hw, hadj, huc, hwc⟩
    rw [PathAttach.mem_cons_append_singleton] at hu hw
    have hu' : u = a₁ ∨ u = b₁ := by
      rcases hu with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd huc (hR₀nc u h1)
      · exact Or.inr h1
    have hw' : w = a₁ ∨ w = b₁ := by
      rcases hw with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd hwc (hR₀nc w h1)
      · exact Or.inr h1
    rcases hu' with rfl | rfl <;> rcases hw' with rfl | rfl
    · exact G.irrefl hadj
    · exact hnab hadj
    · exact hnab hadj.symm
    · exact G.irrefl hadj
  -- PAPER: *"and so by 2.1, `Q₀` contains a leap `q₁, q₂` say."*
  obtain ⟨iS, iT, hiS, hiT, hiS0, hiTlast, hlt, hsQ, htQ, hminS, hmaxT, hoddS, hoddT⟩ :=
    Thm124Setup.claim1 h
  rcases Workspace.Statements.S02.SPGT.thm_2_1 G h.berge (Q ∪ {v}) hQ₀anti
      (a₁ :: (R₀ ++ [b₁])) a₁ b₁ hpath hpQ₀ hodd ha₁Q₀ hb₁Q₀ with
    hcase | ⟨-, aa, haaQ₀, bb, hbbQ₀, hleap⟩ | ⟨h3, -⟩
  · exact hnoedge hcase
  · -- PAPER: *"So neither of `q₁, q₂` has neighbours in the interior of `R₀`; but this is
    -- impossible since one of them is in `Q` and is therefore adjacent to `s`."*
    obtain ⟨-, -, hne, -, hadja, hadjb⟩ := hleap
    have hidx : iS + 1 < (a₁ :: (R₀ ++ [b₁])).length := by rw [hplen]; omega
    have hpget : (a₁ :: (R₀ ++ [b₁]))[iS + 1]'hidx = R₀[iS]'hiS := by
      simp [List.getElem_append_left hiS]
    have hna : ¬ G.Adj aa (R₀[iS]'hiS) := by
      intro hadj
      have hcases := (hadja (iS + 1) hidx).mp (by rw [hpget]; exact hadj)
      rw [hplen] at hcases
      omega
    have hnb : ¬ G.Adj bb (R₀[iS]'hiS) := by
      intro hadj
      have hcases := (hadjb (iS + 1) hidx).mp (by rw [hpget]; exact hadj)
      rw [hplen] at hcases
      omega
    have hone : aa ∈ Q ∨ bb ∈ Q := by
      rcases haaQ₀ with h1 | h1
      · exact Or.inl h1
      · rcases hbbQ₀ with h2 | h2
        · exact Or.inr h2
        · rw [Set.mem_singleton_iff] at h1 h2
          exact absurd (h1.trans h2.symm) hne
    rcases hone with hq | hq
    · exact hna (hsQ aa hq).symm
    · exact hnb (hsQ bb hq).symm
  · omega





end Workspace.ProofLemmas.Thm124Claims
