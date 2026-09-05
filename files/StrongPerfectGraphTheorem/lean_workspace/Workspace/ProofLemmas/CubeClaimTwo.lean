import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.CubeComplement
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S04.Thm_4_5
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S14.Thm_14_1
import Workspace.Statements.S14.Thm_14_2

/-!
# Claim (2) of the proof of 14.3 — "no anticomponent of `Y` is complete to `A ∪ D`"
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CubeClaimTwo

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*}

/-! ## Squares -/

/-- The adjacencies of the four vertices of a square `a₁-b₁-b₂-a₂-a₁`. -/
private theorem square_edges {G : SimpleGraph V} {S T : Set V} {a₁ b₁ b₂ a₂ : V}
    (h : IsSquare G S T a₁ b₁ b₂ a₂) :
    G.Adj a₁ b₁ ∧ G.Adj b₁ b₂ ∧ ¬ G.Adj a₁ b₂ ∧ ¬ G.Adj b₁ a₂ := by
  obtain ⟨hhole, -, -, -, -⟩ := h
  obtain ⟨-, -, hadj⟩ := hhole
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hadj 0 1 (by simp) (by simp)).mpr (by simp)
  · exact (hadj 1 2 (by simp) (by simp)).mpr (by simp)
  · intro hc
    have h2 := (hadj 0 2 (by simp) (by simp)).mp hc
    simp at h2
  · intro hc
    have h2 := (hadj 1 3 (by simp) (by simp)).mp hc
    simp at h2

/-- Every vertex of `S` has a neighbour in `T` when `(S,T)` is square-connected. -/
private theorem exists_adj_left {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {a : V} (ha : a ∈ S) : ∃ b ∈ T, G.Adj a b := by
  obtain ⟨htriv, hclause, -⟩ := h
  obtain ⟨a', ha', hne⟩ := htriv.1.exists_ne a
  obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, -⟩ :=
    hclause {a} (S \ {a}) (Set.union_diff_cancel (Set.singleton_subset_iff.mpr ha))
      (Set.disjoint_left.mpr (fun x hx1 hx2 => hx2.2 hx1)) ⟨a, rfl⟩ ⟨a', ha', hne⟩
  have he : a₁ = a := h1
  exact ⟨b₁, hsq.2.2.2.1, he ▸ (square_edges hsq).1⟩

/-- Every vertex of `S` has a non-neighbour in `T` when `(S,T)` is square-connected. -/
private theorem exists_nonadj_left {G : SimpleGraph V} {S T : Set V}
    (h : SquareConnected G S T) {a : V} (ha : a ∈ S) : ∃ b ∈ T, ¬ G.Adj a b := by
  obtain ⟨htriv, hclause, -⟩ := h
  obtain ⟨a', ha', hne⟩ := htriv.1.exists_ne a
  obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, -⟩ :=
    hclause {a} (S \ {a}) (Set.union_diff_cancel (Set.singleton_subset_iff.mpr ha))
      (Set.disjoint_left.mpr (fun x hx1 hx2 => hx2.2 hx1)) ⟨a, rfl⟩ ⟨a', ha', hne⟩
  have he : a₁ = a := h1
  exact ⟨b₂, hsq.2.2.2.2, he ▸ (square_edges hsq).2.2.1⟩

/-- Square-connectedness of `(S,T)` makes `T` connected: for any splitting of `T` into two
nonempty pieces there is a square crossing it, and the middle edge `b₁b₂` of that square is an
edge of `T` across the splitting. -/
private theorem connectedSet_right_of_squareConnected [Fintype V] {G : SimpleGraph V}
    {S T : Set V} (h : SquareConnected G S T) (hT : T.Nonempty) : ConnectedSet G T := by
  by_contra hcon
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := ComponentsOfSetBasics.exists_two_isComponent G hT hcon
  obtain ⟨q, hq⟩ := ComponentsOfSetBasics.nonempty_of_isComponent G hT hQ
  obtain ⟨a₁, b₁, b₂, a₂, hsq, h1, h2⟩ :=
    h.2.2 P (T \ P) (Set.union_diff_cancel hP.1)
      (Set.disjoint_left.mpr (fun x hx1 hx2 => hx2.2 hx1))
      (ComponentsOfSetBasics.nonempty_of_isComponent G hT hP)
      ⟨q, hQ.1 hq, fun hqP =>
        (ComponentsOfSetBasics.disjoint_of_isComponent G hQ hP (fun he => hPQ he.symm)).le_bot
          ⟨hq, hqP⟩⟩
  obtain ⟨Q', hQ', hb₂⟩ := ComponentsOfSetBasics.exists_isComponent_mem G T hsq.2.2.2.2
  have hne : P ≠ Q' := fun he => h2.2 (he ▸ hb₂)
  exact ComponentsOfSetBasics.anticomplete_of_isComponent G hP hQ' hne b₁ h1 b₂ hb₂
    (square_edges hsq).2.1

/-! ## Anticonnected unions -/

/-- If `S` is anticomplete to `T` and both are nonempty and disjoint, then `S ∪ T` is
anticonnected: in `Gᶜ` every vertex of `S` is adjacent to every vertex of `T`. -/
private theorem anticonnectedSet_union {G : SimpleGraph V} {S T : Set V}
    (hdisj : Disjoint S T) (hanti : Anticomplete G S T) (hS : S.Nonempty) (hT : T.Nonempty) :
    AnticonnectedSet G (S ∪ T) := by
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨t₀, ht₀⟩ := hT
  have key : ∀ (s : V) (hs : s ∈ S) (t : V) (ht : t ∈ T),
      (Gᶜ.induce (S ∪ T)).Adj ⟨s, Or.inl hs⟩ ⟨t, Or.inr ht⟩ := by
    intro s hs t ht
    have hne : s ≠ t := by
      intro hst
      have hsT : s ∈ T := by rw [hst]; exact ht
      exact Set.disjoint_left.mp hdisj hs hsT
    exact ⟨fun he => hne he, hanti s hs t ht⟩
  have reach : ∀ x : ↥(S ∪ T), (Gᶜ.induce (S ∪ T)).Reachable x ⟨t₀, Or.inr ht₀⟩ := by
    rintro ⟨x, hx | hx⟩
    · exact (key x hx t₀ ht₀).reachable
    · exact ((key s₀ hs₀ x hx).symm).reachable.trans (key s₀ hs₀ t₀ ht₀).reachable
  intro x y
  exact (reach x).trans (reach y).symm

/-! ## No vertex is both minor and major -/

/-- PAPER (printed p. 88): the two cases of 14.1 are exclusive, so the set `F` of minor vertices
and the set `Y` of major vertices are disjoint.  The `14` cases in which the *minor* superset and
the *major* subset are incomparable are settled by disjointness of the cube's four parts; the two
remaining cases force `A` complete to `B` (resp. `C` complete to `D`), which square-connectedness
(resp. antisquare-connectedness) forbids. -/
private theorem not_minor_major {G : SimpleGraph V} {A B C D : Set V} (hcube : IsCube G A B C D)
    {v : V} (hmin : MinorForCube G A B C D v) (hmaj : MajorForCube G A B C D v) : False := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, ⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩, ⟨c₀, hc₀⟩, ⟨d₀, hd₀⟩⟩,
    ⟨-, -, -, -⟩, hsqAB, hsqCD⟩ := hcube
  obtain ⟨-, hminsub, hmincomp⟩ := hmin
  obtain ⟨-, hmajsup, -⟩ := hmaj
  -- the eight non-memberships used by the fourteen incomparable cases
  have naCD : a₀ ∉ C ∪ D := fun h => h.elim (Set.disjoint_left.mp dAC ha₀)
    (Set.disjoint_left.mp dAD ha₀)
  have naBD : a₀ ∉ B ∪ D := fun h => h.elim (Set.disjoint_left.mp dAB ha₀)
    (Set.disjoint_left.mp dAD ha₀)
  have nbCD : b₀ ∉ C ∪ D := fun h => h.elim (Set.disjoint_left.mp dBC hb₀)
    (Set.disjoint_left.mp dBD hb₀)
  have nbAC : b₀ ∉ A ∪ C := fun h => h.elim (fun hh => Set.disjoint_left.mp dAB hh hb₀)
    (Set.disjoint_left.mp dBC hb₀)
  have ncAB : c₀ ∉ A ∪ B := fun h => h.elim (fun hh => Set.disjoint_left.mp dAC hh hc₀)
    (fun hh => Set.disjoint_left.mp dBC hh hc₀)
  have ncBD : c₀ ∉ B ∪ D := fun h => h.elim (fun hh => Set.disjoint_left.mp dBC hh hc₀)
    (fun hh => Set.disjoint_left.mp dCD hc₀ hh)
  have ndAB : d₀ ∉ A ∪ B := fun h => h.elim (fun hh => Set.disjoint_left.mp dAD hh hd₀)
    (fun hh => Set.disjoint_left.mp dBD hh hd₀)
  have ndAC : d₀ ∉ A ∪ C := fun h => h.elim (fun hh => Set.disjoint_left.mp dAD hh hd₀)
    (fun hh => Set.disjoint_left.mp dCD hh hd₀)
  -- the two "complete" cases
  have hnotAB : ¬ Complete G A B := by
    obtain ⟨b, hb, hnadj⟩ := exists_nonadj_left hsqAB ha₀
    exact fun hc => hnadj (hc a₀ ha₀ b hb)
  have hnotCD : ¬ Complete G C D := by
    obtain ⟨d, hd, hadj⟩ := exists_adj_left hsqCD hc₀
    exact fun hc => hadj.2 (hc c₀ hc₀ d hd)
  rcases hmajsup with hsup | hsup | hsup | hsup
  · -- `A ∪ B ⊆ N`
    rcases hminsub with hsub | hsub | hsub | hsub
    · exact hnotAB fun x hx y hy =>
        hmincomp x ⟨hsup (Or.inl hx), Or.inl hx⟩ y ⟨hsup (Or.inr hy), Or.inl hy⟩
    · exact nbCD (hsub (hsup (Or.inr hb₀)))
    · exact nbAC (hsub (hsup (Or.inr hb₀)))
    · exact naBD (hsub (hsup (Or.inl ha₀)))
  · -- `C ∪ D ⊆ N`
    rcases hminsub with hsub | hsub | hsub | hsub
    · exact ncAB (hsub (hsup (Or.inl hc₀)))
    · exact hnotCD fun x hx y hy =>
        hmincomp x ⟨hsup (Or.inl hx), Or.inr hx⟩ y ⟨hsup (Or.inr hy), Or.inr hy⟩
    · exact ndAC (hsub (hsup (Or.inr hd₀)))
    · exact ncBD (hsub (hsup (Or.inl hc₀)))
  · -- `A ∪ D ⊆ N`
    rcases hminsub with hsub | hsub | hsub | hsub
    · exact ndAB (hsub (hsup (Or.inr hd₀)))
    · exact naCD (hsub (hsup (Or.inl ha₀)))
    · exact ndAC (hsub (hsup (Or.inr hd₀)))
    · exact naBD (hsub (hsup (Or.inl ha₀)))
  · -- `B ∪ C ⊆ N`
    rcases hminsub with hsub | hsub | hsub | hsub
    · exact ncAB (hsub (hsup (Or.inr hc₀)))
    · exact nbCD (hsub (hsup (Or.inl hb₀)))
    · exact nbAC (hsub (hsup (Or.inl hb₀)))
    · exact ncBD (hsub (hsup (Or.inr hc₀)))

/-! ## Which vertex of a path an end is adjacent to -/

/-- On an induced path, the first vertex is adjacent to exactly one interior vertex, namely
the second vertex of the path. -/
private theorem adj_head_interior {H : SimpleGraph V} {r : List V} {a b x : V}
    (hr : IsPathFrom H r a b) (h3 : 3 ≤ r.length) (hx : x ∈ SPGT.interior r) :
    (H.Adj a x ↔ x = r[1]'(by omega)) := by
  have hnd : r.Nodup := hr.1.2.1
  have hpos : 0 < r.length := by omega
  have h0 : r[0]'hpos = a := PathBasics.getElem_zero_of_head? hr.2.1 hpos
  obtain ⟨hxr, hxa, -⟩ := (PathBasics.mem_interior_iff_of_pathFrom hr).mp hx
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hxr
  constructor
  · intro hadj
    have hadj' : H.Adj (r[0]'hpos) (r[i]'hi) := by rw [h0, hri]; exact hadj
    have hd := (PathBasics.path_adj_iff hr.1 hpos hi).mp hadj'
    have hi1 : i = 1 := by omega
    rw [← hri]
    exact hnd.getElem_inj_iff.mpr hi1
  · intro hxe
    rw [hxe, ← h0]
    exact (PathBasics.path_adj_iff hr.1 hpos (by omega)).mpr (Or.inl rfl)

/-- On an induced path, the last vertex is adjacent to exactly one interior vertex, namely the
second-from-last vertex of the path. -/
private theorem adj_last_interior {H : SimpleGraph V} {r : List V} {a b x : V}
    (hr : IsPathFrom H r a b) (h3 : 3 ≤ r.length) (hx : x ∈ SPGT.interior r) :
    (H.Adj b x ↔ x = r[r.length - 2]'(by omega)) := by
  have hnd : r.Nodup := hr.1.2.1
  have hpos : 0 < r.length := by omega
  have hlt : r.length - 1 < r.length := by omega
  have h0 : r[r.length - 1]'hlt = b := PathBasics.getElem_last_of_getLast? hr.2.2 hpos
  obtain ⟨hxr, -, hxb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hr).mp hx
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hxr
  constructor
  · intro hadj
    have hadj' : H.Adj (r[r.length - 1]'hlt) (r[i]'hi) := by rw [h0, hri]; exact hadj
    have hd := (PathBasics.path_adj_iff hr.1 hlt hi).mp hadj'
    have hi1 : i = r.length - 2 := by omega
    rw [← hri]
    exact hnd.getElem_inj_iff.mpr hi1
  · intro hxe
    rw [hxe, ← h0]
    exact (PathBasics.path_adj_iff hr.1 hlt (by omega)).mpr (Or.inr (by omega))

/-! ## Claim (2) -/

/-- **Claim (2) of the proof of 14.3** (printed p. 91).

PAPER: *"There is no anticomponent of `Y` that is complete to `A ∪ D` or `B ∪ C`."*

This is the `A ∪ D` half; the `B ∪ C` half is this one applied to `Gᶜ` (see
`ProofLemmas.CubeComplement`).  Here `(A,B,C,D)` is a maximal cube in `G ∈ F₅` forming `K`,
`F` is the set of minor vertices of `V(G) \ V(K)`, `Y` the set of major ones, and `Y₁` is an
anticomponent of `Y` complete to `A ∪ D`.  The printed argument builds the skew partition
`(L ∪ M, X ∪ A ∪ D ∪ Y₁)` and shows it is balanced, then applies 4.5. -/
theorem cube_claim_two [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D Y : Set V}
    (hG : InF5 G) (hno : ¬ AdmitsBalancedSkewPartition G)
    (hcube : MaximalCube G A B C D)
    (hYdef : Y = {v : V | MajorForCube G A B C D v}) (hYne : Y.Nonempty)
    (Y₁ : Set V) (hY₁ : IsAnticomponent G Y Y₁) (hcomp : Complete G Y₁ (A ∪ D)) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, hAne, hBne, hCne, hDne⟩,
    ⟨-, cBD, aAD, aBC⟩, hsqAB, hsqCD⟩ := hcube.1
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨b₀, hb₀⟩ := hBne
  obtain ⟨c₀, hc₀⟩ := hCne
  obtain ⟨d₀, hd₀⟩ := hDne
  -- the eight non-memberships that keep recurring
  have naCD : a₀ ∉ C ∪ D := fun h => h.elim (Set.disjoint_left.mp dAC ha₀)
    (Set.disjoint_left.mp dAD ha₀)
  have naBD : a₀ ∉ B ∪ D := fun h => h.elim (Set.disjoint_left.mp dAB ha₀)
    (Set.disjoint_left.mp dAD ha₀)
  have ndAB : d₀ ∉ A ∪ B := fun h => h.elim (fun hh => Set.disjoint_left.mp dAD hh hd₀)
    (fun hh => Set.disjoint_left.mp dBD hh hd₀)
  have ndAC : d₀ ∉ A ∪ C := fun h => h.elim (fun hh => Set.disjoint_left.mp dAD hh hd₀)
    (fun hh => Set.disjoint_left.mp dCD hh hd₀)
  -- `Y₁ ⊆ Y` and `Y₁` is nonempty
  have hY₁Y : Y₁ ⊆ Y := hY₁.1
  have hY₁ne : Y₁.Nonempty := ComponentsOfSetBasics.nonempty_of_isComponent Gᶜ hYne hY₁
  -- `D` is anticonnected, and so is `A ∪ D`
  have hDanti : AnticonnectedSet G D :=
    connectedSet_right_of_squareConnected hsqCD ⟨d₀, hd₀⟩
  have hADanti : AnticonnectedSet G (A ∪ D) :=
    anticonnectedSet_union dAD aAD ⟨a₀, ha₀⟩ ⟨d₀, hd₀⟩
  -- every vertex of `C` has a nonneighbour in `D` (it lies in an antisquare)
  have hCnotD : ∀ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d := by
    intro c hc
    obtain ⟨d, hd, hadj⟩ := exists_adj_left hsqCD hc
    exact ⟨d, hd, hadj.2⟩
  -- `Y₁` is disjoint from `A ∪ D`
  have hY₁AD : ∀ y ∈ Y₁, y ∉ A ∪ D := fun y hy hmem => G.irrefl (hcomp y hy y hmem)
  -- ### `F`, `L`, `M`, `X`
  obtain ⟨Fs, hFs⟩ : ∃ S : Set V, S = {v : V | MinorForCube G A B C D v} := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ S : Set V, S = C ∪ {v : V | ∃ P : Set V, IsComponent G Fs P ∧
      (∃ c ∈ C, ∃ f ∈ P, G.Adj c f) ∧ v ∈ P} := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ S : Set V, S = B ∪ {v : V | ∃ P : Set V, IsComponent G Fs P ∧
      ¬ (∃ c ∈ C, ∃ f ∈ P, G.Adj c f) ∧ v ∈ P} := ⟨_, rfl⟩
  obtain ⟨Xs, hX⟩ : ∃ S : Set V, S = {v : V | VertexComplete G v Y₁} \ (L ∪ M) := ⟨_, rfl⟩
  -- basic membership facts
  have hFsmin : ∀ v ∈ Fs, MinorForCube G A B C D v := by
    intro v hv; rw [hFs] at hv; exact hv
  have hFsK : ∀ v ∈ Fs, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hFsmin v hv).1
  have hYK : ∀ v ∈ Y, v ∉ A ∪ B ∪ C ∪ D := by
    intro v hv; rw [hYdef] at hv; exact hv.1
  have hFsYdisj : ∀ v, v ∈ Fs → v ∈ Y → False := by
    intro v hvF hvY
    rw [hYdef] at hvY
    exact not_minor_major hcube.1 (hFsmin v hvF) hvY
  have hLsub : ∀ x ∈ L, x ∈ C ∨ x ∈ Fs := by
    intro x hx
    rw [hL] at hx
    rcases hx with hx | ⟨P, hP, -, hxP⟩
    · exact Or.inl hx
    · exact Or.inr (hP.1 hxP)
  have hMsub : ∀ x ∈ M, x ∈ B ∨ x ∈ Fs := by
    intro x hx
    rw [hM] at hx
    rcases hx with hx | ⟨P, hP, -, hxP⟩
    · exact Or.inl hx
    · exact Or.inr (hP.1 hxP)
  -- ### every vertex is in `V(K)`, `F` or `Y` (this is 14.1)
  have hcover14 : ∀ v : V, v ∈ A ∪ B ∪ C ∪ D ∨ v ∈ Fs ∨ v ∈ Y := by
    intro v
    by_cases hvK : v ∈ A ∪ B ∪ C ∪ D
    · exact Or.inl hvK
    · rcases _root_.Workspace.Statements.S14.SPGT.thm_14_1 G hG A B C D hcube v hvK
        (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) rfl with h | h
      · exact Or.inr (Or.inl (by rw [hFs]; exact ⟨hvK, h.1, h.2⟩))
      · exact Or.inr (Or.inr (by rw [hYdef]; exact ⟨hvK, h.1, h.2⟩))
  -- ### 14.2 applied to the components of `F`
  have hatt : ∀ P : Set V, IsComponent G Fs P →
      (attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
        attachments G P (A ∪ B ∪ C ∪ D) ⊆ C ∪ D ∨
        attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ C ∨
        attachments G P (A ∪ B ∪ C ∪ D) ⊆ B ∪ D) := by
    intro P hP
    exact (_root_.Workspace.Statements.S14.SPGT.thm_14_2 G hG A B C D hcube P
      (fun x hx => hFsK x (hP.1 hx)) hP.2.1 (fun x hx => hFsmin x (hP.1 hx))
      (attachments G P (A ∪ B ∪ C ∪ D)) rfl).1
  have hnoB : ∀ P : Set V, IsComponent G Fs P → (∃ c ∈ C, ∃ f ∈ P, G.Adj c f) →
      ∀ b ∈ B, ∀ f ∈ P, ¬ G.Adj b f := by
    rintro P hP ⟨c, hc, f, hf, hcf⟩ b hb g hg hbg
    have hcatt : c ∈ attachments G P (A ∪ B ∪ C ∪ D) := ⟨Or.inl (Or.inr hc), f, hf, hcf⟩
    have hbatt : b ∈ attachments G P (A ∪ B ∪ C ∪ D) :=
      ⟨Or.inl (Or.inl (Or.inr hb)), g, hg, hbg⟩
    rcases hatt P hP with h | h | h | h
    · exact (h hcatt).elim (fun hh => Set.disjoint_left.mp dAC hh hc)
        (fun hh => Set.disjoint_left.mp dBC hh hc)
    · exact (h hbatt).elim (fun hh => Set.disjoint_left.mp dBC hb hh)
        (fun hh => Set.disjoint_left.mp dBD hb hh)
    · exact (h hbatt).elim (fun hh => Set.disjoint_left.mp dAB hh hb)
        (fun hh => Set.disjoint_left.mp dBC hb hh)
    · exact (h hcatt).elim (fun hh => Set.disjoint_left.mp dBC hh hc)
        (fun hh => Set.disjoint_left.mp dCD hc hh)
  have hnoA : ∀ P : Set V, IsComponent G Fs P → (∃ c ∈ C, ∃ f ∈ P, G.Adj c f) →
      (∃ d ∈ D, ∃ f ∈ P, G.Adj d f) → ∀ a ∈ A, ∀ f ∈ P, ¬ G.Adj a f := by
    rintro P hP ⟨c, hc, f, hf, hcf⟩ ⟨d, hd, e, he, hde⟩ a ha g hg hag
    have hcatt : c ∈ attachments G P (A ∪ B ∪ C ∪ D) := ⟨Or.inl (Or.inr hc), f, hf, hcf⟩
    have hdatt : d ∈ attachments G P (A ∪ B ∪ C ∪ D) := ⟨Or.inr hd, e, he, hde⟩
    have haatt : a ∈ attachments G P (A ∪ B ∪ C ∪ D) :=
      ⟨Or.inl (Or.inl (Or.inl ha)), g, hg, hag⟩
    rcases hatt P hP with h | h | h | h
    · exact (h hcatt).elim (fun hh => Set.disjoint_left.mp dAC hh hc)
        (fun hh => Set.disjoint_left.mp dBC hh hc)
    · exact (h haatt).elim (fun hh => Set.disjoint_left.mp dAC ha hh)
        (fun hh => Set.disjoint_left.mp dAD ha hh)
    · exact (h hdatt).elim (fun hh => Set.disjoint_left.mp dAD hh hd)
        (fun hh => Set.disjoint_left.mp dCD hh hd)
    · exact (h hcatt).elim (fun hh => Set.disjoint_left.mp dBC hh hc)
        (fun hh => Set.disjoint_left.mp dCD hc hh)
  -- ### there are no edges between `L` and `M`
  have hLM : ∀ x ∈ L, ∀ y ∈ M, ¬ G.Adj x y := by
    intro x hx y hy hadj
    rw [hL] at hx
    rw [hM] at hy
    rcases hx with hxC | ⟨P, hP, hPatt, hxP⟩
    · rcases hy with hyB | ⟨Q, hQ, hQatt, hyQ⟩
      · exact aBC y hyB x hxC hadj.symm
      · exact hQatt ⟨x, hxC, y, hyQ, hadj⟩
    · rcases hy with hyB | ⟨Q, hQ, hQatt, hyQ⟩
      · exact hnoB P hP hPatt y hyB x hxP hadj.symm
      · exact ComponentsOfSetBasics.anticomplete_of_isComponent G hP hQ
          (fun he => hQatt (he ▸ hPatt)) x hxP y hyQ hadj
  have hBL : ∀ b ∈ B, ∀ x ∈ L, ¬ G.Adj b x := by
    intro b hb x hx hadj
    rw [hL] at hx
    rcases hx with hxC | ⟨P, hP, hPatt, hxP⟩
    · exact aBC b hb x hxC hadj
    · exact hnoB P hP hPatt b hb x hxP hadj
  -- ### disjointness of the four parts
  have hLK : ∀ x ∈ L, x ∈ C ∨ x ∉ A ∪ B ∪ C ∪ D := by
    intro x hx; rcases hLsub x hx with h | h
    · exact Or.inl h
    · exact Or.inr (hFsK x h)
  have hMK : ∀ x ∈ M, x ∈ B ∨ x ∉ A ∪ B ∪ C ∪ D := by
    intro x hx; rcases hMsub x hx with h | h
    · exact Or.inl h
    · exact Or.inr (hFsK x h)
  have hLA : ∀ x ∈ L, x ∉ A := by
    intro x hx hxA
    rcases hLK x hx with h | h
    · exact Set.disjoint_left.mp dAC hxA h
    · exact h (Or.inl (Or.inl (Or.inl hxA)))
  have hLD : ∀ x ∈ L, x ∉ D := by
    intro x hx hxD
    rcases hLK x hx with h | h
    · exact Set.disjoint_left.mp dCD h hxD
    · exact h (Or.inr hxD)
  have hMA : ∀ x ∈ M, x ∉ A := by
    intro x hx hxA
    rcases hMK x hx with h | h
    · exact Set.disjoint_left.mp dAB hxA h
    · exact h (Or.inl (Or.inl (Or.inl hxA)))
  have hMD : ∀ x ∈ M, x ∉ D := by
    intro x hx hxD
    rcases hMK x hx with h | h
    · exact Set.disjoint_left.mp dBD h hxD
    · exact h (Or.inr hxD)
  have hLY : ∀ x ∈ L, x ∉ Y := by
    intro x hx hxY
    rcases hLsub x hx with h | h
    · exact hYK x hxY (Or.inl (Or.inr h))
    · exact hFsYdisj x h hxY
  have hMY : ∀ x ∈ M, x ∉ Y := by
    intro x hx hxY
    rcases hMsub x hx with h | h
    · exact hYK x hxY (Or.inl (Or.inl (Or.inr h)))
    · exact hFsYdisj x h hxY
  have hLMd : ∀ x, x ∈ L → x ∈ M → False := by
    intro x hxL hxM
    rw [hL] at hxL
    rw [hM] at hxM
    rcases hxL with hxC | ⟨P, hP, hPatt, hxP⟩
    · rcases hxM with hxB | ⟨Q, hQ, -, hxQ⟩
      · exact Set.disjoint_left.mp dBC hxB hxC
      · exact hFsK x (hQ.1 hxQ) (Or.inl (Or.inr hxC))
    · rcases hxM with hxB | ⟨Q, hQ, hQatt, hxQ⟩
      · exact hFsK x (hP.1 hxP) (Or.inl (Or.inl (Or.inr hxB)))
      · have hPQ : P = Q := by
          by_contra hne
          exact (ComponentsOfSetBasics.disjoint_of_isComponent G hP hQ hne).le_bot ⟨hxP, hxQ⟩
        exact hQatt (hPQ ▸ hPatt)
  -- ### no vertex of `L` is `A ∪ D`-complete
  have hLnotAD : ∀ z ∈ L, ¬ VertexComplete G z (A ∪ D) := by
    intro z hz hzc
    rcases hLsub z hz with hzC | hzF
    · obtain ⟨d, hd, hnd⟩ := hCnotD z hzC
      exact hnd (hzc d (Or.inr hd))
    · have hzmin := hFsmin z hzF
      rcases hzmin.2.1 with hsub | hsub | hsub | hsub
      · exact ndAB (hsub ⟨hzc d₀ (Or.inr hd₀), Or.inr hd₀⟩)
      · exact naCD (hsub ⟨hzc a₀ (Or.inl ha₀), Or.inl (Or.inl (Or.inl ha₀))⟩)
      · exact ndAC (hsub ⟨hzc d₀ (Or.inr hd₀), Or.inr hd₀⟩)
      · exact naBD (hsub ⟨hzc a₀ (Or.inl ha₀), Or.inl (Or.inl (Or.inl ha₀))⟩)
  -- ### `(L, D)` is balanced, by 2.6 applied at any vertex of `B`
  have hbalLD : Workspace.Types.Core.SPGT.Balanced G L D := by
    refine _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge L D
      (Set.disjoint_left.mpr (fun x hxL hxD => hLD x hxL hxD)) b₀ ?_ ?_ ?_
    · rintro (hbL | hbD)
      · rcases hLK b₀ hbL with h | h
        · exact Set.disjoint_left.mp dBC hb₀ h
        · exact h (Or.inl (Or.inl (Or.inr hb₀)))
      · exact Set.disjoint_left.mp dBD hb₀ hbD
    · exact fun d hd => cBD b₀ hb₀ d hd
    · exact fun x hx => hBL b₀ hb₀ x hx
  have hY₁D : ∀ y ∈ Y₁, y ∉ D := fun y hy hyD => hY₁AD y hy (Or.inr hyD)
  -- ### PAPER: "Let `u, v ∈ L` be adjacent, and suppose they are joined by an odd antipath `Q₁`
  -- with interior in `Y₁`."  This is the antipath half of `(L, Y₁)` being balanced.
  have hantipath : ∀ (u v : V) (q : List V), u ∈ L → v ∈ L → G.Adj u v →
      IsAntipathFrom G q u v → (∀ x ∈ SPGT.interior q, x ∈ Y₁) → ¬ Odd (pathLength q) := by
    -- PAPER: "So we may assume that `u` is `D`-complete."
    have caseB : ∀ (u v : V) (q : List V), u ∈ L → v ∈ L → G.Adj u v →
        IsAntipathFrom G q u v → (∀ x ∈ SPGT.interior q, x ∈ Y₁) →
        VertexComplete G u D → Odd (pathLength q) → False := by
      intro u v q huL hvL huv hq hint hDu hodd
      -- PAPER: "Hence `u ∉ C`" — every vertex of `C` lies in an antisquare.
      have huC : u ∉ C := by
        intro hcU
        obtain ⟨d, hd, hnd⟩ := hCnotD u hcU
        exact hnd (hDu d hd)
      -- PAPER: "and so `u` belongs to some component `F₁` of `F` with an attachment in `C`."
      have hu' := huL
      rw [hL] at hu'
      rcases hu' with hu' | ⟨P, hP, hPatt, huP⟩
      · exact huC hu'
      have humin := hFsmin u (hP.1 huP)
      -- PAPER: "Since `u` is minor, all its neighbours in `C` are adjacent to all its
      -- neighbours in `D`, and hence it has no neighbours in `C`."
      have hnoCu : ∀ c ∈ C, ¬ G.Adj u c := by
        intro c hc hadj
        obtain ⟨d, hd, hnd⟩ := hCnotD c hc
        exact hnd (humin.2.2 c ⟨⟨hadj, Or.inl (Or.inr hc)⟩, Or.inr hc⟩ d
          ⟨⟨hDu d hd, Or.inr hd⟩, Or.inr hd⟩)
      -- PAPER: "so `v ∈ F₁`."
      have hvP : v ∈ P := by
        have hv' := hvL
        rw [hL] at hv'
        rcases hv' with hvC | ⟨Q, hQ, hQatt, hvQ⟩
        · exact absurd huv (hnoCu v hvC)
        · by_cases hPQ : P = Q
          · rw [hPQ]; exact hvQ
          · exact absurd huv
              (ComponentsOfSetBasics.anticomplete_of_isComponent G hP hQ hPQ u huP v hvQ)
      -- PAPER: "Since `F₁` has an attachment in `C` and in `D` … it follows that `F₁` has no
      -- attachments in `A`, and so `u, v` have no neighbours in `A`."
      have hnoAu := hnoA P hP hPatt ⟨d₀, hd₀, u, huP, (hDu d₀ hd₀).symm⟩
      -- PAPER: "But then `a-u-Q₁-v-a` is an odd antihole (where `a ∈ A`), a contradiction."
      -- That construction is exactly 2.6 for the pair `({u,v}, Y₁)` with the vertex `a₀`.
      refine (_root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge ({u, v} : Set V) Y₁
        ?_ a₀ ?_ ?_ ?_).2 u v q (Or.inl rfl) (Or.inr rfl) huv hq hint hodd
      · refine Set.disjoint_left.mpr ?_
        rintro x (rfl | rfl) hxY
        · exact hLY x huL (hY₁Y hxY)
        · exact hLY x hvL (hY₁Y hxY)
      · rintro ((h | h) | h)
        · exact hLA u huL (by rw [← h]; exact ha₀)
        · exact hLA v hvL (by rw [← h]; exact ha₀)
        · exact hY₁AD a₀ h (Or.inl ha₀)
      · exact fun y hy => (hcomp y hy a₀ (Or.inl ha₀)).symm
      · rintro x (rfl | rfl)
        · exact hnoAu a₀ ha₀ x huP
        · exact hnoAu a₀ ha₀ x hvP
    intro u v q huL hvL huv hq hint hodd
    by_cases hDu : VertexComplete G u D
    · exact caseB u v q huL hvL huv hq hint hDu hodd
    by_cases hDv : VertexComplete G v D
    · refine caseB v u q.reverse hvL huL huv.symm (PathBasics.isPathFrom_reverse hq) ?_ hDv ?_
      · intro x hx
        rw [PathBasics.interior_reverse, List.mem_reverse] at hx
        exact hint x hx
      · have he : pathLength q.reverse = pathLength q := by
          simp only [SPGT.pathLength, List.length_reverse]
        rw [he]; exact hodd
    -- PAPER: "If they both have nonneighbours in `D`, then since `D` is anticonnected they are
    -- also joined by an antipath `Q₂` with interior in `D`."
    have hu' : ∃ d ∈ D, ¬ G.Adj u d := by
      by_contra hc
      push Not at hc
      exact hDu (fun d hd => hc d hd)
    have hv' : ∃ d ∈ D, ¬ G.Adj v d := by
      by_contra hc
      push Not at hc
      exact hDv (fun d hd => hc d hd)
    obtain ⟨q₂, hq₂, hq₂int⟩ := InducedPathExtraction.exists_antipath_interior_in hDanti
      (hLD u huL) (hLD v hvL) hu' hv'
    have hnadjc : ¬ Gᶜ.Adj u v := fun h => h.2 huv
    -- `Q₂` has at least three vertices
    have hq₂pos : 0 < q₂.length := PathBasics.path_length_pos hq₂.1
    have hq₂len : 3 ≤ q₂.length := by
      by_contra hc
      have h2 : q₂.length = 1 ∨ q₂.length = 2 := by omega
      rcases h2 with h2 | h2
      · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h2
        rw [ha] at hq₂
        have hu2 : a = u := by simpa using hq₂.2.1
        have hv2 : a = v := by simpa using hq₂.2.2
        exact huv.ne (hu2.symm.trans hv2)
      · exact hnadjc (PathBasics.isPathFrom_ends_adj_of_length_one hq₂
          (by rw [PathBasics.pathLength_eq]; omega))
    -- `Q₁` has at least four vertices
    have hqpos : 0 < q.length := PathBasics.path_length_pos hq.1
    have hqlen : 4 ≤ q.length := by
      obtain ⟨k, hk⟩ := hodd
      rw [PathBasics.pathLength_eq] at hk
      by_contra hc
      have h2 : q.length = 1 ∨ q.length = 2 := by omega
      rcases h2 with h2 | h2
      · omega
      · exact hnadjc (PathBasics.isPathFrom_ends_adj_of_length_one hq
          (by rw [PathBasics.pathLength_eq]; omega))
    -- PAPER: "which is also odd since its union with `Q₁` is an antihole"
    have hintq₂ : IsPathFrom Gᶜ (SPGT.interior q₂) (q₂[1]'(by omega))
        (q₂[q₂.length - 2]'(by omega)) := PathGlue.isPathFrom_interior hq₂.1 hq₂len
    have hRev := PathBasics.isPathFrom_reverse hintq₂
    have hhole : IsHoleList Gᶜ (q ++ (SPGT.interior q₂).reverse) := by
      refine PathGlue.glue_hole hq hRev ?_ ?_ ?_
      · intro x hxq hxr
        rw [List.mem_reverse] at hxr
        have hxD : x ∈ D := hq₂int x hxr
        by_cases hxu : x = u
        · exact hLD u huL (by rw [← hxu]; exact hxD)
        by_cases hxv : x = v
        · exact hLD v hvL (by rw [← hxv]; exact hxD)
        · exact hY₁D x (hint x ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr
            ⟨hxq, hxu, hxv⟩)) hxD
      · intro x hxq y hyr
        rw [List.mem_reverse] at hyr
        have hyD : y ∈ D := hq₂int y hyr
        by_cases hxu : x = u
        · have hhead := adj_head_interior hq₂ hq₂len hyr
          constructor
          · intro hadj
            exact Or.inr ⟨hxu, hhead.mp (by rw [← hxu]; exact hadj)⟩
          · rintro (⟨hxv, -⟩ | ⟨-, hy1⟩)
            · exact absurd (hxu.symm.trans hxv) huv.ne
            · rw [hxu]; exact hhead.mpr hy1
        by_cases hxv : x = v
        · have hlast := adj_last_interior hq₂ hq₂len hyr
          constructor
          · intro hadj
            exact Or.inl ⟨hxv, hlast.mp (by rw [← hxv]; exact hadj)⟩
          · rintro (⟨-, hy1⟩ | ⟨hxu', -⟩)
            · rw [hxv]; exact hlast.mpr hy1
            · exact absurd (hxv.symm.trans hxu') (fun h => huv.ne h.symm)
        · have hxY : x ∈ Y₁ :=
            hint x ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hxq, hxu, hxv⟩)
          constructor
          · intro hadj
            exact absurd (hcomp x hxY y (Or.inr hyD)) hadj.2
          · rintro (⟨h, -⟩ | ⟨h, -⟩)
            · exact absurd h hxv
            · exact absurd h hxu
      · simp only [List.length_reverse]
        omega
    have heven : Even (holeLength (q ++ (SPGT.interior q₂).reverse)) := hBerge.2 _ hhole
    have hodd₂ : Odd (pathLength q₂) := by
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff] at hodd ⊢
      simp only [SPGT.holeLength, List.length_append, List.length_reverse,
        PathBasics.interior_length] at heven
      rw [PathBasics.pathLength_eq] at hodd ⊢
      omega
    -- PAPER: "contradicting that `(L, D)` is balanced"
    exact hbalLD.2 u v q₂ huL hvL huv hq₂ hq₂int hodd₂
  -- ### PAPER: "Next suppose there exist nonadjacent `u, v ∈ Y₁`, joined by an odd path `P`
  -- with interior in `L`."  This is the path half of `(L, Y₁)` being balanced.
  have hpathhalf : ∀ (u v : V) (p : List V), u ∈ Y₁ → v ∈ Y₁ → ¬ G.Adj u v →
      IsPathFrom G p u v → (∀ x ∈ SPGT.interior p, x ∈ L) → ¬ Odd (pathLength p) := by
    intro u v p hu hv hnadj hp hint hodd
    have hplen : p.length = pathLength p + 1 := PathBasics.length_eq_pathLength_add_one hp.1
    have hne1 : pathLength p ≠ 1 := fun h =>
      hnadj (PathBasics.isPathFrom_ends_adj_of_length_one hp h)
    -- PAPER: "By what we just proved about odd antipaths, it follows that `P` has length ≥ 5."
    have hne3 : pathLength p ≠ 3 := by
      intro h3
      have h4 : p.length = 4 := by omega
      obtain ⟨x0, x1, x2, x3, hpe⟩ := PathGlue.length_eq_four h4
      subst hpe
      have hpl := hp.1
      have hnd : ([x0, x1, x2, x3] : List V).Nodup := hpl.2.1
      have hu0 : x0 = u := by simpa using hp.2.1
      have hv3 : x3 = v := by simpa using hp.2.2
      have e01 : G.Adj x0 x1 :=
        (PathBasics.path_adj_iff hpl (i := 0) (j := 1) (by simp) (by simp)).mpr (Or.inl rfl)
      have e12 : G.Adj x1 x2 :=
        (PathBasics.path_adj_iff hpl (i := 1) (j := 2) (by simp) (by simp)).mpr (Or.inl rfl)
      have e23 : G.Adj x2 x3 :=
        (PathBasics.path_adj_iff hpl (i := 2) (j := 3) (by simp) (by simp)).mpr (Or.inl rfl)
      have n02 : ¬ G.Adj x0 x2 := by
        intro h
        have := (PathBasics.path_adj_iff hpl (i := 0) (j := 2) (by simp) (by simp)).mp h
        omega
      have n03 : ¬ G.Adj x0 x3 := by
        intro h
        have := (PathBasics.path_adj_iff hpl (i := 0) (j := 3) (by simp) (by simp)).mp h
        omega
      have n13 : ¬ G.Adj x1 x3 := by
        intro h
        have := (PathBasics.path_adj_iff hpl (i := 1) (j := 3) (by simp) (by simp)).mp h
        omega
      have d01 : x0 ≠ x1 := by rintro rfl; simp at hnd
      have d02 : x0 ≠ x2 := by rintro rfl; simp at hnd
      have d03 : x0 ≠ x3 := by rintro rfl; simp at hnd
      have d12 : x1 ≠ x2 := by rintro rfl; simp at hnd
      have d13 : x1 ≠ x3 := by rintro rfl; simp at hnd
      have d23 : x2 ≠ x3 := by rintro rfl; simp at hnd
      have hpl4 : IsPathList Gᶜ [x1, x3, x0, x2] :=
        PathGlue.isPathList_four
          (by simp [d13, d12, d02, Ne.symm d01, Ne.symm d03, Ne.symm d23])
          ⟨d13, n13⟩ ⟨Ne.symm d03, fun h => n03 h.symm⟩ ⟨d02, n02⟩
          (fun h => h.2 e01.symm) (fun h => h.2 e12) (fun h => h.2 e23.symm)
      have hantip : IsAntipathFrom G [x1, x3, x0, x2] x1 x2 := ⟨hpl4, by simp, by simp⟩
      have hintq : ∀ z ∈ SPGT.interior ([x1, x3, x0, x2] : List V), z ∈ Y₁ := by
        intro z hz
        have hzz : z = x3 ∨ z = x0 := by
          simpa [show SPGT.interior ([x1, x3, x0, x2] : List V) = [x3, x0] from rfl] using hz
        rcases hzz with h | h
        · rw [h, hv3]; exact hv
        · rw [h, hu0]; exact hu
      have hx1L : x1 ∈ L := hint x1
        (by simp [show SPGT.interior ([x0, x1, x2, x3] : List V) = [x1, x2] from rfl])
      have hx2L : x2 ∈ L := hint x2
        (by simp [show SPGT.interior ([x0, x1, x2, x3] : List V) = [x1, x2] from rfl])
      exact hantipath x1 x2 [x1, x3, x0, x2] hx1L hx2L e12 hantip hintq ⟨1, rfl⟩
    have h5 : 5 ≤ pathLength p := by obtain ⟨k, hk⟩ := hodd; omega
    -- PAPER: "Now `A ∪ D` is anticonnected, and there is no `A ∪ D`-complete vertex in `L` …
    -- Hence the ends of `P` are `A ∪ D`-complete and its internal vertices are not.  But this
    -- contradicts 13.6."
    have hXP : (A ∪ D) ⊆ {w : V | w ∈ p}ᶜ := by
      intro z hz hzp
      by_cases hzu : z = u
      · exact hY₁AD u hu (by rw [← hzu]; exact hz)
      by_cases hzv : z = v
      · exact hY₁AD v hv (by rw [← hzv]; exact hz)
      · have hzL := hint z ((PathBasics.mem_interior_iff_of_pathFrom hp).mpr ⟨hzp, hzu, hzv⟩)
        rcases hz with hzA | hzD
        · exact hLA z hzL hzA
        · exact hLD z hzL hzD
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG p u v hp hodd (A ∪ D) hXP
      hADanti (hcomp u hu) (hcomp v hv) with ⟨u', hu'p, v', hv'p, hedge⟩ | ⟨h3, -⟩
    · have key : ∀ w, w ∈ p → VertexComplete G w (A ∪ D) → w = u ∨ w = v := by
        intro w hw hwc
        by_contra hc
        push Not at hc
        exact hLnotAD w
          (hint w ((PathBasics.mem_interior_iff_of_pathFrom hp).mpr ⟨hw, hc.1, hc.2⟩)) hwc
      have hadj' : G.Adj u' v' := hedge.1
      rcases key u' hu'p hedge.2.1 with h | h <;> rcases key v' hv'p hedge.2.2 with h' | h' <;>
        rw [h, h'] at hadj'
      · exact G.irrefl hadj'
      · exact hnadj hadj'
      · exact hnadj hadj'.symm
      · exact G.irrefl hadj'
    · omega
  -- ### PAPER: "it follows that `(L ∪ M, X ∪ A ∪ D ∪ Y₁)` is a skew partition of `G` … We claim
  -- it is balanced. … By 4.5, `G` admits a balanced skew partition, a contradiction."
  refine hno (_root_.Workspace.Statements.S04.SPGT.thm_4_5 G hBerge (Xs ∪ A ∪ D) Y₁ L M
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Or.inr (Or.inr ⟨hpathhalf, hantipath⟩)))
  · -- the four sets cover `V(G)`
    refine Set.eq_univ_of_forall (fun v => ?_)
    rcases hcover14 v with hvK | hvF | hvY
    · rcases hvK with ((hvA | hvB) | hvC) | hvD
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hvA))))
      · exact Or.inr (by rw [hM]; exact Or.inl hvB)
      · exact Or.inl (Or.inr (by rw [hL]; exact Or.inl hvC))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hvD)))
    · obtain ⟨P, hP, hvP⟩ := ComponentsOfSetBasics.exists_isComponent_mem G Fs hvF
      by_cases hPatt : ∃ c ∈ C, ∃ f ∈ P, G.Adj c f
      · exact Or.inl (Or.inr (by rw [hL]; exact Or.inr ⟨P, hP, hPatt, hvP⟩))
      · exact Or.inr (by rw [hM]; exact Or.inr ⟨P, hP, hPatt, hvP⟩)
    · by_cases hvY₁ : v ∈ Y₁
      · exact Or.inl (Or.inl (Or.inr hvY₁))
      · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))
        rw [hX]
        exact ⟨LooseSkewPartition.vertexComplete_of_notMem_anticomponent hY₁ hvY hvY₁,
          fun hc => hc.elim (fun h => hLY v h hvY) (fun h => hMY v h hvY)⟩
  · refine Set.disjoint_left.mpr ?_
    rintro x ((hxX | hxA) | hxD) hxY
    · rw [hX] at hxX; exact G.irrefl (hxX.1 x hxY)
    · exact hY₁AD x hxY (Or.inl hxA)
    · exact hY₁AD x hxY (Or.inr hxD)
  · refine Set.disjoint_left.mpr ?_
    rintro x ((hxX | hxA) | hxD) hxL
    · rw [hX] at hxX; exact hxX.2 (Or.inl hxL)
    · exact hLA x hxL hxA
    · exact hLD x hxL hxD
  · refine Set.disjoint_left.mpr ?_
    rintro x ((hxX | hxA) | hxD) hxM
    · rw [hX] at hxX; exact hxX.2 (Or.inr hxM)
    · exact hMA x hxM hxA
    · exact hMD x hxM hxD
  · exact Set.disjoint_left.mpr (fun x hxY hxL => hLY x hxL (hY₁Y hxY))
  · exact Set.disjoint_left.mpr (fun x hxY hxM => hMY x hxM (hY₁Y hxY))
  · exact Set.disjoint_left.mpr (fun x hxL hxM => hLMd x hxL hxM)
  · exact ⟨a₀, Or.inl (Or.inr ha₀)⟩
  · exact hY₁ne
  · exact ⟨c₀, by rw [hL]; exact Or.inl hc₀⟩
  · exact ⟨b₀, by rw [hM]; exact Or.inl hb₀⟩
  · exact hLM
  · rintro x ((hxX | hxA) | hxD) y hy
    · rw [hX] at hxX; exact hxX.1 y hy
    · exact (hcomp y hy x (Or.inl hxA)).symm
    · exact (hcomp y hy x (Or.inr hxD)).symm

end Workspace.ProofLemmas.CubeClaimTwo
