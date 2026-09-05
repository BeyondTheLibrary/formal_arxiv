import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.StripSystemNeighbourhood
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.Thm86ClaimTwo

/-!
# The selected-strip separation data in the proof of 8.6

This packages the properties of the sets obtained by selecting a strip that has
two distinct rungs, or receives an attachment from an outside component.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.SelectedStripSeparationData

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

/-! ## Reachability inside a fixed set -/

section Reach

variable {V : Type*} {G : SimpleGraph V} {B : Set V}

/-- `x` and `y` lie in `B` and are joined by a walk of `G|B`. -/
private def ReachIn (G : SimpleGraph V) (B : Set V) (x y : V) : Prop :=
  ∃ (hx : x ∈ B) (hy : y ∈ B), (G.induce B).Reachable ⟨x, hx⟩ ⟨y, hy⟩

private theorem reachIn_refl {x : V} (hx : x ∈ B) : ReachIn G B x x :=
  ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

private theorem reachIn_symm {x y : V} (h : ReachIn G B x y) : ReachIn G B y x := by
  obtain ⟨hx, hy, r⟩ := h
  exact ⟨hy, hx, r.symm⟩

private theorem reachIn_trans {x y z : V} (h₁ : ReachIn G B x y) (h₂ : ReachIn G B y z) :
    ReachIn G B x z := by
  obtain ⟨hx, hy, r₁⟩ := h₁
  obtain ⟨hy', hz, r₂⟩ := h₂
  exact ⟨hx, hz, r₁.trans r₂⟩

private theorem reachIn_of_adj {x y : V} (hx : x ∈ B) (hy : y ∈ B) (hadj : G.Adj x y) :
    ReachIn G B x y :=
  ⟨hx, hy, SimpleGraph.Adj.reachable
    (show (G.induce B).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hadj)⟩

private theorem reachIn_of_connected {C : Set V} (hCB : C ⊆ B) (hC : ConnectedSet G C)
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) : ReachIn G B x y := by
  refine ⟨hCB hx, hCB hy, ?_⟩
  obtain ⟨w⟩ := hC ⟨x, hx⟩ ⟨y, hy⟩
  exact ⟨SimpleGraph.Walk.map
    (⟨fun z => ⟨z.1, hCB z.2⟩, fun {_ _} hab => hab⟩ : (G.induce C) →g (G.induce B)) w⟩

private theorem connectedSet_of_reachIn (h : ∀ x ∈ B, ∀ y ∈ B, ReachIn G B x y) :
    ConnectedSet G B := by
  intro a b
  obtain ⟨ha, hb, r⟩ := h a.1 a.2 b.1 b.2
  exact r

end Reach

/-! ## A connected subset of a path that contains both ends is the whole path -/

section PathSubset

variable {V : Type*} {G : SimpleGraph V}

/-- If `C` is a connected subset of the vertex set of a path `p` and contains both ends of
`p`, then `C` is all of `V(p)`. -/
private theorem path_subset_of_connected {p : List V} {a₁ a₂ : V}
    (hp : IsPathFrom G p a₁ a₂) {C : Set V} (hCsub : C ⊆ {v : V | v ∈ p})
    (hC : ConnectedSet G C) (h₁ : a₁ ∈ C) (h₂ : a₂ ∈ C) : {v : V | v ∈ p} ⊆ C := by
  classical
  have hlen : 0 < p.length := PathBasics.path_length_pos hp.1
  have hzero : p[0]'hlen = a₁ := PathBasics.getElem_zero_of_head? hp.2.1 hlen
  have hlast : p[p.length - 1]'(by omega) = a₂ :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hlen
  intro x hx
  by_contra hxC
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  subst hxi
  -- `i` is neither the first nor the last index
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact absurd (hzero ▸ h₁) hxC
    · exact h
  have hilast : i < p.length - 1 := by
    rcases Nat.lt_or_ge i (p.length - 1) with h | h
    · exact h
    · have : i = p.length - 1 := by omega
      subst this
      exact absurd (hlast ▸ h₂) hxC
  set P : Set V := {v : V | ∃ j, ∃ _ : j < p.length, j < i ∧ v = p[j]} with hP
  set Q : Set V := {v : V | ∃ j, ∃ _ : j < p.length, i < j ∧ v = p[j]} with hQ
  have hPQ : Anticomplete G P Q := by
    rintro a ⟨j, hj, hji, rfl⟩ b ⟨k, hk, hik, rfl⟩
    exact PathBasics.path_not_adj_of_gap hp.1 hj hk (by omega) (by omega)
  have hsub : C ⊆ P ∪ Q := by
    intro c hc
    obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.mp (hCsub hc)
    have hji : j ≠ i := by
      rintro rfl
      exact hxC (hcj ▸ hc)
    rcases Nat.lt_or_ge j i with h | h
    · exact Or.inl ⟨j, hj, h, hcj.symm⟩
    · exact Or.inr ⟨j, hj, by omega, hcj.symm⟩
  have ha₁P : a₁ ∈ P := ⟨0, hlen, hi0, hzero.symm⟩
  have hCP : C ⊆ P :=
    StripSystemNeighbourhood.connectedSet_subset_of_anticomplete hPQ hC hsub h₁ ha₁P
  obtain ⟨k, hk, hki, hak⟩ := hCP h₂
  have : k = p.length - 1 := by
    have hnd := PathBasics.path_nodup hp.1
    have heq : p[k]'hk = p[p.length - 1]'(by omega) := by rw [← hak, hlast]
    exact hnd.getElem_inj_iff.mp heq
  omega

end PathSubset

/-! ## The core statement -/

private theorem core {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hS : IsJStripSystem G J S N)
    (Z : Set V) (hZ : Z = (stripSystemVertices J S)ᶜ)
    (hLocal : ∀ F : Set V, IsComponent G Z F → F.Nonempty →
      ∃! T : Set V,
        IsStripOfStripSystem J S T ∧
          (attachments G F (stripSystemVertices J S)).Nonempty ∧
          attachments G F (stripSystemVertices J S) ⊆ T ∧
          ∀ v : U, ¬ attachments G F (stripSystemVertices J S) ⊆ N v)
    (b₁ b₂ : U) (hb₁b₂ : J.Adj b₁ b₂)
    (hselected :
      (∃ R₁ R₂ : List V,
        IsUVRung G J S N b₁ b₂ R₁ ∧ IsUVRung G J S N b₁ b₂ R₂ ∧
          ({x : V | x ∈ R₁} : Set V) ≠ {x : V | x ∈ R₂}) ∨
      ∃ F : Set V, IsComponent G Z F ∧
        (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty)
    (A B A₁ A₂ B₁ B₂ : Set V)
    (hA : A = S b₁ b₂ ∪
      ⋃ (F : Set V) (_ : IsComponent G Z F ∧
        (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty), F)
    (hBdef : B = Set.univ \ A)
    (hA₁ : A₁ = N b₁ ∩ S b₁ b₂) (hA₂ : A₂ = N b₂ ∩ S b₁ b₂)
    (hB₁ : B₁ = N b₁ \ A₁) (hB₂ : B₂ = N b₂ \ A₂) :
    A ∪ B = Set.univ ∧ Disjoint A B ∧
    A₁.Nonempty ∧ A₁ ⊆ A ∧ A₂.Nonempty ∧ A₂ ⊆ A ∧
    B₁.Nonempty ∧ B₁ ⊆ B ∧ 2 ≤ B₁.ncard ∧
    B₂.Nonempty ∧ B₂ ⊆ B ∧ 2 ≤ B₂.ncard ∧
    (∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ ((a ∈ A₁ ∧ b ∈ B₁) ∨ (a ∈ A₂ ∧ b ∈ B₂))) ∧
    (∀ C : Set V, IsComponent G A C →
      (C ∩ A₁).Nonempty ∧ (C ∩ A₂).Nonempty) ∧
    ConnectedSet G B ∧ (B ∩ B₁).Nonempty ∧ (B ∩ B₂).Nonempty ∧
    2 ≤ A.ncard ∧ (B \ (B₁ ∪ B₂)).Nonempty ∧
    (∀ a₁ a₂ : V, A₁ = {a₁} → A₂ = {a₂} →
      ¬ ∃ p : List V, IsPathFrom G p a₁ a₂ ∧ {v : V | v ∈ p} = A) := by
  classical
  have hb₂b₁ : J.Adj b₂ b₁ := hb₁b₂.symm
  have hSsymm : S b₂ b₁ = S b₁ b₂ := (StripSystemBasics.strip_symm hS hb₁b₂).symm
  -- membership unfoldings
  have hmemA : ∀ x : V, x ∈ A ↔ (x ∈ S b₁ b₂ ∨ ∃ F : Set V,
      (IsComponent G Z F ∧
        (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty) ∧ x ∈ F) := by
    intro x
    rw [hA]
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
  have hmemB : ∀ x : V, x ∈ B ↔ x ∉ A := by
    intro x; rw [hBdef]; simp
  -- vertices of the strip system are not in `Z`
  have hZW : ∀ x : V, x ∈ stripSystemVertices J S → x ∉ Z := by
    intro x hx; rw [hZ]; simpa using hx
  -- a strip on an edge other than `b₁b₂` lies in `B`
  have hstripB : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(b₁, b₂) → S u v ⊆ B := by
    intro u v huv hne x hx
    rw [hmemB, hmemA]
    push_neg
    refine ⟨fun hc => ?_, fun F hF hxF => ?_⟩
    · exact (Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hS huv hb₁b₂ hne) hx) hc
    · exact hZW x (StripSystemBasics.strip_subset_vertices huv hx) (hF.1.1 hxF)
  -- the third-neighbour lemma
  have hthird : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(b₁, b₂) →
      ∃ w : U, J.Adj u w ∧ w ≠ v ∧ s(u, w) ≠ s(b₁, b₂) := by
    intro u v huv hne
    have h3 : 3 ≤ (J.neighborSet u).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ u
    by_cases hu1 : u = b₁
    · subst hu1
      obtain ⟨w, hw, hwv, hwb⟩ := Thm86ClaimTwo.exists_mem_ne_two h3 v b₂
      refine ⟨w, hw, hwv, fun hcon => ?_⟩
      rcases Sym2.eq_iff.mp hcon with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hwb h2
      · exact hb₁b₂.ne h1
    · by_cases hu2 : u = b₂
      · subst hu2
        obtain ⟨w, hw, hwv, hwb⟩ := Thm86ClaimTwo.exists_mem_ne_two h3 v b₁
        refine ⟨w, hw, hwv, fun hcon => ?_⟩
        rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hu1 h1
        · exact hwb h2
      · obtain ⟨w, hw, hwv⟩ :=
          Set.exists_ne_of_one_lt_ncard (s := J.neighborSet u) (by omega) v
        refine ⟨w, hw, hwv, fun hcon => ?_⟩
        rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hu1 h1
        · exact hu2 h1
  -- every vertex of `J` has an incident edge other than `b₁b₂`
  have hedge : ∀ u : U, ∃ v : U, J.Adj u v ∧ s(u, v) ≠ s(b₁, b₂) := by
    intro u
    have h3 : 3 ≤ (J.neighborSet u).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ u
    by_cases hu1 : u = b₁
    · subst hu1
      obtain ⟨w, hw, hwb⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := J.neighborSet u) (by omega) b₂
      refine ⟨w, hw, fun hcon => ?_⟩
      rcases Sym2.eq_iff.mp hcon with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hwb h2
      · exact hb₁b₂.ne h1
    · by_cases hu2 : u = b₂
      · subst hu2
        obtain ⟨w, hw, hwb⟩ :=
          Set.exists_ne_of_one_lt_ncard (s := J.neighborSet u) (by omega) b₁
        refine ⟨w, hw, fun hcon => ?_⟩
        rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hu1 h1
        · exact hwb h2
      · obtain ⟨w, hw⟩ := SubdivisionCounting.exists_adj_of_three_connected J hJ u
        refine ⟨w, hw, fun hcon => ?_⟩
        rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hu1 h1
        · exact hu2 h1
  -- rung vertex sets are connected
  have hrungconn : ∀ (u v : U) (R : List V), IsUVRung G J S N u v R →
      ConnectedSet G {x : V | x ∈ R} := by
    intro u v R hR
    obtain ⟨s, t, hp, -, -⟩ := StripSystemBasics.rung_isPath hR
    exact KiteTailBasics.connectedSet_of_isPathList hp.1
  -- reachability between rung ends meeting at a common vertex of `J`
  have hends : ∀ u v v' : U, J.Adj u v → J.Adj u v' →
      s(u, v) ≠ s(b₁, b₂) → s(u, v') ≠ s(b₁, b₂) →
      ∀ x ∈ stripSystemNuv S N u v, ∀ x' ∈ stripSystemNuv S N u v', ReachIn G B x x' := by
    intro u v v' huv huv' hne hne' x hx x' hx'
    by_cases hvv' : v = v'
    · subst hvv'
      obtain ⟨w, huw, hwv, hnew⟩ := hthird u v huv hne
      obtain ⟨y, hy⟩ := StripSystemBasics.Nuv_nonempty hS huw
      have hyB : y ∈ B := hstripB u w huw hnew hy.2
      refine reachIn_trans (reachIn_of_adj (hstripB u v huv hne hx.2) hyB ?_)
        (reachIn_of_adj hyB (hstripB u v huv hne hx'.2) ?_)
      · exact StripSystemBasics.Nuv_complete hS huv huw (Ne.symm hwv) x hx y hy
      · exact (StripSystemBasics.Nuv_complete hS huv huw (Ne.symm hwv) x' hx' y hy).symm
    · exact reachIn_of_adj (hstripB u v huv hne hx.2) (hstripB u v' huv' hne' hx'.2)
        (StripSystemBasics.Nuv_complete hS huv huv' hvv' x hx x' hx')
  -- every vertex of a strip off `b₁b₂` reaches every rung end at `u`
  have hstripReach : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(b₁, b₂) → ∀ x ∈ S u v,
      ∀ v' : U, J.Adj u v' → s(u, v') ≠ s(b₁, b₂) →
      ∀ y ∈ stripSystemNuv S N u v', ReachIn G B x y := by
    intro u v huv hne x hx v' huv' hne' y hy
    obtain ⟨R, hR, hxR⟩ := StripSystemBasics.exists_rung hS huv hx
    obtain ⟨s, hsR, hsS, hsN, -⟩ := StripSystemBasics.exists_rung_head hR
    have hRB : {z : V | z ∈ R} ⊆ B := fun z hz =>
      hstripB u v huv hne (StripSystemBasics.rung_subset_strip hR z hz)
    refine reachIn_trans (reachIn_of_connected hRB (hrungconn u v R hR) hxR hsR) ?_
    exact hends u v v' huv huv' hne hne' s ⟨hsN, hsS⟩ y hy
  -- base points, one per vertex of `J`
  choose m hm hmne using hedge
  have hgpt : ∀ u : U, ∃ x : V, x ∈ stripSystemNuv S N u (m u) := fun u =>
    StripSystemBasics.Nuv_nonempty hS (hm u)
  choose g hg using hgpt
  have hgB : ∀ u : U, g u ∈ B := fun u => hstripB u (m u) (hm u) (hmne u) (hg u).2
  have hstep : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(b₁, b₂) → ReachIn G B (g u) (g v) := by
    intro u v huv hne
    obtain ⟨R, hR⟩ := StripSystemBasics.exists_uvRung hS huv
    obtain ⟨s, hsR, hsS, hsN, -⟩ := StripSystemBasics.exists_rung_head hR
    obtain ⟨t, htR, htS, htN, -⟩ := StripSystemBasics.exists_rung_last hR
    have hne' : s(v, u) ≠ s(b₁, b₂) := by
      intro hc; apply hne; rw [← hc]; exact Sym2.eq_swap
    have hRB : {z : V | z ∈ R} ⊆ B := fun z hz =>
      hstripB u v huv hne (StripSystemBasics.rung_subset_strip hR z hz)
    have hh1 : ReachIn G B (g u) s :=
      hends u (m u) v (hm u) huv (hmne u) hne (g u) (hg u) s ⟨hsN, hsS⟩
    have hh2 : ReachIn G B s t := reachIn_of_connected hRB (hrungconn u v R hR) hsR htR
    have htS' : t ∈ S v u := by rw [← StripSystemBasics.strip_symm hS huv]; exact htS
    have hh3 : ReachIn G B t (g v) :=
      hends v u (m v) huv.symm (hm v) hne' (hmne v) t ⟨htN, htS'⟩ (g v) (hg v)
    exact reachIn_trans hh1 (reachIn_trans hh2 hh3)
  -- `J` with the edge `b₁b₂` deleted is still connected
  have hJdadj : ∀ u v : U, (J.deleteEdges {s(b₁, b₂)}).Adj u v ↔
      (J.Adj u v ∧ s(u, v) ≠ s(b₁, b₂)) := by
    intro u v
    simp [SimpleGraph.deleteEdges_adj]
  have hJdreach : ∀ u v : U, (J.deleteEdges {s(b₁, b₂)}).Reachable u v := by
    have step : ∀ x y : U, x ≠ b₁ → y ≠ b₁ →
        (J.deleteEdges {s(b₁, b₂)}).Reachable x y := by
      intro x y hx hy
      have hc := hJ.2 ({b₁} : Set U) (by rw [Set.ncard_singleton]; omega)
      have hxm : x ∈ (({b₁} : Set U)ᶜ) := by simpa using hx
      have hym : y ∈ (({b₁} : Set U)ᶜ) := by simpa using hy
      obtain ⟨w⟩ := hc.preconnected ⟨x, hxm⟩ ⟨y, hym⟩
      refine ⟨SimpleGraph.Walk.map
        (⟨fun z => (z : U), fun {a b} hab => ?_⟩ :
          (J.induce (({b₁} : Set U)ᶜ)) →g (J.deleteEdges {s(b₁, b₂)})) w⟩
      have hab' : J.Adj (a : U) (b : U) := hab
      refine (hJdadj _ _).mpr ⟨hab', fun hcon => ?_⟩
      rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact a.2 (by simp [h1])
      · exact b.2 (by simp [h2])
    have esc : ∀ u : U, ∃ x : U, x ≠ b₁ ∧ (J.deleteEdges {s(b₁, b₂)}).Reachable u x := by
      intro u
      by_cases hu : u = b₁
      · subst hu
        have h3 : 3 ≤ (J.neighborSet u).ncard :=
          SubdivisionCounting.three_le_degree_of_three_connected J hJ u
        obtain ⟨w, hw, hwb⟩ :=
          Set.exists_ne_of_one_lt_ncard (s := J.neighborSet u) (by omega) b₂
        have hadj : J.Adj u w := hw
        refine ⟨w, fun hcc => hadj.ne hcc.symm, SimpleGraph.Adj.reachable ?_⟩
        refine (hJdadj _ _).mpr ⟨hadj, fun hcon => ?_⟩
        rcases Sym2.eq_iff.mp hcon with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hwb h2
        · exact hb₁b₂.ne h1
      · exact ⟨u, hu, SimpleGraph.Reachable.refl u⟩
    intro u v
    obtain ⟨x, hx, hux⟩ := esc u
    obtain ⟨y, hy, hvy⟩ := esc v
    exact (hux.trans (step x y hx hy)).trans hvy.symm
  have hallg : ∀ u v : U, ReachIn G B (g u) (g v) := by
    intro u v
    obtain ⟨w⟩ := hJdreach u v
    induction w with
    | nil => exact reachIn_refl (hgB _)
    | cons hadj p ih =>
        exact reachIn_trans
          (hstep _ _ ((hJdadj _ _).mp hadj).1 ((hJdadj _ _).mp hadj).2) ih
  -- description of `B`
  have hmemB' : ∀ x : V, x ∈ B →
      (x ∈ stripSystemVertices J S ∧ x ∉ S b₁ b₂) ∨ x ∈ Z := by
    intro x hx
    by_cases hxW : x ∈ stripSystemVertices J S
    · exact Or.inl ⟨hxW, fun hc => (hmemB x).mp hx ((hmemA x).mpr (Or.inl hc))⟩
    · right; rw [hZ]; simpa using hxW
  have hBreach : ∀ x ∈ B, ∃ u : U, ReachIn G B x (g u) := by
    intro x hx
    rcases hmemB' x hx with ⟨hxW, hxS⟩ | hxZ
    · obtain ⟨u, v, huv, hxuv⟩ := StripSystemBasics.mem_stripSystemVertices_iff.mp hxW
      have hne : s(u, v) ≠ s(b₁, b₂) := by
        intro hcon
        rcases Sym2.eq_iff.mp hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxS hxuv
        · exact hxS (by rw [← hSsymm]; exact hxuv)
      exact ⟨u, hstripReach u v huv hne x hxuv (m u) (hm u) (hmne u) (g u) (hg u)⟩
    · obtain ⟨F, hF, hxF⟩ := ComponentsOfSetBasics.exists_isComponent_mem G Z hxZ
      have hFnotatt : ¬ (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty :=
        fun hcc => (hmemB x).mp hx ((hmemA x).mpr (Or.inr ⟨F, ⟨hF, hcc⟩, hxF⟩))
      obtain ⟨T, ⟨⟨u, v, huv, rfl⟩, hattne, hattsub, -⟩, -⟩ := hLocal F hF ⟨x, hxF⟩
      obtain ⟨z, hz⟩ := hattne
      have hne : s(u, v) ≠ s(b₁, b₂) := by
        intro hcon
        refine hFnotatt ⟨z, hz, ?_⟩
        have hzT := hattsub hz
        rcases Sym2.eq_iff.mp hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hzT
        · rw [← hSsymm]; exact hzT
      have hFB : F ⊆ B := by
        intro f hf
        rw [hmemB, hmemA]
        push_neg
        refine ⟨fun hcc => ?_, fun F' hF' hfF' => ?_⟩
        · exact hZW f (StripSystemBasics.strip_subset_vertices hb₁b₂ hcc) (hF.1 hf)
        · have hFF' : F' = F := by
            by_contra hne'
            exact (Set.disjoint_left.mp
              (ComponentsOfSetBasics.disjoint_of_isComponent G hF'.1 hF hne') hfF') hf
          exact hFnotatt (hFF' ▸ hF'.2)
      obtain ⟨hzW, f, hfF, hzf⟩ := id hz
      have hzSuv : z ∈ S u v := hattsub hz
      have hzB : z ∈ B := hstripB u v huv hne hzSuv
      refine ⟨u, reachIn_trans ?_
        (hstripReach u v huv hne z hzSuv (m u) (hm u) (hmne u) (g u) (hg u))⟩
      exact reachIn_trans (reachIn_of_connected hFB hF.2.1 hxF hfF)
        (reachIn_of_adj (hFB hfF) hzB hzf.symm)
  have hBconn : ConnectedSet G B := by
    refine connectedSet_of_reachIn (fun x hx y hy => ?_)
    obtain ⟨u, hu⟩ := hBreach x hx
    obtain ⟨v, hv⟩ := hBreach y hy
    exact reachIn_trans hu (reachIn_trans (hallg u v) (reachIn_symm hv))
  -- the elementary set-theoretic conjuncts
  have hAne : A.Nonempty := by
    obtain ⟨z, hz⟩ := StripSystemBasics.strip_nonempty hS hb₁b₂
    exact ⟨z, (hmemA z).mpr (Or.inl hz)⟩
  have hA₁ne : A₁.Nonempty := by rw [hA₁]; exact StripSystemBasics.Nuv_nonempty hS hb₁b₂
  have hA₂ne : A₂.Nonempty := by
    rw [hA₂]
    obtain ⟨z, hz⟩ := StripSystemBasics.Nuv_nonempty hS hb₂b₁
    exact ⟨z, hz.1, by rw [← hSsymm]; exact hz.2⟩
  have hA₁A : A₁ ⊆ A := by rw [hA₁]; exact fun x hx => (hmemA x).mpr (Or.inl hx.2)
  have hA₂A : A₂ ⊆ A := by rw [hA₂]; exact fun x hx => (hmemA x).mpr (Or.inl hx.2)
  have hmemB₁ : ∀ x : V, x ∈ B₁ ↔ (x ∈ N b₁ ∧ x ∉ S b₁ b₂) := by
    intro x
    rw [hB₁, hA₁]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun hc => h2 ⟨h1, hc⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun hc => h2 hc.2⟩
  have hmemB₂ : ∀ x : V, x ∈ B₂ ↔ (x ∈ N b₂ ∧ x ∉ S b₁ b₂) := by
    intro x
    rw [hB₂, hA₂]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun hc => h2 ⟨h1, hc⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun hc => h2 hc.2⟩
  have hB₁B : B₁ ⊆ B := by
    intro x hx
    obtain ⟨hxN, hxS⟩ := (hmemB₁ x).mp hx
    obtain ⟨w, hw, hxw⟩ := StripSystemBasics.mem_Nuv_of_mem_N hS hxN
    have hne : s(b₁, w) ≠ s(b₁, b₂) := by
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨-, rfl⟩ | ⟨h1, -⟩
      · exact hxS hxw.2
      · exact hb₁b₂.ne h1
    exact hstripB b₁ w hw hne hxw.2
  have hB₂B : B₂ ⊆ B := by
    intro x hx
    obtain ⟨hxN, hxS⟩ := (hmemB₂ x).mp hx
    obtain ⟨w, hw, hxw⟩ := StripSystemBasics.mem_Nuv_of_mem_N hS hxN
    have hne : s(b₂, w) ≠ s(b₁, b₂) := by
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨-, rfl⟩
      · exact hb₁b₂.ne h1.symm
      · exact hxS (by rw [← hSsymm]; exact hxw.2)
    exact hstripB b₂ w hw hne hxw.2
  -- two distinct vertices in `B₁`, and in `B₂`
  have htwo : ∀ c d : U, J.Adj c d → S c d = S b₁ b₂ →
      ∃ x y : V, x ∈ N c ∧ x ∉ S b₁ b₂ ∧ y ∈ N c ∧ y ∉ S b₁ b₂ ∧ x ≠ y := by
    intro c d hcd hSeq
    have h3 : 3 ≤ (J.neighborSet c).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ c
    obtain ⟨w, hw, hwd⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet c) (by omega) d
    obtain ⟨w', hw', hw'd, hw'w⟩ := Thm86ClaimTwo.exists_mem_ne_two h3 d w
    have hadjw : J.Adj c w := hw
    have hadjw' : J.Adj c w' := hw'
    obtain ⟨x, hx⟩ := StripSystemBasics.Nuv_nonempty hS hadjw
    obtain ⟨x', hx'⟩ := StripSystemBasics.Nuv_nonempty hS hadjw'
    have hnotin : ∀ (e : U) (he : J.Adj c e), e ≠ d → ∀ y ∈ stripSystemNuv S N c e,
        y ∉ S b₁ b₂ := by
      intro e he hed y hy hcon
      have hne : s(c, e) ≠ s(c, d) := by
        intro hcc
        rcases Sym2.eq_iff.mp hcc with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hed h2
        · exact hcd.ne h1
      exact (Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hS he hcd hne) hy.2)
        (by rw [hSeq]; exact hcon)
    refine ⟨x, x', hx.1, hnotin w hadjw hwd x hx, hx'.1, hnotin w' hadjw' hw'd x' hx', ?_⟩
    rintro rfl
    exact hw'w (StripSystemBasics.Nuv_eq_of_mem hS hadjw' hadjw hx' hx)
  obtain ⟨x₁, y₁, hx₁N, hx₁S, hy₁N, hy₁S, hxy₁⟩ := htwo b₁ b₂ hb₁b₂ rfl
  obtain ⟨x₂, y₂, hx₂N, hx₂S, hy₂N, hy₂S, hxy₂⟩ := htwo b₂ b₁ hb₂b₁ hSsymm
  have hB₁card : 2 ≤ B₁.ncard := by
    have hsub : ({x₁, y₁} : Set V) ⊆ B₁ := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact (hmemB₁ y).mpr ⟨hx₁N, hx₁S⟩
      · exact (hmemB₁ y).mpr ⟨hy₁N, hy₁S⟩
    calc 2 = ({x₁, y₁} : Set V).ncard := (Set.ncard_pair hxy₁).symm
      _ ≤ B₁.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hB₂card : 2 ≤ B₂.ncard := by
    have hsub : ({x₂, y₂} : Set V) ⊆ B₂ := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact (hmemB₂ y).mpr ⟨hx₂N, hx₂S⟩
      · exact (hmemB₂ y).mpr ⟨hy₂N, hy₂S⟩
    calc 2 = ({x₂, y₂} : Set V).ncard := (Set.ncard_pair hxy₂).symm
      _ ≤ B₂.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hB₁ne : B₁.Nonempty := ⟨x₁, (hmemB₁ x₁).mpr ⟨hx₁N, hx₁S⟩⟩
  have hB₂ne : B₂.Nonempty := ⟨x₂, (hmemB₂ x₂).mpr ⟨hx₂N, hx₂S⟩⟩
  -- the adjacency characterisation
  have hadjchar : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ ((a ∈ A₁ ∧ b ∈ B₁) ∨ (a ∈ A₂ ∧ b ∈ B₂)) := by
    intro a ha b hb
    constructor
    · intro hadj
      rcases (hmemA a).mp ha with haS | ⟨F, ⟨hFcomp, hFatt⟩, haF⟩
      · rcases hmemB' b hb with ⟨hbW, hbnS⟩ | hbZ
        · obtain ⟨u, v, huv, hbuv⟩ := StripSystemBasics.mem_stripSystemVertices_iff.mp hbW
          have hne : s(u, v) ≠ s(b₁, b₂) := by
            intro hcon
            rcases Sym2.eq_iff.mp hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hbnS hbuv
            · exact hbnS (by rw [← hSsymm]; exact hbuv)
          have hJ1 : ∀ w : U, J.Adj b₁ w → w ≠ b₂ → b ∈ S b₁ w →
              (a ∈ N b₁ ∧ b ∈ N b₁) := fun w hbw hwb₂ hbS =>
            StripSystemBasics.mem_N_of_adj hS hb₁b₂ hbw (Ne.symm hwb₂) haS hbS hadj
          have hJ2 : ∀ w : U, J.Adj b₂ w → w ≠ b₁ → b ∈ S b₂ w →
              (a ∈ N b₂ ∧ b ∈ N b₂) := by
            intro w hbw hwb₁ hbS
            have haS' : a ∈ S b₂ b₁ := by rw [hSsymm]; exact haS
            exact StripSystemBasics.mem_N_of_adj hS hb₂b₁ hbw (Ne.symm hwb₁) haS' hbS hadj
          have key : (a ∈ N b₁ ∧ b ∈ N b₁) ∨ (a ∈ N b₂ ∧ b ∈ N b₂) := by
            by_cases hu1 : u = b₁
            · refine Or.inl (hJ1 v (hu1 ▸ huv) ?_ (hu1 ▸ hbuv))
              intro hc; exact hne (by rw [hu1, hc])
            · by_cases hv1 : v = b₁
              · have hbS : b ∈ S b₁ u := by
                  rw [← hv1, ← StripSystemBasics.strip_symm hS huv]; exact hbuv
                refine Or.inl (hJ1 u (hv1 ▸ huv.symm) ?_ hbS)
                intro hc; exact hne (by rw [hc, hv1]; exact Sym2.eq_swap)
              · by_cases hu2 : u = b₂
                · exact Or.inr (hJ2 v (hu2 ▸ huv) hv1 (hu2 ▸ hbuv))
                · by_cases hv2 : v = b₂
                  · have hbS : b ∈ S b₂ u := by
                      rw [← hv2, ← StripSystemBasics.strip_symm hS huv]; exact hbuv
                    exact Or.inr (hJ2 u (hv2 ▸ huv.symm) hu1 hbS)
                  · exfalso
                    have hnd : [b₁, b₂, u, v].Nodup := by
                      have e1 : b₁ ≠ b₂ := hb₁b₂.ne
                      have e2 : b₁ ≠ u := Ne.symm hu1
                      have e3 : b₁ ≠ v := Ne.symm hv1
                      have e4 : b₂ ≠ u := Ne.symm hu2
                      have e5 : b₂ ≠ v := Ne.symm hv2
                      have e6 : u ≠ v := huv.ne
                      simp [e1, e2, e3, e4, e5, e6]
                    exact StripSystemBasics.strip_anticomplete hS hb₁b₂ huv hnd a haS b hbuv hadj
          rcases key with ⟨haN, hbN⟩ | ⟨haN, hbN⟩
          · exact Or.inl ⟨by rw [hA₁]; exact ⟨haN, haS⟩, (hmemB₁ b).mpr ⟨hbN, hbnS⟩⟩
          · exact Or.inr ⟨by rw [hA₂]; exact ⟨haN, haS⟩, (hmemB₂ b).mpr ⟨hbN, hbnS⟩⟩
        · exfalso
          obtain ⟨F, hF, hbF⟩ := ComponentsOfSetBasics.exists_isComponent_mem G Z hbZ
          have hatt : (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty :=
            ⟨a, ⟨StripSystemBasics.strip_subset_vertices hb₁b₂ haS, b, hbF, hadj⟩, haS⟩
          exact (hmemB b).mp hb ((hmemA b).mpr (Or.inr ⟨F, ⟨hF, hatt⟩, hbF⟩))
      · exfalso
        rcases hmemB' b hb with ⟨hbW, hbnS⟩ | hbZ
        · obtain ⟨T, ⟨⟨u, v, huv, rfl⟩, hattne, hattsub, -⟩, -⟩ := hLocal F hFcomp ⟨a, haF⟩
          obtain ⟨z, hzatt, hzS⟩ := hFatt
          have hTeq : S u v = S b₁ b₂ :=
            StripSystemBasics.strip_eq_of_mem_strips hS huv hb₁b₂ (hattsub hzatt) hzS
          exact hbnS (by rw [← hTeq]; exact hattsub ⟨hbW, a, haF, hadj.symm⟩)
        · obtain ⟨F', hF', hbF'⟩ := ComponentsOfSetBasics.exists_isComponent_mem G Z hbZ
          have hFF' : F ≠ F' := by
            rintro rfl
            exact (hmemB b).mp hb ((hmemA b).mpr (Or.inr ⟨F, ⟨hFcomp, hFatt⟩, hbF'⟩))
          exact ComponentsOfSetBasics.anticomplete_of_isComponent G hFcomp hF' hFF'
            a haF b hbF' hadj
    · rintro (⟨ha1, hb1⟩ | ⟨ha2, hb2⟩)
      · rw [hA₁] at ha1
        obtain ⟨hbN, hbS⟩ := (hmemB₁ b).mp hb1
        obtain ⟨w, hw, hbw⟩ := StripSystemBasics.mem_Nuv_of_mem_N hS hbN
        have hwb₂ : b₂ ≠ w := by rintro rfl; exact hbS hbw.2
        exact StripSystemBasics.Nuv_complete hS hb₁b₂ hw hwb₂ a ha1 b hbw
      · rw [hA₂] at ha2
        obtain ⟨hbN, hbS⟩ := (hmemB₂ b).mp hb2
        obtain ⟨w, hw, hbw⟩ := StripSystemBasics.mem_Nuv_of_mem_N hS hbN
        have hwb₁ : b₁ ≠ w := by
          rintro rfl
          exact hbS (by rw [← hSsymm]; exact hbw.2)
        have ha2' : a ∈ N b₂ ∩ S b₂ b₁ := ⟨ha2.1, by rw [hSsymm]; exact ha2.2⟩
        exact StripSystemBasics.Nuv_complete hS hb₂b₁ hw hwb₁ a ha2' b hbw
  -- components of `A` meet both ends of the strip
  have hAcomp : ∀ C : Set V, IsComponent G A C → (C ∩ A₁).Nonempty ∧ (C ∩ A₂).Nonempty := by
    intro C hC
    obtain ⟨c, hc⟩ := ComponentsOfSetBasics.nonempty_of_isComponent G hAne hC
    have hmeet : ∃ z ∈ C, z ∈ S b₁ b₂ := by
      rcases (hmemA c).mp (hC.1 hc) with hcS | ⟨F, ⟨hFcomp, hFatt⟩, hcF⟩
      · exact ⟨c, hc, hcS⟩
      · obtain ⟨z, hzatt, hzS⟩ := hFatt
        have hFA : F ⊆ A := fun y hy =>
          (hmemA y).mpr (Or.inr ⟨F, ⟨hFcomp, ⟨z, hzatt, hzS⟩⟩, hy⟩)
        obtain ⟨hzW, f, hfF, hzf⟩ := id hzatt
        have hCF : C ∪ F = C := hC.2.2 (C ∪ F) Set.subset_union_left
          (Set.union_subset hC.1 hFA)
          (ConnectedSetUnionAttach.connectedSet_union hC.2.1 hFcomp.2.1 (Or.inl ⟨c, hc, hcF⟩))
        have hfC : f ∈ C := by rw [← hCF]; exact Set.mem_union_right _ hfF
        have hzC : z ∈ C := by
          have hCz : C ∪ {z} = C := hC.2.2 (C ∪ {z}) Set.subset_union_left
            (Set.union_subset hC.1 (by
              intro y hy
              simp only [Set.mem_singleton_iff] at hy
              subst hy
              exact (hmemA y).mpr (Or.inl hzS)))
            (ConnectedSetUnionAttach.connectedSet_union_singleton hC.2.1 ⟨f, hfC, hzf⟩)
          rw [← hCz]; exact Set.mem_union_right _ rfl
        exact ⟨z, hzC, hzS⟩
    obtain ⟨z, hzC, hzS⟩ := hmeet
    obtain ⟨R, hR, hzR⟩ := StripSystemBasics.exists_rung hS hb₁b₂ hzS
    obtain ⟨s, hsR, hsS, hsN, -⟩ := StripSystemBasics.exists_rung_head hR
    obtain ⟨t, htR, htS, htN, -⟩ := StripSystemBasics.exists_rung_last hR
    have hRA : {x : V | x ∈ R} ⊆ A := fun y hy =>
      (hmemA y).mpr (Or.inl (StripSystemBasics.rung_subset_strip hR y hy))
    have hCR : C ∪ {x : V | x ∈ R} = C := hC.2.2 _ Set.subset_union_left
      (Set.union_subset hC.1 hRA)
      (ConnectedSetUnionAttach.connectedSet_union hC.2.1 (hrungconn b₁ b₂ R hR)
        (Or.inl ⟨z, hzC, hzR⟩))
    have hsC : s ∈ C := by rw [← hCR]; exact Set.mem_union_right _ hsR
    have htC : t ∈ C := by rw [← hCR]; exact Set.mem_union_right _ htR
    exact ⟨⟨s, hsC, by rw [hA₁]; exact ⟨hsN, hsS⟩⟩, ⟨t, htC, by rw [hA₂]; exact ⟨htN, htS⟩⟩⟩
  -- an edge of `J` avoiding both `b₁` and `b₂`
  have hedgeAvoid : ∃ c d : U, J.Adj c d ∧ c ≠ b₁ ∧ c ≠ b₂ ∧ d ≠ b₁ ∧ d ≠ b₂ := by
    have hcard2 : ({b₁, b₂} : Set U).ncard ≤ 2 := by
      have h := Set.ncard_insert_le b₁ ({b₂} : Set U)
      rw [Set.ncard_singleton] at h; omega
    have hcc := hJ.2 ({b₁, b₂} : Set U) (by omega)
    have hcompl : 1 < ((({b₁, b₂} : Set U)ᶜ)).ncard := by
      have h1 := Set.ncard_add_ncard_compl ({b₁, b₂} : Set U)
      rw [Nat.card_eq_fintype_card] at h1
      have h4 : 3 < Fintype.card U := hJ.1
      omega
    obtain ⟨a, ha⟩ : ((({b₁, b₂} : Set U)ᶜ)).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard hcompl a
    have hne : (⟨a, ha⟩ : ↥((({b₁, b₂} : Set U)ᶜ))) ≠ ⟨b, hb⟩ := fun hcon =>
      hba (congrArg Subtype.val hcon).symm
    obtain ⟨c, hcadj⟩ := SubdivisionCounting.exists_adj_of_reachable
      (hcc.preconnected ⟨a, ha⟩ ⟨b, hb⟩) hne
    refine ⟨a, (c : U), hcadj, ?_, ?_, ?_, ?_⟩
    · intro h; exact ha (by simp [h])
    · intro h; exact ha (by simp [h])
    · intro h; exact c.2 (by simp [h])
    · intro h; exact c.2 (by simp [h])
  have hBdiff : (B \ (B₁ ∪ B₂)).Nonempty := by
    obtain ⟨c, d, hcd, hc1, hc2, hd1, hd2⟩ := hedgeAvoid
    have hne : s(c, d) ≠ s(b₁, b₂) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hc1 h1
      · exact hc2 h1
    obtain ⟨x, hx⟩ := StripSystemBasics.strip_nonempty hS hcd
    have hnb₁ : x ∉ N b₁ := by
      intro hxN
      have he := StripSystemBasics.strip_inter_N_eq_empty hS hcd (Ne.symm hc1) (Ne.symm hd1)
      rw [Set.eq_empty_iff_forall_notMem] at he
      exact he x ⟨hx, hxN⟩
    have hnb₂ : x ∉ N b₂ := by
      intro hxN
      have he := StripSystemBasics.strip_inter_N_eq_empty hS hcd (Ne.symm hc2) (Ne.symm hd2)
      rw [Set.eq_empty_iff_forall_notMem] at he
      exact he x ⟨hx, hxN⟩
    refine ⟨x, hstripB c d hcd hne hx, ?_⟩
    rintro (h | h)
    · exact hnb₁ ((hmemB₁ x).mp h).1
    · exact hnb₂ ((hmemB₂ x).mp h).1
  -- `|A| ≥ 2`
  have hAcard : 2 ≤ A.ncard := by
    rcases hselected with ⟨R₁, R₂, hR₁, hR₂, hRne⟩ | ⟨F, hFcomp, hFatt⟩
    · have hex : ∃ x : V, ¬ (x ∈ R₁ ↔ x ∈ R₂) := by
        by_contra hcon
        exact hRne (Set.ext (fun y => not_not.mp (fun hh => hcon ⟨y, hh⟩)))
      obtain ⟨x, hx⟩ := hex
      have hpair : ∃ p q : V, p ∈ A ∧ q ∈ A ∧ p ≠ q := by
        rcases Classical.em (x ∈ R₁) with h1 | h1
        · have h2 : x ∉ R₂ := fun hcc => hx ⟨fun _ => hcc, fun _ => h1⟩
          obtain ⟨y, hyR, -, -, -⟩ := StripSystemBasics.exists_rung_head hR₂
          refine ⟨x, y, (hmemA x).mpr (Or.inl (StripSystemBasics.rung_subset_strip hR₁ x h1)),
            (hmemA y).mpr (Or.inl (StripSystemBasics.rung_subset_strip hR₂ y hyR)), ?_⟩
          rintro rfl; exact h2 hyR
        · have h2 : x ∈ R₂ := by
            by_contra hcc
            exact hx ⟨fun hh => absurd hh h1, fun hh => absurd hh hcc⟩
          obtain ⟨y, hyR, -, -, -⟩ := StripSystemBasics.exists_rung_head hR₁
          refine ⟨x, y, (hmemA x).mpr (Or.inl (StripSystemBasics.rung_subset_strip hR₂ x h2)),
            (hmemA y).mpr (Or.inl (StripSystemBasics.rung_subset_strip hR₁ y hyR)), ?_⟩
          rintro rfl; exact h1 hyR
      obtain ⟨p, q, hp, hq, hpq⟩ := hpair
      have hsub : ({p, q} : Set V) ⊆ A := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hp
        · exact hq
      calc 2 = ({p, q} : Set V).ncard := (Set.ncard_pair hpq).symm
        _ ≤ A.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    · obtain ⟨z, hzatt, hzS⟩ := hFatt
      have hzA : z ∈ A := (hmemA z).mpr (Or.inl hzS)
      obtain ⟨hzW, f, hfF, hzf⟩ := id hzatt
      have hfA : f ∈ A := (hmemA f).mpr (Or.inr ⟨F, ⟨hFcomp, ⟨z, hzatt, hzS⟩⟩, hfF⟩)
      have hzfne : z ≠ f := by
        intro hcc
        exact hZW z hzW (by rw [hcc]; exact hFcomp.1 hfF)
      have hsub : ({z, f} : Set V) ⊆ A := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hzA
        · exact hfA
      calc 2 = ({z, f} : Set V).ncard := (Set.ncard_pair hzfne).symm
        _ ≤ A.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  -- `A` is not the vertex set of a path joining singleton ends
  have hpathcond : ∀ a₁ a₂ : V, A₁ = {a₁} → A₂ = {a₂} →
      ¬ ∃ p : List V, IsPathFrom G p a₁ a₂ ∧ {v : V | v ∈ p} = A := by
    rintro a₁ a₂ h1 h2 ⟨p, hp, hpA⟩
    have hrungA : ∀ R : List V, IsUVRung G J S N b₁ b₂ R → ({x : V | x ∈ R} : Set V) = A := by
      intro R hR
      obtain ⟨s, hsR, hsS, hsN, -⟩ := StripSystemBasics.exists_rung_head hR
      obtain ⟨t, htR, htS, htN, -⟩ := StripSystemBasics.exists_rung_last hR
      have hsa : s = a₁ := by
        have hmem : s ∈ A₁ := by rw [hA₁]; exact ⟨hsN, hsS⟩
        rw [h1] at hmem; exact hmem
      have hta : t = a₂ := by
        have hmem : t ∈ A₂ := by rw [hA₂]; exact ⟨htN, htS⟩
        rw [h2] at hmem; exact hmem
      have hRA : {x : V | x ∈ R} ⊆ A := fun y hy =>
        (hmemA y).mpr (Or.inl (StripSystemBasics.rung_subset_strip hR y hy))
      refine Set.Subset.antisymm hRA ?_
      rw [← hpA]
      refine path_subset_of_connected hp (by rw [hpA]; exact hRA) (hrungconn b₁ b₂ R hR)
        ?_ ?_
      · rw [← hsa]; exact hsR
      · rw [← hta]; exact htR
    rcases hselected with ⟨R₁, R₂, hR₁, hR₂, hRne⟩ | ⟨F, hFcomp, hFatt⟩
    · exact hRne ((hrungA R₁ hR₁).trans (hrungA R₂ hR₂).symm)
    · obtain ⟨R, hR⟩ := StripSystemBasics.exists_uvRung hS hb₁b₂
      obtain ⟨z, hzatt, hzS⟩ := hFatt
      obtain ⟨hzW, f, hfF, hzf⟩ := id hzatt
      have hfA : f ∈ A := (hmemA f).mpr (Or.inr ⟨F, ⟨hFcomp, ⟨z, hzatt, hzS⟩⟩, hfF⟩)
      have hfR : f ∈ ({x : V | x ∈ R} : Set V) := by rw [hrungA R hR]; exact hfA
      exact hZW f (StripSystemBasics.strip_subset_vertices hb₁b₂
        (StripSystemBasics.rung_subset_strip hR f hfR)) (hFcomp.1 hfF)
  refine ⟨?_, ?_, hA₁ne, hA₁A, hA₂ne, hA₂A, hB₁ne, hB₁B, hB₁card, hB₂ne, hB₂B, hB₂card,
    hadjchar, hAcomp, hBconn, ?_, ?_, hAcard, hBdiff, hpathcond⟩
  · rw [hBdef]; ext y; by_cases hy : y ∈ A <;> simp [hy]
  · rw [hBdef]; exact Set.disjoint_sdiff_right
  · obtain ⟨y, hy⟩ := hB₁ne; exact ⟨y, hB₁B hy, hy⟩
  · obtain ⟨y, hy⟩ := hB₂ne; exact ⟨y, hB₂B hy, hy⟩

theorem selectedStripSeparationData
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hS : IsJStripSystem G J S N)
    (Z : Set V) (hZdisj : Disjoint Z (stripSystemVertices J S))
    (hZ : Z = (stripSystemVertices J S)ᶜ)
    (hLocal : ∀ F : Set V, IsComponent G Z F → F.Nonempty →
      ∃! T : Set V,
        IsStripOfStripSystem J S T ∧
          (attachments G F (stripSystemVertices J S)).Nonempty ∧
          attachments G F (stripSystemVertices J S) ⊆ T ∧
          ∀ v : U, ¬ attachments G F (stripSystemVertices J S) ⊆ N v)
    (b₁ b₂ : U) (hb₁b₂ : J.Adj b₁ b₂)
    (hselected :
      (∃ R₁ R₂ : List V,
        IsUVRung G J S N b₁ b₂ R₁ ∧ IsUVRung G J S N b₁ b₂ R₂ ∧
          ({x : V | x ∈ R₁} : Set V) ≠ {x : V | x ∈ R₂}) ∨
      ∃ F : Set V, IsComponent G Z F ∧
        (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty) :
    let A : Set V := S b₁ b₂ ∪
      ⋃ (F : Set V) (_ : IsComponent G Z F ∧
        (attachments G F (stripSystemVertices J S) ∩ S b₁ b₂).Nonempty), F
    let B : Set V := Set.univ \ A
    let A₁ : Set V := N b₁ ∩ S b₁ b₂
    let A₂ : Set V := N b₂ ∩ S b₁ b₂
    let B₁ : Set V := N b₁ \ A₁
    let B₂ : Set V := N b₂ \ A₂
    A ∪ B = Set.univ ∧ Disjoint A B ∧
    A₁.Nonempty ∧ A₁ ⊆ A ∧ A₂.Nonempty ∧ A₂ ⊆ A ∧
    B₁.Nonempty ∧ B₁ ⊆ B ∧ 2 ≤ B₁.ncard ∧
    B₂.Nonempty ∧ B₂ ⊆ B ∧ 2 ≤ B₂.ncard ∧
    (∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ ((a ∈ A₁ ∧ b ∈ B₁) ∨ (a ∈ A₂ ∧ b ∈ B₂))) ∧
    (∀ C : Set V, IsComponent G A C →
      (C ∩ A₁).Nonempty ∧ (C ∩ A₂).Nonempty) ∧
    ConnectedSet G B ∧ (B ∩ B₁).Nonempty ∧ (B ∩ B₂).Nonempty ∧
    2 ≤ A.ncard ∧ (B \ (B₁ ∪ B₂)).Nonempty ∧
    (∀ a₁ a₂ : V, A₁ = {a₁} → A₂ = {a₂} →
      ¬ ∃ p : List V, IsPathFrom G p a₁ a₂ ∧ {v : V | v ∈ p} = A) := by
  intro A B A₁ A₂ B₁ B₂
  exact core G J hJ S N hS Z hZ hLocal b₁ b₂ hb₁b₂ hselected A B A₁ A₂ B₁ B₂ rfl rfl rfl rfl
    rfl rfl

end Workspace.ProofLemmas.SelectedStripSeparationData
