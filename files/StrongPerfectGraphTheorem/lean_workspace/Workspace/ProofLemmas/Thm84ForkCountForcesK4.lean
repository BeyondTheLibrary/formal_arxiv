import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
import Workspace.ProofLemmas.Thm84AdjacentChoices
import Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath
import Workspace.Statements.S05.Thm_5_7

/-!
# 8.4, second paragraph — proof attempt 2

* Open with `by_cases hK4 : Nonempty (J ≃g K₄)`.  Positive branch: the third disjunct closes the
  goal.  Negative branch: `EnlargementFromNonlocalAttachmentPath`'s hypothesis
  `Nonempty (J ≃g K₄) → NondegenerateAppearance J H'` is **vacuous**, which removes the paper's
  appeal to 8.3 and with it the overshadowed disjunct (anything 8.3 delivers comes with `J = K₄`,
  which is already the third disjunct).
* 5.7's `hnotrack` is where `Berge G` and `y ∉ V(S,N)` are spent: `TrackToRungPath.trackRung`
  turns the forbidden track into an induced path of `G` of odd length `≥ 3` whose ends are
  neighbours of `y` and whose interior avoids `y`, and
  `PrismBasics.isHoleList_of_path_add_vertex` closes it through `y` into an odd hole.
* `forkcount_eq_ncard` is the fork-number analogue of `Thm84AdjacentChoices.saturates_iff`: the
  fork number is a property of the rung family alone, which is what lets the fork numbers of `R`
  and `R'` — computed in *different* graphs `H` and `H'` — be compared at all.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84ForkCountForcesK4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `u` **forks** for the choice of rungs `R`: at least two `J`-neighbours `v` of `u` have the
`u`-end of `R u v` in `X`. -/
def ForkAt {U : Type*} (J : SimpleGraph U) (R : U → U → List V) (X : Set V) (u : U) : Prop :=
  ∃ v v' : U, J.Adj u v ∧ J.Adj u v' ∧ v ≠ v' ∧
    (∃ s : V, (R u v).head? = some s ∧ s ∈ X) ∧
    (∃ s' : V, (R u v').head? = some s' ∧ s' ∈ X)

/-- **The fork number is a property of the choice of rungs alone.**  The fork-number analogue of
`Thm84AdjacentChoices.saturates_iff`. -/
theorem forkcount_eq_ncard {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V) (hForms : FormsLineGraph G J S N R H)
    (φ : H.lineGraph ≃g G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
    (X : Set V) :
    {b ∈ branchVertices H | (incidentEdges H b ∩
        {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}).Nontrivial}.ncard
      = {u : U | ForkAt J R X u}.ncard := by
  classical
  obtain ⟨ι, E, hιinj, hrange, hEedge, hincid, hEinj, hEφ⟩ :=
    Thm84BranchRungDictionaryAt.rungEndDictionaryAt G J hJ S N hSN H R hForms φ
  have hφhead : ∀ (u v : U) (huv : J.Adj u v) (he : E u v ∈ H.edgeSet),
      (R u v).head? = some (↑(φ ⟨E u v, he⟩) : V) := by
    intro u v huv he
    obtain ⟨-, s, t, hp, -, -, -⟩ := hForms.1 u v huv
    rw [hEφ u v huv he s t hp]
    exact hp.2.1
  have hkey : {b ∈ branchVertices H | (incidentEdges H b ∩
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}).Nontrivial}
      = ι '' {u : U | ForkAt J R X u} := by
    ext w
    constructor
    · rintro ⟨hbr, e₁, he₁, e₂, he₂, hne⟩
      obtain ⟨u, rfl⟩ : w ∈ Set.range ι := by rw [hrange]; exact hbr
      refine ⟨u, ?_, rfl⟩
      have h1 := he₁.1
      rw [hincid u] at h1
      obtain ⟨v, huv, rfl⟩ := h1
      have h2 := he₂.1
      rw [hincid u] at h2
      obtain ⟨v', huv', rfl⟩ := h2
      obtain ⟨hx1, hxin1⟩ := he₁.2
      obtain ⟨hx2, hxin2⟩ := he₂.2
      refine ⟨v, v', huv, huv', ?_, ⟨_, hφhead u v huv hx1, hxin1⟩,
        ⟨_, hφhead u v' huv' hx2, hxin2⟩⟩
      rintro rfl
      exact hne rfl
    · rintro ⟨u, ⟨v, v', huv, huv', hvv', ⟨s, hs, hsX⟩, ⟨s', hs', hs'X⟩⟩, rfl⟩
      have hbr : ι u ∈ branchVertices H := by rw [← hrange]; exact ⟨u, rfl⟩
      have hmem : ∀ (w : U) (hw : J.Adj u w) (z : V), (R u w).head? = some z → z ∈ X →
          E u w ∈ incidentEdges H (ι u) ∩
            {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} := by
        intro w hw z hz hzX
        refine ⟨by rw [hincid u]; exact ⟨w, hw, rfl⟩, hEedge u w hw, ?_⟩
        have hh := hφhead u w hw (hEedge u w hw)
        rw [hz] at hh
        rw [← Option.some_injective _ hh]
        exact hzX
      refine ⟨hbr, E u v, hmem v huv s hs hsX, E u v', hmem v' huv' s' hs' hs'X, ?_⟩
      intro hcon
      exact hvv' (hEinj u v v' huv huv' hcon)
  rw [hkey, Set.ncard_image_of_injective _ hιinj]

/-- Three distinct `J`-neighbours of a vertex, from 3-connectivity. -/
theorem exists_three_neighbours {U : Type*} [Fintype U] (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (u : U) :
    ∃ v₁ v₂ v₃ : U, J.Adj u v₁ ∧ J.Adj u v₂ ∧ J.Adj u v₃ ∧
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
  have hn : 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  obtain ⟨v₁, hv₁⟩ : (J.neighborSet u).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hc1 : (J.neighborSet u \ {v₁}).ncard = (J.neighborSet u).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hv₁
  obtain ⟨v₂, hv₂⟩ : (J.neighborSet u \ {v₁}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hc2 : ((J.neighborSet u \ {v₁}) \ {v₂}).ncard = (J.neighborSet u \ {v₁}).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hv₂
  obtain ⟨v₃, hv₃⟩ : ((J.neighborSet u \ {v₁}) \ {v₂}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  exact ⟨v₁, v₂, v₃, hv₁, hv₂.1, hv₃.1.1,
    fun h => hv₂.2 h.symm, fun h => hv₃.1.2 h.symm, fun h => hv₃.2 h.symm⟩

/-- **The second paragraph of the printed proof of 8.4.** -/
theorem forkCountForcesK4 {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateStripSystem G J S N)
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (a b : U) (hab : J.Adj a b)
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
    (φ : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (φ' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms : FormsLineGraph G J S N R H)
    (hsym : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (hForms' : FormsLineGraph G J S N R' H')
    (hsym' : ∀ u v : U, J.Adj u v → R' v u = (R' u v).reverse)
    (hSat : SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X})
    (hUnsat : ¬ SaturatesLineGraph H'
      {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X})
    (hdiff : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v) :
    (∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (k : ℕ) (H'' : SimpleGraph (Fin k)) (K'' : Set V),
        IsAppearance G J' H'' K'' ∧ NondegenerateAppearance J' H'') ∨
    (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧
      ∃ (k : ℕ) (H'' : SimpleGraph (Fin k)) (K'' : Set V)
        (ψ : H''.lineGraph ≃g G.induce K''),
        IsAppearance G J H'' K'' ∧ IsOvershadowedAppearance G H'' K'' ψ) ∨
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := by
  classical
  by_cases hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4)))
  · exact Or.inr (Or.inr hK4)
  have hbip' : H'.IsBipartite := hForms'.2.1.2
  obtain ⟨J₀, ⟨eJ⟩⟩ := IsoTransport.exists_iso_fin J
  have hc3 : CyclicallyThreeConnected H' :=
    ⟨Fintype.card U, J₀, SubdivisionCounting.isKConnected_of_iso eJ hJ,
      Thm85Five8Transported.isSubdivision_of_iso eJ hForms'.2.1.1⟩
  have hXE : {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X}
      ⊆ H'.edgeSet := by
    rintro e ⟨he, -⟩
    exact he
  have hyK' : y ∉ (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}) := by
    intro h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at h
    obtain ⟨u, v, huv, hmem⟩ := h
    obtain ⟨-, s, t, -, hsubs, -, -⟩ := hForms'.1 u v huv
    refine hy ?_
    simp only [stripSystemVertices, Set.mem_iUnion]
    exact ⟨u, v, huv, hsubs y hmem⟩
  ---------------------------------------------------------------------------
  -- 5.7 applied to `H'`.
  ---------------------------------------------------------------------------
  have h57 := _root_.Workspace.Statements.S05.SPGT.thm_5_7 H' hbip' hc3
    {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X} hXE (by
      rintro ⟨q, hq5, hqt, hqeven, hfirst, hlast, hmid⟩
      have hnodup : q.Nodup := hqt.2.1
      obtain ⟨m, hm⟩ : ∃ m : ℕ, q.length = m + 2 := ⟨q.length - 2, by omega⟩
      have hm3 : 3 ≤ m := by omega
      have h1le : 1 ≤ trackLength q := by simp only [trackLength]; omega
      have hplen : (TrackToRungPath.trackRung φ' q hqt).length = trackLength q :=
        TrackToRungPath.trackRung_length φ' q hqt
      have hpl : pathLength (TrackToRungPath.trackRung φ' q hqt) = trackLength q - 1 :=
        TrackToRungPath.trackRung_pathLength φ' q hqt
      have htlq : trackLength q = m + 1 := by simp only [trackLength]; omega
      set p : List V := TrackToRungPath.trackRung φ' q hqt with hpdef
      have hplenm : p.length = m + 1 := by rw [hplen, htlq]
      have hpath := TrackToRungPath.trackRung_exists_isPathFrom φ' q hqt h1le
      obtain ⟨s, t, hpst⟩ := hpath
      have hpget : ∀ (i : ℕ) (hi : i < p.length) (hi' : i + 1 < q.length)
          (he : s(q[i]'(by omega), q[i + 1]'hi') ∈ H'.edgeSet),
          p[i]'hi = (↑(φ' ⟨s(q[i]'(by omega), q[i + 1]'hi'), he⟩) : V) :=
        TrackToRungPath.trackRung_getElem φ' q hqt
      -- distinct indices give distinct edges of the track
      have hedgeInj : ∀ (i j : ℕ) (hi : i + 1 < q.length) (hj : j + 1 < q.length),
          s(q[i]'(by omega), q[i + 1]'hi) = s(q[j]'(by omega), q[j + 1]'hj) → i = j := by
        intro i j hi hj hcon
        rcases Sym2.eq_iff.mp hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hnodup.getElem_inj_iff.mp h1
        · have ha : i = j + 1 := hnodup.getElem_inj_iff.mp h1
          have hb : i + 1 = j := hnodup.getElem_inj_iff.mp h2
          omega
      -- normalise the last edge to index `m`
      have e_a : q[q.length - 2]'(by omega) = q[m]'(by omega) :=
        SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
      have e_b : q[q.length - 1]'(by omega) = q[m + 1]'(by omega) :=
        SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
      have hlastEdge : s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega))
          = s(q[m]'(by omega), q[m + 1]'(by omega)) := by rw [e_a, e_b]
      obtain ⟨he0, hx0⟩ := hfirst
      obtain ⟨heL, hxL⟩ := hlast
      have heL' : s(q[m]'(by omega), q[m + 1]'(by omega)) ∈ H'.edgeSet := by
        rw [← hlastEdge]; exact heL
      have hxL' : (↑(φ' ⟨s(q[m]'(by omega), q[m + 1]'(by omega)), heL'⟩) : V) ∈ X := by
        have hsub : (⟨s(q[m]'(by omega), q[m + 1]'(by omega)), heL'⟩ : H'.edgeSet)
            = ⟨s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)), heL⟩ :=
          Subtype.ext hlastEdge.symm
        rw [hsub]; exact hxL
      -- the two ends of `p`
      have hs0 : p[0]'(by omega) = s := by
        have h := hpst.2.1
        rw [List.head?_eq_getElem?,
          List.getElem?_eq_getElem (show 0 < p.length by omega)] at h
        exact Option.some_injective _ h
      have htm : p[m]'(by omega) = t := by
        have h := hpst.2.2
        rw [List.getLast?_eq_getElem?,
          List.getElem?_eq_getElem (show p.length - 1 < p.length by omega)] at h
        have h2 : p[p.length - 1]'(show p.length - 1 < p.length by omega)
            = p[m]'(show m < p.length by omega) :=
          SubdivisionCounting.getElem_eq_of_index_eq p (by omega) _ _
        rw [h2] at h
        exact Option.some_injective _ h
      have hsX : s ∈ X := by
        have hz : s = p[0]'(show 0 < p.length by omega) := hs0.symm
        rw [hz, hpget 0 (by omega) (by omega) he0]
        exact hx0
      have htX : t ∈ X := by
        have hz : t = p[m]'(show m < p.length by omega) := htm.symm
        rw [hz, hpget m (by omega) (by omega) heL']
        exact hxL'
      -- the interior of `p` avoids `y`
      have hintp : ∀ x ∈ SPGT.interior p, ¬ G.Adj y x := by
        intro x hx
        have hx' : x ∈ trackInterior p := hx
        rw [SubdivisionCounting.mem_trackInterior_iff] at hx'
        obtain ⟨j, hj, hjx⟩ := hx'
        have hi1 : j + 1 + 1 < q.length := by omega
        have he : s(q[j + 1]'(by omega), q[j + 1 + 1]'hi1) ∈ H'.edgeSet :=
          TrackToRungPath.trackEdge_mem_edgeSet hqt (j + 1) hi1
        have hxeq : x = (↑(φ' ⟨s(q[j + 1]'(by omega), q[j + 1 + 1]'hi1), he⟩) : V) := by
          rw [← hjx, hpget (j + 1) (by omega) hi1 he]
        have hne0 : s(q[j + 1]'(by omega), q[j + 1 + 1]'hi1)
            ≠ s(q[0]'(by omega), q[0 + 1]'(by omega)) := by
          intro hcon
          have := hedgeInj (j + 1) 0 hi1 (by omega) hcon
          omega
        have hneL : s(q[j + 1]'(by omega), q[j + 1 + 1]'hi1)
            ≠ s(q[m]'(by omega), q[m + 1]'(by omega)) := by
          intro hcon
          have := hedgeInj (j + 1) m hi1 (by omega) hcon
          omega
        have hnotX := hmid _ ⟨j + 1, hi1, rfl⟩ hne0 (by rw [hlastEdge]; exact hneL)
        rw [hxeq]
        intro hadj
        exact hnotX ⟨he, by rw [hX]; exact hadj⟩
      -- close the path through `y`
      have hyp : y ∉ p := fun hmem =>
        hyK' (TrackToRungPath.trackRung_subset_K φ' q hqt y hmem)
      have hadjs : G.Adj y s := by rw [hX] at hsX; exact hsX
      have hadjt : G.Adj y t := by rw [hX] at htX; exact htX
      have hhole : IsHoleList G (y :: p) :=
        PrismBasics.isHoleList_of_path_add_vertex hpst (by rw [hpl, htlq]; omega)
          hadjs hadjt hyp hintp
      have hlen : holeLength (y :: p) = pathLength p + 2 :=
        PrismBasics.holeLength_cons y (by intro hc; rw [hc] at hplenm; simp at hplenm)
      have heven := hG.1 (y :: p) hhole
      rw [hlen, hpl, htlq] at heven
      obtain ⟨c, hc⟩ := heven
      obtain ⟨d, hd⟩ := hqeven
      rw [htlq] at hd
      omega)
  ---------------------------------------------------------------------------
  -- The three surviving alternatives.
  ---------------------------------------------------------------------------
  rcases h57.2 with (hsat | h576) | ⟨hfork, -⟩
  · exact absurd hsat hUnsat
  · -- 5.7.6: attach `y` as a new branch, giving an appearance of a `J`-enlargement
    obtain ⟨c₁, c₂, hbip12, hnb, hXeq⟩ := h576
    refine Or.inl ?_
    refine EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath
      G hG J hJ n' H' (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v})
      hForms'.2 φ'
      (fun c => {x : V | ∃ (e : Sym2 (Fin n')) (he : e ∈ H'.edgeSet),
        e ∈ incidentEdges H' c ∧ x = (↑(φ' ⟨e, he⟩) : V)})
      (fun c => rfl) [y] y y ?_ ?_ c₁ c₂ hnb ?_ ?_ ?_ (fun h => absurd h hK4)
    · -- `[y]` is a path of `G` from `y` to `y`
      refine ⟨⟨by simp, by simp, ?_⟩, rfl, rfl⟩
      intro i j hi hj
      simp only [List.length_singleton] at hi hj
      have hii : i = 0 := by omega
      have hjj : j = 0 := by omega
      subst hii
      subst hjj
      constructor
      · intro hcon; exact (G.irrefl hcon).elim
      · intro hcon; omega
    · intro x hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      exact hyK'
    · -- every vertex of `δ(c₁)` is a neighbour of `y`
      rintro x ⟨e, he, hein, rfl⟩
      have hex : e ∈ {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X} := by
        rw [hXeq]; exact Or.inl hein
      obtain ⟨he', hx'⟩ := hex
      rw [hX] at hx'
      exact hx'
    · rintro x ⟨e, he, hein, rfl⟩
      have hex : e ∈ {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X} := by
        rw [hXeq]; exact Or.inr hein
      obtain ⟨he', hx'⟩ := hex
      rw [hX] at hx'
      exact hx'
    · -- every neighbour of `y` inside `L(H')` lies in `δ(c₁) ∪ δ(c₂)`
      intro x hx z hz hadj
      simp only [List.mem_singleton] at hx
      subst hx
      have hzX : (↑(φ' (φ'.symm ⟨z, hz⟩)) : V) ∈ X := by
        rw [RelIso.apply_symm_apply, hX]
        exact hadj
      have hezX : ((φ'.symm ⟨z, hz⟩ : H'.edgeSet) : Sym2 (Fin n'))
          ∈ {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X} :=
        ⟨(φ'.symm ⟨z, hz⟩).2, hzX⟩
      have hzeq : (↑(φ' (φ'.symm ⟨z, hz⟩)) : V) = z := by rw [RelIso.apply_symm_apply]
      rw [hXeq] at hezX
      rcases hezX with h | h
      · exact Or.inl ⟨rfl, ⟨_, (φ'.symm ⟨z, hz⟩).2, h, hzeq.symm⟩⟩
      · exact Or.inr ⟨rfl, ⟨_, (φ'.symm ⟨z, hz⟩).2, h, hzeq.symm⟩⟩
  · -- the fork count: `|V(J)| ≤ 4`, hence `J = K₄`
    have hforkR' : {u : U | ForkAt J R' X u}.ncard ≤ 2 := by
      rw [← forkcount_eq_ncard G J hJ S N hSN H' R' hForms' φ' X]
      exact hfork
    -- every vertex of `J` forks for the saturated choice `R`
    have hfam := (Thm84AdjacentChoices.saturates_iff G J hJ S N hSN H R hForms φ X).mp hSat
    have hallfork : ∀ u : U, ForkAt J R X u := by
      intro u
      have hBadEq : ∀ v v' : U, J.Adj u v → J.Adj u v' →
          ¬ (∃ s : V, (R u v).head? = some s ∧ s ∈ X) →
          ¬ (∃ s : V, (R u v').head? = some s ∧ s ∈ X) → v = v' := by
        intro v v' hv hv' hb hb'
        refine hfam u v v' hv hv' ?_ ?_
        · intro s hs hxx; exact hb ⟨s, hs, hxx⟩
        · intro s hs hxx; exact hb' ⟨s, hs, hxx⟩
      obtain ⟨v₁, v₂, v₃, h1, h2, h3, h12, h13, h23⟩ := exists_three_neighbours J hJ u
      by_cases g1 : ∃ s : V, (R u v₁).head? = some s ∧ s ∈ X
      · by_cases g2 : ∃ s : V, (R u v₂).head? = some s ∧ s ∈ X
        · exact ⟨v₁, v₂, h1, h2, h12, g1, g2⟩
        · by_cases g3 : ∃ s : V, (R u v₃).head? = some s ∧ s ∈ X
          · exact ⟨v₁, v₃, h1, h3, h13, g1, g3⟩
          · exact absurd (hBadEq v₂ v₃ h2 h3 g2 g3) h23
      · by_cases g2 : ∃ s : V, (R u v₂).head? = some s ∧ s ∈ X
        · by_cases g3 : ∃ s : V, (R u v₃).head? = some s ∧ s ∈ X
          · exact ⟨v₂, v₃, h2, h3, h23, g2, g3⟩
          · exact absurd (hBadEq v₁ v₃ h1 h3 g1 g3) h13
        · exact absurd (hBadEq v₁ v₂ h1 h2 g1 g2) h12
    -- off `{a, b}` the two families agree, so their fork sets do
    have hagree : ∀ u : U, u ≠ a → u ≠ b → (ForkAt J R X u ↔ ForkAt J R' X u) := by
      intro u hua hub
      have hRR : ∀ v : U, J.Adj u v → R u v = R' u v := by
        intro v huv
        refine hdiff u v huv ?_
        intro hcon
        rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hua h1
        · exact hub h1
      constructor
      · rintro ⟨v, v', hv, hv', hne, hg, hg'⟩
        exact ⟨v, v', hv, hv', hne, by rw [← hRR v hv]; exact hg,
          by rw [← hRR v' hv']; exact hg'⟩
      · rintro ⟨v, v', hv, hv', hne, hg, hg'⟩
        exact ⟨v, v', hv, hv', hne, by rw [hRR v hv]; exact hg,
          by rw [hRR v' hv']; exact hg'⟩
    have hsubset : (Set.univ : Set U) ⊆ {u : U | ForkAt J R' X u} ∪ ({a, b} : Set U) := by
      intro u _
      by_cases hua : u = a
      · exact Or.inr (by rw [hua]; exact Set.mem_insert _ _)
      · by_cases hub : u = b
        · exact Or.inr (by rw [hub]; exact Set.mem_insert_of_mem _ rfl)
        · exact Or.inl ((hagree u hua hub).mp (hallfork u))
    have hcard4 : Fintype.card U = 4 := by
      have h1 : (Set.univ : Set U).ncard
          ≤ ({u : U | ForkAt J R' X u} ∪ ({a, b} : Set U)).ncard :=
        Set.ncard_le_ncard hsubset (Set.toFinite _)
      have h2 : ({u : U | ForkAt J R' X u} ∪ ({a, b} : Set U)).ncard
          ≤ {u : U | ForkAt J R' X u}.ncard + ({a, b} : Set U).ncard :=
        Set.ncard_union_le _ _
      have h3 : ({a, b} : Set U).ncard ≤ 2 := by
        have h := Set.ncard_insert_le a ({b} : Set U)
        rw [Set.ncard_singleton] at h
        exact h
      have h4 : (Set.univ : Set U).ncard = Fintype.card U := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card]
      have h5 := hJ.1
      omega
    -- a 4-vertex graph of minimum degree `≥ 3` is `K₄`
    have hcomplete : ∀ x z : U, x ≠ z → J.Adj x z := by
      intro x z hxz
      have hdx : 3 ≤ (J.neighborSet x).ncard :=
        SubdivisionCounting.three_le_degree_of_three_connected J hJ x
      have hsub : J.neighborSet x ⊆ ((Set.univ : Set U) \ {x}) := by
        intro w hw
        refine ⟨Set.mem_univ w, ?_⟩
        intro hc
        rw [Set.mem_singleton_iff] at hc
        subst hc
        exact J.irrefl hw
      have hcard3 : ((Set.univ : Set U) \ {x}).ncard = 3 := by
        rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ x), Set.ncard_univ,
          Nat.card_eq_fintype_card, hcard4]
      have heq : J.neighborSet x = (Set.univ : Set U) \ {x} :=
        Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
      have hz : z ∈ J.neighborSet x := by
        rw [heq]
        exact ⟨Set.mem_univ z, fun hc => hxz (Set.mem_singleton_iff.mp hc).symm⟩
      exact hz
    refine Or.inr (Or.inr ⟨⟨Fintype.equivFinOfCardEq hcard4, ?_⟩⟩)
    intro x z
    simp only [SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact ⟨fun h => hcomplete x z h, fun h => h.ne⟩

end Workspace.ProofLemmas.Thm84ForkCountForcesK4
