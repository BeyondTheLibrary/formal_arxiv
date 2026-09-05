import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.BranchClassification

/-!
# The branch half of the rung dictionary — proof attempt 2 (COMPLETE)

All five conjuncts of `branchRungDictionaryAt` are closed; no `sorry`, no new `axiom`.
`#print axioms` gives exactly `propext, Classical.choice, Quot.sound`.

| conjunct | status | where it comes from |
|---|---|---|
| `Function.Injective ι` | closed | `rungEndDictionaryAt` (step 1) |
| `Set.range ι = branchVertices H` | closed | `rungEndDictionaryAt` (step 1) |
| `IsBranch H (B u v) ∧ IsTrackFrom H (B u v) (ι u) (ι v)` | closed | `branchOfRung` (step 2) |
| `φ '' E(B u v) = V(R u v)` | closed | `branchOfRung` step 8 (new work) |
| every branch of `H` is some `B u v` | closed | step 3, via `BranchClassification` |

## Structure

* `two_le_length_of_isBranch` — a branch of a graph with no isolated vertex has `≥ 2` vertices
  (needed because `IsBranch` alone permits a one-vertex track; maximality rules it out).
* `rungEndDictionaryAt` — `Thm84RungEndDictionary.rungEndDictionary` with the isomorphism `φ`
  supplied as an *input* rather than produced.  The proof is that one verbatim; it never uses
  anything about `φ` beyond its being an isomorphism.  This is what makes the branch family
  attach to the caller's own `φ`, which is what the statement demands.
* `branchOfRung` — `Thm82BranchDelta.thm82BranchDelta` restructured so that `φ`, `ι` and `E`
  are inputs (so the branch family shares a single `ι` across all edges of `J`), with the
  `δ`-clauses dropped and the edge-set identification `φ '' E(B) = V(R_uv)` added in step 8.
  The extra conclusion `E u v ∈ trackEdges B` is what the surjectivity argument consumes.
* Surjectivity: given a branch `q`, `BranchClassification.exists_trackEdges_eq_of_isBranch`
  gives `E(q) = E(T a b)` for a `J`-edge `ab`.  The first edge `f` of `T a b` sits at the
  branch-vertex `ι₀ a = ι u`, so `hincid u` names it `E u w` for a `J`-neighbour `w` of `u`.
  The branch `B u w` also carries `f`, so `E(B u w) = E(T c d)` with `f ∈ E(T c d)`;
  `SubdivisionCounting.trackEdges_disjoint` forces `s(c,d) = s(a,b)`, whence
  `E(q) = E(B u w)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84BranchRungDictionaryAt

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm84RungEndDictionary
open Workspace.ProofLemmas.Thm82BranchDelta

/-! ## Step 0: a branch has at least two vertices -/

section Small

variable {W : Type*}

/-- If every vertex of `H` has a neighbour then every branch of `H` has at least two vertices. -/
theorem two_le_length_of_isBranch {H : SimpleGraph W} (hnbr : ∀ w : W, ∃ x : W, H.Adj w x)
    {q : List W} (hq : IsBranch H q) : 2 ≤ q.length := by
  obtain ⟨hqt, hqint, hqmax⟩ := hq
  have hne : q ≠ [] := hqt.1
  have h1 : 1 ≤ q.length := List.length_pos_of_ne_nil hne
  by_contra hcon
  have hlen1 : q.length = 1 := by omega
  obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen1
  obtain ⟨x, hadj⟩ := hnbr w
  have hq' : IsTrackList H [w, x] := by
    refine ⟨by simp, ?_, ?_⟩
    · simp [hadj.ne]
    · intro i hi
      have : i = 0 := by simp at hi; omega
      subst this
      exact hadj
  have hint' : ∀ v ∈ trackInterior ([w, x] : List W), v ∉ branchVertices H := by
    intro v hv
    simp [trackInterior] at hv
  have hsub : trackEdges ([w] : List W) ⊆ trackEdges ([w, x] : List W) := by
    rintro e ⟨i, hi, rfl⟩
    simp at hi
  have hverts : ∀ v ∈ ([w] : List W), v ∈ ([w, x] : List W) := by
    intro v hv
    simp at hv
    simp [hv]
  have hmax := hqmax [w, x] hq' hint' hsub hverts
  have hmem : s(w, x) ∈ trackEdges ([w, x] : List W) := by
    refine ⟨0, by simp, ?_⟩
    simp
  rw [hmax] at hmem
  obtain ⟨i, hi, -⟩ := hmem
  simp at hi

end Small

/-! ## Step 1: the rung-end dictionary at a prescribed isomorphism

This is `Thm84RungEndDictionary.rungEndDictionary` with the isomorphism `φ` supplied as an
input rather than produced; the proof is the same, since it never uses anything about `φ`
beyond its being an isomorphism. -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rungEndDictionaryAt {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (φ : H.lineGraph ≃g G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b})) :
    ∃ (ι : U → W) (E : U → U → Sym2 W),
      Function.Injective ι ∧
      Set.range ι = branchVertices H ∧
      (∀ u v : U, J.Adj u v → E u v ∈ H.edgeSet) ∧
      (∀ u : U, incidentEdges H (ι u) = {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = E u v}) ∧
      (∀ u v v' : U, J.Adj u v → J.Adj u v' → E u v = E u v' → v = v') ∧
      (∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
        IsPathFrom G (R u v) s t → (↑(φ ⟨E u v, he⟩) : V) = s) := by
  classical
  obtain ⟨hR, hbipsub, -⟩ := hForms
  obtain ⟨hsub, hbip⟩ := hbipsub
  obtain ⟨ι₀, T, hι₀, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    fun u => SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hUne : Nonempty U := by
    have := hJ.1
    exact Fintype.card_pos_iff.mp (by omega)
  have hhead : ∀ u v : U, J.Adj u v → ∃ s : V,
      (R u v).head? = some s ∧ s ∈ R u v ∧ s ∈ S u v ∧ s ∈ N u := by
    intro u v huv
    obtain ⟨-, s, t, hp, hsubR, hs, -⟩ := hR u v huv
    have hsR : s ∈ R u v := List.mem_of_mem_head? hp.2.1
    exact ⟨s, hp.2.1, hsR, hsubR s hsR, (hs s hsR).mpr rfl⟩
  have hVne : Nonempty V := by
    obtain ⟨u⟩ := hUne
    obtain ⟨v, hv⟩ : (J.neighborSet u).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; have := hdeg u; omega
    obtain ⟨s, -, -, -, -⟩ := hhead u v hv
    exact ⟨s⟩
  choose! sfun hsHead hsMem hsStrip hsN using hhead
  have hsK : ∀ u v : U, J.Adj u v →
      sfun u v ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}) := by
    intro u v huv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, v, huv, hsMem u v huv⟩
  obtain ⟨u₀⟩ := hUne
  set Emap : U → U → Sym2 W :=
    fun u v => if h : J.Adj u v then (↑(φ.symm ⟨sfun u v, hsK u v h⟩) : Sym2 W)
      else s(ι₀ u₀, ι₀ u₀) with hEmapDef
  have hEmap : ∀ (u v : U) (h : J.Adj u v),
      Emap u v = (↑(φ.symm ⟨sfun u v, hsK u v h⟩) : Sym2 W) := by
    intro u v h; rw [hEmapDef]; exact dif_pos h
  have hEedge : ∀ u v : U, J.Adj u v → Emap u v ∈ H.edgeSet := by
    intro u v h; rw [hEmap u v h]; exact (φ.symm ⟨sfun u v, hsK u v h⟩).2
  have hEφ : ∀ (u v : U) (h : J.Adj u v) (he : Emap u v ∈ H.edgeSet),
      (↑(φ ⟨Emap u v, he⟩) : V) = sfun u v := by
    intro u v h he
    have : (⟨Emap u v, he⟩ : H.edgeSet) = φ.symm ⟨sfun u v, hsK u v h⟩ :=
      Subtype.ext (hEmap u v h)
    rw [this, RelIso.apply_symm_apply]
  have hEdgeNe : ∀ u v v' : U, J.Adj u v → J.Adj u v' → v ≠ v' → s(u, v) ≠ s(u, v') := by
    intro u v v' huv huv' hne hcon
    rcases Sym2.eq_iff.mp hcon with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact hne h2
    · exact absurd huv (by rw [h2]; exact J.loopless.irrefl u)
  have hsne : ∀ u v v' : U, J.Adj u v → J.Adj u v' → v ≠ v' → sfun u v ≠ sfun u v' := by
    intro u v v' huv huv' hne hcon
    have hd := StripSystemBasics.strip_disjoint hSN huv huv' (hEdgeNe u v v' huv huv' hne)
    exact Set.disjoint_left.mp hd (hsStrip u v huv) (hcon ▸ hsStrip u v' huv')
  have hEne : ∀ u v v' : U, J.Adj u v → J.Adj u v' → v ≠ v' → Emap u v ≠ Emap u v' := by
    intro u v v' huv huv' hne heq
    have h1 : (φ.symm ⟨sfun u v, hsK u v huv⟩ : H.edgeSet)
        = φ.symm ⟨sfun u v', hsK u v' huv'⟩ :=
      Subtype.ext (by rw [← hEmap u v huv, ← hEmap u v' huv', heq])
    have h2 := congrArg Subtype.val (φ.symm.injective h1)
    exact hsne u v v' huv huv' hne h2
  have hEmeet : ∀ u v v' : U, J.Adj u v → J.Adj u v' →
      ∃ w : W, w ∈ Emap u v ∧ w ∈ Emap u v' := by
    intro u v v' huv huv'
    rcases eq_or_ne v v' with rfl | hne
    · obtain ⟨w, hw⟩ := sym2_exists_mem (Emap u v)
      exact ⟨w, hw, hw⟩
    · have hadjG : G.Adj (sfun u v) (sfun u v') :=
        StripSystemBasics.Nuv_complete hSN huv huv' hne (sfun u v)
          ⟨hsN u v huv, hsStrip u v huv⟩ (sfun u v') ⟨hsN u v' huv', hsStrip u v' huv'⟩
      have hadjI : (G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b})).Adj
          ⟨sfun u v, hsK u v huv⟩ ⟨sfun u v', hsK u v' huv'⟩ := hadjG
      have hadjL : H.lineGraph.Adj (φ.symm ⟨sfun u v, hsK u v huv⟩)
          (φ.symm ⟨sfun u v', hsK u v' huv'⟩) := φ.symm.map_rel_iff.mpr hadjI
      obtain ⟨-, w, hw1, hw2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadjL
      refine ⟨w, ?_, ?_⟩
      · rw [hEmap u v huv]; exact hw1
      · rw [hEmap u v' huv']; exact hw2
  have hthree : ∀ u : U, ∃ v₁ v₂ v₃ : U, J.Adj u v₁ ∧ J.Adj u v₂ ∧ J.Adj u v₃ ∧
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
    intro u
    have hn := hdeg u
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
  have hIotaEx : ∀ u : U, ∃ w : W, ∀ v : U, J.Adj u v → w ∈ Emap u v := by
    intro u
    obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, h12, h13, h23⟩ := hthree u
    obtain ⟨w, hw1, hw2, hw3⟩ :=
      exists_common_of_three hbip (hEedge u v₁ hv₁) (hEedge u v₂ hv₂) (hEedge u v₃ hv₃)
        (hEne u v₁ v₂ hv₁ hv₂ h12) (hEne u v₁ v₃ hv₁ hv₃ h13) (hEne u v₂ v₃ hv₂ hv₃ h23)
        (hEmeet u v₁ v₂ hv₁ hv₂) (hEmeet u v₁ v₃ hv₁ hv₃) (hEmeet u v₂ v₃ hv₂ hv₃)
    refine ⟨w, fun v hv => ?_⟩
    exact mem_of_meets_three (hEedge u v₁ hv₁) (hEedge u v₂ hv₂) (hEedge u v₃ hv₃)
      (hEne u v₁ v₂ hv₁ hv₂ h12) (hEne u v₁ v₃ hv₁ hv₃ h13) (hEne u v₂ v₃ hv₂ hv₃ h23)
      hw1 hw2 hw3 (hEmeet u v v₁ hv hv₁) (hEmeet u v v₂ hv hv₂) (hEmeet u v v₃ hv hv₃)
  choose ι hιmem using hIotaEx
  have hother : ∀ u v : U, J.Adj u v → ∃ x : W, Emap u v = s(ι u, x) := fun u v hv =>
    Sym2.mem_iff_exists.mp (hιmem u v hv)
  have hιbranch : ∀ u : U, ι u ∈ branchVertices H := by
    intro u
    obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, h12, h13, h23⟩ := hthree u
    obtain ⟨x₁, hx₁⟩ := hother u v₁ hv₁
    obtain ⟨x₂, hx₂⟩ := hother u v₂ hv₂
    obtain ⟨x₃, hx₃⟩ := hother u v₃ hv₃
    have hadj : ∀ (v : U) (x : W), J.Adj u v → Emap u v = s(ι u, x) → H.Adj (ι u) x := by
      intro v x hv hx
      have := hEedge u v hv
      rw [hx] at this
      exact (SimpleGraph.mem_edgeSet _).mp this
    have hn12 : x₁ ≠ x₂ := by
      rintro rfl; exact hEne u v₁ v₂ hv₁ hv₂ h12 (hx₁.trans hx₂.symm)
    have hn13 : x₁ ≠ x₃ := by
      rintro rfl; exact hEne u v₁ v₃ hv₁ hv₃ h13 (hx₁.trans hx₃.symm)
    have hn23 : x₂ ≠ x₃ := by
      rintro rfl; exact hEne u v₂ v₃ hv₂ hv₃ h23 (hx₂.trans hx₃.symm)
    have hsubset : ({x₁, x₂, x₃} : Set W) ⊆ H.neighborSet (ι u) := by
      rintro y (rfl | rfl | rfl)
      · exact hadj v₁ _ hv₁ hx₁
      · exact hadj v₂ _ hv₂ hx₂
      · exact hadj v₃ _ hv₃ hx₃
    have hcard3 : ({x₁, x₂, x₃} : Set W).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨x₁, x₂, x₃, hn12, hn13, hn23, rfl⟩
    show 3 ≤ (H.neighborSet (ι u)).ncard
    calc (3 : ℕ) = ({x₁, x₂, x₃} : Set W).ncard := hcard3.symm
      _ ≤ (H.neighborSet (ι u)).ncard := Set.ncard_le_ncard hsubset (Set.toFinite _)
  have hιinj : Function.Injective ι := by
    intro u u' heq
    by_contra hne
    obtain ⟨v₁, v₂, hv₁, hv₂, h12⟩ :=
      exists_two_mem (two_le_ncard_diff (a := u') (hdeg u))
    obtain ⟨w₁, w₂, hw₁, hw₂, hw12⟩ :=
      exists_two_mem (two_le_ncard_diff (a := u) (hdeg u'))
    obtain ⟨v, w, hvmem, hwmem, hvw⟩ :
        ∃ v w : U, v ∈ J.neighborSet u \ {u'} ∧ w ∈ J.neighborSet u' \ {u} ∧ v ≠ w := by
      by_cases hc : v₁ = w₁
      · exact ⟨v₁, w₂, hv₁, hw₂, by rw [hc]; exact hw12⟩
      · exact ⟨v₁, w₁, hv₁, hw₁, hc⟩
    have huv : J.Adj u v := hvmem.1
    have hu'w : J.Adj u' w := hwmem.1
    have hvu' : v ≠ u' := fun h => hvmem.2 (by rw [h]; rfl)
    have hwu : w ≠ u := fun h => hwmem.2 (by rw [h]; rfl)
    have hnd : [u, v, u', w].Nodup := by
      have e1 : u ≠ v := huv.ne
      have e2 : u' ≠ w := hu'w.ne
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
        not_or, ne_eq]
      have e3 : u ≠ w := Ne.symm hwu
      have e4 : u ≠ u' := hne
      have e5 : v ≠ u' := hvu'
      have e6 : v ≠ w := hvw
      tauto
    have hnotadj : ¬ G.Adj (sfun u v) (sfun u' w) :=
      StripSystemBasics.not_adj_of_disjoint_edges hSN huv hu'w hnd
        (hsStrip u v huv) (hsStrip u' w hu'w)
    have hsdiff : sfun u v ≠ sfun u' w := by
      intro hcon
      have hsymne : s(u, v) ≠ s(u', w) := by
        intro hcon2
        rcases Sym2.eq_iff.mp hcon2 with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hne h1
        · exact hwu h1.symm
      exact Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN huv hu'w hsymne)
        (hsStrip u v huv) (hcon ▸ hsStrip u' w hu'w)
    have hEdgeNe2 : (φ.symm ⟨sfun u v, hsK u v huv⟩ : H.edgeSet)
        ≠ φ.symm ⟨sfun u' w, hsK u' w hu'w⟩ := by
      intro hcon
      exact hsdiff (congrArg Subtype.val (φ.symm.injective hcon))
    have hmem1 : ι u ∈ ((φ.symm ⟨sfun u v, hsK u v huv⟩ : H.edgeSet) : Sym2 W) := by
      rw [← hEmap u v huv]; exact hιmem u v huv
    have hmem2 : ι u ∈ ((φ.symm ⟨sfun u' w, hsK u' w hu'w⟩ : H.edgeSet) : Sym2 W) := by
      rw [← hEmap u' w hu'w, heq]; exact hιmem u' w hu'w
    have hadjL : H.lineGraph.Adj (φ.symm ⟨sfun u v, hsK u v huv⟩)
        (φ.symm ⟨sfun u' w, hsK u' w hu'w⟩) :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hEdgeNe2, ι u, hmem1, hmem2⟩
    exact hnotadj (φ.symm.map_rel_iff.mp hadjL)
  have hbranchrange : branchVertices H = Set.range ι₀ :=
    Set.Subset.antisymm
      (SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges)
      (SubdivisionCounting.range_subset_branchVertices hι₀ htrack hlen hdisjint hnew hdeg)
  have hrangecard : ∀ f : U → W, Function.Injective f → (Set.range f).ncard = Nat.card U := by
    intro f hf
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hf, Set.ncard_univ]
  have hrange : Set.range ι = branchVertices H := by
    refine Set.eq_of_subset_of_ncard_le (fun w hw => ?_) ?_ (Set.toFinite _)
    · obtain ⟨u, rfl⟩ := hw
      exact hιbranch u
    · rw [hbranchrange, hrangecard ι₀ hι₀, hrangecard ι hιinj]
  have hincl : ∀ u : U, {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = Emap u v} ⊆
      incidentEdges H (ι u) := by
    rintro u e ⟨v, hv, rfl⟩
    exact ⟨hEedge u v hv, hιmem u v hv⟩
  have hinjOn : ∀ u : U, Set.InjOn (Emap u) (J.neighborSet u) := by
    intro u v hv v' hv' heq
    by_contra h
    exact hEne u v v' hv hv' h heq
  have hle : ∀ u : U, (J.neighborSet u).ncard ≤ (H.neighborSet (ι u)).ncard := by
    intro u
    rw [← incidentEdges_ncard (H := H) (ι u)]
    exact Set.ncard_le_ncard_of_injOn (Emap u)
      (fun v hv => ⟨hEedge u v hv, hιmem u v hv⟩) (hinjOn u) (Set.toFinite _)
  have hsigmaEx : ∀ u : U, ∃ p : U, ι₀ p = ι u := by
    intro u
    have : ι u ∈ Set.range ι₀ := by rw [← hbranchrange]; exact hιbranch u
    exact this
  choose σ hσ using hsigmaEx
  have hσinj : Function.Injective σ := by
    intro a b hab
    exact hιinj (by rw [← hσ a, ← hσ b, hab])
  have hσbij : Function.Bijective σ := (Finite.injective_iff_bijective).mp hσinj
  have hsum : ∑ u : U, (H.neighborSet (ι u)).ncard
      = ∑ p : U, (H.neighborSet (ι₀ p)).ncard := by
    refine Fintype.sum_bijective σ hσbij _ _ ?_
    intro u
    rw [hσ u]
  have hsumle : ∑ u : U, (J.neighborSet u).ncard = ∑ u : U, (H.neighborSet (ι u)).ncard := by
    refine le_antisymm (Finset.sum_le_sum fun u _ => hle u) ?_
    rw [hsum]
    exact Finset.sum_le_sum fun p _ =>
      degree_branch_le hι₀ htrack hlen hrev hnew hedges p
  have hdegeq : ∀ u : U, (J.neighborSet u).ncard = (H.neighborSet (ι u)).ncard := by
    intro u
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsumle u (Finset.mem_univ u)
  have hcount : ∀ u : U, (incidentEdges H (ι u)).ncard = (J.neighborSet u).ncard := by
    intro u
    rw [incidentEdges_ncard, ← hdegeq u]
  have himg : ∀ u : U, {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = Emap u v}
      = (Emap u) '' (J.neighborSet u) := by
    intro u
    ext e
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  refine ⟨ι, Emap, hιinj, hrange, hEedge, ?_, ?_, ?_⟩
  · intro u
    refine (Set.eq_of_subset_of_ncard_le (hincl u) ?_ (Set.toFinite _)).symm
    rw [himg u, Set.ncard_image_of_injOn (hinjOn u), hcount u]
  · intro u v v' huv huv' heq
    by_contra hne
    exact hEne u v v' huv huv' hne heq
  · intro u v huv he s t hst
    rw [hEφ u v huv he]
    have h1 : (R u v).head? = some (sfun u v) := hsHead u v huv
    have h2 : (R u v).head? = some s := hst.2.1
    exact Option.some_injective _ (h1.symm.trans h2)

/-! ## Step 2: the branch attached to one edge of `J`, and the rung it carries -/

theorem branchOfRung {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (φ : H.lineGraph ≃g G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
    (ι : U → W) (E : U → U → Sym2 W)
    (hιinj : Function.Injective ι)
    (hrange : Set.range ι = branchVertices H)
    (hEedge : ∀ u v : U, J.Adj u v → E u v ∈ H.edgeSet)
    (hincid : ∀ u : U, incidentEdges H (ι u) = {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = E u v})
    (hEinj : ∀ u v v' : U, J.Adj u v → J.Adj u v' → E u v = E u v' → v = v')
    (hEφ : ∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
        IsPathFrom G (R u v) s t → (↑(φ ⟨E u v, he⟩) : V) = s)
    (u v : U) (huv : J.Adj u v) :
    ∃ B : List W, IsBranch H B ∧ IsTrackFrom H B (ι u) (ι v) ∧
      E u v ∈ trackEdges B ∧
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)} = {x : V | x ∈ R u v} := by
  classical
  have hbip : H.IsBipartite := hForms.2.1.2
  ---------------------------------------------------------------------------
  -- 1.  The `a`-end of the rung on the edge `ab`, and its `φ`-preimage `E a b`.
  ---------------------------------------------------------------------------
  have hheadData : ∀ a b : U, J.Adj a b → ∃ s : V,
      (R a b).head? = some s ∧ s ∈ R a b ∧ s ∈ S a b ∧ s ∈ N a ∧
      (∀ he : E a b ∈ H.edgeSet, (↑(φ ⟨E a b, he⟩) : V) = s) := by
    intro a b hab
    obtain ⟨-, s, t, hp, hsubs, hs, -⟩ := hForms.1 a b hab
    have hsR : s ∈ R a b := List.mem_of_mem_head? hp.2.1
    exact ⟨s, hp.2.1, hsR, hsubs s hsR, (hs s hsR).mpr rfl, fun he => hEφ a b hab he s t hp⟩
  choose! sf hsfHead hsfMem hsfStrip hsfN hsfφ using hheadData
  have hincidMem : ∀ (a : U) (e : Sym2 W), e ∈ H.edgeSet → ι a ∈ e →
      ∃ b : U, J.Adj a b ∧ e = E a b := by
    intro a e he hae
    have hmem : e ∈ incidentEdges H (ι a) := ⟨he, hae⟩
    rw [hincid a] at hmem
    exact hmem
  have hEmemIncid : ∀ a b : U, J.Adj a b → ι a ∈ E a b := by
    intro a b hab
    have hmem : E a b ∈ incidentEdges H (ι a) := by rw [hincid a]; exact ⟨b, hab, rfl⟩
    exact hmem.2
  ---------------------------------------------------------------------------
  -- 2.  The rung `R_uv`, indexed by a total function.
  ---------------------------------------------------------------------------
  obtain ⟨-, s₀, t₀, hpath, hstrip, hNu, hNv⟩ := hForms.1 u v huv
  have hLne : R u v ≠ [] := hpath.1.1
  have hn1 : 1 ≤ (R u v).length := List.length_pos_of_ne_nil hLne
  have hLnodup : (R u v).Nodup := hpath.1.2.1
  have hHead : (R u v)[0]'(by omega) = s₀ := by
    have h1 := hpath.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some_injective _ h1
  have hLast : (R u v)[(R u v).length - 1]'(by omega) = t₀ := by
    have h1 := hpath.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some_injective _ h1
  obtain ⟨idx, hidxlt, hidxMem⟩ :
      ∃ f : ℕ → V, (∀ (i : ℕ) (hi : i < (R u v).length), f i = (R u v)[i]'hi) ∧
        (∀ i : ℕ, f i ∈ R u v) := by
    refine ⟨fun i => ((R u v)[i]?).getD ((R u v)[0]'(by omega)), ?_, ?_⟩
    · intro i hi
      simp [List.getElem?_eq_getElem hi]
    · intro i
      by_cases hi : i < (R u v).length
      · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem hi
      · simp only [List.getElem?_eq_none (show (R u v).length ≤ i by omega), Option.getD_none]
        exact List.getElem_mem _
  have hidxK : ∀ i : ℕ,
      idx i ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}) := by
    intro i
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, v, huv, hidxMem i⟩
  have hkeyNu : ∀ i : ℕ, i < (R u v).length → idx i ∈ N u → i = 0 := by
    intro i hi hmem
    have h1 : idx i = s₀ := (hNu (idx i) (hidxMem i)).mp hmem
    rw [hidxlt i hi] at h1
    have h2 : (R u v)[i]'hi = (R u v)[0]'(show 0 < (R u v).length by omega) := by
      rw [h1, hHead]
    exact hLnodup.getElem_inj_iff.mp h2
  have hkeyNv : ∀ i : ℕ, i < (R u v).length → idx i ∈ N v → i = (R u v).length - 1 := by
    intro i hi hmem
    have h1 : idx i = t₀ := (hNv (idx i) (hidxMem i)).mp hmem
    rw [hidxlt i hi] at h1
    have h2 : (R u v)[i]'hi
        = (R u v)[(R u v).length - 1]'(show (R u v).length - 1 < (R u v).length by omega) := by
      rw [h1, hLast]
    exact hLnodup.getElem_inj_iff.mp h2
  ---------------------------------------------------------------------------
  -- 3.  `E(B) = V(R_uv)`: the edges of `H` corresponding to the rung.
  ---------------------------------------------------------------------------
  obtain ⟨ef, hefφ⟩ : ∃ f : ℕ → H.edgeSet, ∀ i : ℕ, (↑(φ (f i)) : V) = idx i :=
    ⟨fun i => φ.symm ⟨idx i, hidxK i⟩, fun i => by rw [RelIso.apply_symm_apply]⟩
  obtain ⟨ee, heedef⟩ : ∃ g : ℕ → Sym2 W, ∀ i : ℕ, g i = ((ef i : H.edgeSet) : Sym2 W) :=
    ⟨fun i => ((ef i : H.edgeSet) : Sym2 W), fun _ => rfl⟩
  have heeEdge : ∀ i : ℕ, ee i ∈ H.edgeSet := by
    intro i; rw [heedef i]; exact (ef i).2
  have hefNe : ∀ i j : ℕ, i < (R u v).length → j < (R u v).length → i ≠ j → ef i ≠ ef j := by
    intro i j hi hj hij hcon
    have h1 : idx i = idx j := by rw [← hefφ i, ← hefφ j, hcon]
    rw [hidxlt i hi, hidxlt j hj] at h1
    exact hij (hLnodup.getElem_inj_iff.mp h1)
  have hefAdj : ∀ i j : ℕ, i < (R u v).length → j < (R u v).length →
      (H.lineGraph.Adj (ef i) (ef j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    have key : H.lineGraph.Adj (ef i) (ef j) ↔ G.Adj (idx i) (idx j) := by
      constructor
      · intro h
        have h3 : G.Adj (↑(φ (ef i))) (↑(φ (ef j))) := φ.map_rel_iff.mpr h
        rwa [hefφ i, hefφ j] at h3
      · intro h
        have h3 : G.Adj (↑(φ (ef i))) (↑(φ (ef j))) := by rw [hefφ i, hefφ j]; exact h
        exact φ.map_rel_iff.mp h3
    rw [key, hidxlt i hi, hidxlt j hj]
    exact hpath.1.2.2 i j hi hj
  have hMeet : ∀ i : ℕ, i + 1 < (R u v).length → ∃ w : W, w ∈ ee i ∧ w ∈ ee (i + 1) := by
    intro i hi
    have hadj : H.lineGraph.Adj (ef i) (ef (i + 1)) :=
      (hefAdj i (i + 1) (by omega) hi).mpr (Or.inl rfl)
    obtain ⟨-, w, hw1, hw2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
    exact ⟨w, by rw [heedef i]; exact hw1, by rw [heedef (i + 1)]; exact hw2⟩
  have hDisj : ∀ i j : ℕ, i < (R u v).length → j < (R u v).length →
      ¬ (i + 1 = j ∨ j + 1 = i) → i ≠ j → ∀ w : W, w ∈ ee i → w ∈ ee j → False := by
    intro i j hi hj hcons hne w hw1 hw2
    rw [heedef i] at hw1
    rw [heedef j] at hw2
    have hadj : H.lineGraph.Adj (ef i) (ef j) :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hefNe i j hi hj hne, w, hw1, hw2⟩
    exact hcons ((hefAdj i j hi hj).mp hadj)
  have hee0 : ee 0 = E u v := by
    have h1 : idx 0 = sf u v huv := by
      have h2 : (R u v)[0]? = some (sf u v huv) := by
        rw [← List.head?_eq_getElem?]; exact hsfHead u v huv
      rw [hidxlt 0 (by omega)]
      have h3 := List.getElem?_eq_getElem (show 0 < (R u v).length by omega)
      rw [h3] at h2
      exact Option.some_injective _ h2
    have h4 : φ (ef 0) = φ ⟨E u v, hEedge u v huv⟩ :=
      Subtype.ext (by rw [hefφ 0, h1, hsfφ u v huv (hEedge u v huv)])
    have h5 : ef 0 = ⟨E u v, hEedge u v huv⟩ := φ.injective h4
    rw [heedef 0, h5]
  have hstepN : ∀ (a : U) (m : ℕ), m < (R u v).length → ι a ∈ ee m → idx m ∈ N a := by
    intro a m hm hmem
    obtain ⟨b, hb, hEq⟩ := hincidMem a (ee m) (heeEdge m) hmem
    have h5 : ef m = ⟨E a b, hEedge a b hb⟩ :=
      Subtype.ext (by rw [← heedef m]; exact hEq)
    have h6 : idx m = sf a b hb := by
      rw [← hefφ m, h5]; exact hsfφ a b hb (hEedge a b hb)
    rw [h6]; exact hsfN a b hb
  have hstepUV : ∀ (a : U) (m : ℕ), m < (R u v).length → ι a ∈ ee m → a = u ∨ a = v := by
    intro a m hm hmem
    have hNa := hstepN a m hm hmem
    by_contra hc
    push_neg at hc
    have hempty := StripSystemBasics.strip_inter_N_eq_empty hSN huv hc.1 hc.2
    have : idx m ∈ S u v ∩ N a := ⟨hstrip (idx m) (hidxMem m), hNa⟩
    rw [hempty] at this
    exact this
  ---------------------------------------------------------------------------
  -- 4.  Walking the edge list back into a track of `H`.
  ---------------------------------------------------------------------------
  obtain ⟨wf, hwf0, hwfs⟩ :
      ∃ f : ℕ → W, f 0 = ι u ∧ ∀ k : ℕ, f (k + 1) = otherEnd (ee k) (f k) :=
    ⟨fun i => Nat.rec (motive := fun _ => W) (ι u) (fun k acc => otherEnd (ee k) acc) i,
      rfl, fun _ => rfl⟩
  have hIotaU1 : 1 < (R u v).length → ι u ∉ ee 1 := by
    intro h1n hcon
    have := hkeyNu 1 h1n (hstepN u 1 h1n hcon)
    omega
  have hinv : ∀ i : ℕ, i < (R u v).length →
      (wf i ∈ ee i ∧ (i + 1 < (R u v).length → wf i ∉ ee (i + 1))) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [hwf0, hee0]; exact hEmemIncid u v huv
      · intro h1n; rw [hwf0]; exact hIotaU1 h1n
    | succ k IH =>
      intro hk1
      obtain ⟨hmem, hnot⟩ := IH (by omega)
      have hnotk : wf k ∉ ee (k + 1) := hnot hk1
      have hedgek : ee k = s(wf k, wf (k + 1)) := by
        rw [hwfs k]; exact otherEnd_spec hmem
      obtain ⟨c, hc1, hc2⟩ := hMeet k hk1
      have hcw : c = wf (k + 1) := by
        rw [hedgek] at hc1
        rcases Sym2.mem_iff.mp hc1 with h | h
        · exact absurd (by rw [← h]; exact hc2) hnotk
        · exact h
      subst hcw
      refine ⟨hc2, ?_⟩
      intro hk2 hcon
      have hmemk : wf (k + 1) ∈ ee k := by rw [hedgek]; exact Sym2.mem_mk_right _ _
      exact hDisj k (k + 2) (by omega) hk2 (by omega) (by omega) _ hmemk hcon
  have hedge : ∀ i : ℕ, i < (R u v).length → ee i = s(wf i, wf (i + 1)) := by
    intro i hi
    rw [hwfs i]; exact otherEnd_spec (hinv i hi).1
  have hadjW : ∀ i : ℕ, i < (R u v).length → H.Adj (wf i) (wf (i + 1)) := by
    intro i hi
    have h := heeEdge i
    rw [hedge i hi] at h
    exact h
  have hwfNe : ∀ i : ℕ, i < (R u v).length → wf i ≠ wf (i + 1) := fun i hi => (hadjW i hi).ne
  have hwfMemPrev : ∀ i : ℕ, i < (R u v).length → wf (i + 1) ∈ ee i := by
    intro i hi; rw [hedge i hi]; exact Sym2.mem_mk_right _ _
  have hwfInj : ∀ i j : ℕ, i ≤ (R u v).length → j ≤ (R u v).length → i < j → wf i ≠ wf j := by
    intro i j hi hj hij hcon
    have hi' : i < (R u v).length := by omega
    have hjm : j - 1 < (R u v).length := by omega
    have hmem1 : wf i ∈ ee i := (hinv i hi').1
    have hmem2 : wf j ∈ ee (j - 1) := by
      have h := hwfMemPrev (j - 1) hjm
      rwa [show j - 1 + 1 = j from by omega] at h
    rw [hcon] at hmem1
    rcases Nat.lt_or_ge (i + 1) j with hlt | hge
    · by_cases hcase : j - 1 = i + 1
      · have h1 : wf j ∈ ee (i + 1) := by rwa [hcase] at hmem2
        have h2 : wf (i + 1) ∈ ee i := hwfMemPrev i hi'
        have h3 : wf (i + 1) ∈ ee (i + 1) := (hinv (i + 1) (by omega)).1
        have hneEE : ee i ≠ ee (i + 1) := by
          intro hc
          refine hefNe i (i + 1) hi' (by omega) (by omega) (Subtype.ext ?_)
          rw [← heedef i, ← heedef (i + 1), hc]
        have h4 := subsingleton_inter_of_ne hneEE hmem1 h1 h2 h3
        exact hwfNe i hi' (hcon.trans h4)
      · exact hDisj i (j - 1) hi' hjm (by omega) (by omega) _ hmem1 hmem2
    · have hji : j = i + 1 := by omega
      subst hji
      exact hwfNe i hi' hcon
  ---------------------------------------------------------------------------
  -- 5.  The track `B`.
  ---------------------------------------------------------------------------
  obtain ⟨B, hBlen, hBget⟩ :
      ∃ l : List W, l.length = (R u v).length + 1 ∧
        ∀ (i : ℕ) (hi : i < l.length), l[i]'hi = wf i := by
    refine ⟨List.ofFn (fun i : Fin ((R u v).length + 1) => wf (i : ℕ)), by simp, ?_⟩
    intro i hi
    simp only [List.getElem_ofFn]
  have hBnodup : B.Nodup := by
    rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj
    intro hcon
    have hi : i < B.length := by omega
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hcon
    have h1 := Option.some_injective _ hcon
    rw [hBget i hi, hBget j hj] at h1
    exact hwfInj i j (by omega) (by omega) hij h1
  have hBtrack : IsTrackList H B := by
    refine ⟨?_, hBnodup, ?_⟩
    · intro hcon
      rw [hcon] at hBlen
      simp at hBlen
    · intro i hi
      rw [hBget i (by omega), hBget (i + 1) hi]
      exact hadjW i (by omega)
  have hBhead : B.head? = some (ι u) := by
    have h0 : 0 < B.length := by omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0, hBget 0 h0, hwf0]
  have hBlast : B.getLast? = some (wf ((R u v).length)) := by
    have h0 : (R u v).length < B.length := by omega
    rw [List.getLast?_eq_getElem?, show B.length - 1 = (R u v).length from by omega,
      List.getElem?_eq_getElem h0, hBget _ h0]
  ---------------------------------------------------------------------------
  -- 6.  The far end of `B` is the branch-vertex `ι v`.
  ---------------------------------------------------------------------------
  have hdegv : 3 ≤ (J.neighborSet v).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ v
  obtain ⟨w₁, w₂, hw₁, hw₂, hw12⟩ :=
    exists_two_mem (two_le_ncard_diff (s := J.neighborSet v) (a := u) hdegv)
  have hvw₁ : J.Adj v w₁ := hw₁.1
  have hvw₂ : J.Adj v w₂ := hw₂.1
  have hw₁u : u ≠ w₁ := fun h => hw₁.2 (by simp [h])
  have hw₂u : u ≠ w₂ := fun h => hw₂.2 (by simp [h])
  have hMeetEnd : ∀ w : U, J.Adj v w → u ≠ w →
      ∃ z : W, z ∈ ee ((R u v).length - 1) ∧ z ∈ E v w := by
    intro w hvw hwu
    have hidxNv : idx ((R u v).length - 1) ∈ N v := by
      rw [hidxlt _ (by omega), hLast]
      have := hNv t₀ (List.mem_of_getLast? hpath.2.2)
      exact this.mpr rfl
    have hidxSvu : idx ((R u v).length - 1) ∈ S v u := by
      rw [← StripSystemBasics.strip_symm hSN huv]
      exact hstrip _ (hidxMem _)
    have hadjG : G.Adj (idx ((R u v).length - 1)) (sf v w hvw) :=
      StripSystemBasics.Nuv_complete hSN huv.symm hvw hwu
        (idx ((R u v).length - 1)) ⟨hidxNv, hidxSvu⟩
        (sf v w hvw) ⟨hsfN v w hvw, hsfStrip v w hvw⟩
    have hadjI : G.Adj (↑(φ (ef ((R u v).length - 1))))
        (↑(φ (⟨E v w, hEedge v w hvw⟩ : H.edgeSet))) := by
      rw [hefφ _, hsfφ v w hvw (hEedge v w hvw)]
      exact hadjG
    have hadjL : H.lineGraph.Adj (ef ((R u v).length - 1)) ⟨E v w, hEedge v w hvw⟩ :=
      φ.map_rel_iff.mp hadjI
    obtain ⟨-, z, hz1, hz2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadjL
    exact ⟨z, by rw [heedef _]; exact hz1, hz2⟩
  have hIotaVmem : ι v ∈ ee ((R u v).length - 1) := by
    by_contra hcon
    obtain ⟨z₁, hz₁a, hz₁b⟩ := hMeetEnd w₁ hvw₁ hw₁u
    obtain ⟨z₂, hz₂a, hz₂b⟩ := hMeetEnd w₂ hvw₂ hw₂u
    obtain ⟨x₁, hx₁⟩ := Sym2.mem_iff_exists.mp (hEmemIncid v w₁ hvw₁)
    obtain ⟨x₂, hx₂⟩ := Sym2.mem_iff_exists.mp (hEmemIncid v w₂ hvw₂)
    have hz₁x : z₁ = x₁ := by
      rw [hx₁] at hz₁b
      rcases Sym2.mem_iff.mp hz₁b with h | h
      · exact absurd (by rw [← h]; exact hz₁a) hcon
      · exact h
    have hz₂x : z₂ = x₂ := by
      rw [hx₂] at hz₂b
      rcases Sym2.mem_iff.mp hz₂b with h | h
      · exact absurd (by rw [← h]; exact hz₂a) hcon
      · exact h
    have hx12 : x₁ ≠ x₂ := by
      intro hc
      have hEE : E v w₁ = E v w₂ := by rw [hx₁, hx₂, hc]
      exact hw12 (hEinj v w₁ w₂ hvw₁ hvw₂ hEE)
    have hx₁mem : x₁ ∈ ee ((R u v).length - 1) := by rw [← hz₁x]; exact hz₁a
    have hx₂mem : x₂ ∈ ee ((R u v).length - 1) := by rw [← hz₂x]; exact hz₂a
    have heeeq : ee ((R u v).length - 1) = s(x₁, x₂) :=
      eq_sym2_of_mem_mem hx12 hx₁mem hx₂mem
    have hadj12 : H.Adj x₁ x₂ := by
      have h := heeEdge ((R u v).length - 1)
      rw [heeeq] at h
      exact h
    have hadjv1 : H.Adj (ι v) x₁ := by
      have h := hEedge v w₁ hvw₁
      rw [hx₁] at h
      exact h
    have hadjv2 : H.Adj (ι v) x₂ := by
      have h := hEedge v w₂ hvw₂
      rw [hx₂] at h
      exact h
    exact no_triangle_of_bipartite hbip hadjv1 hadj12 hadjv2
  have hιuv : ι u ≠ ι v := fun h => huv.ne (hιinj h)
  have hwfEnd : wf ((R u v).length) = ι v := by
    have hedgeE : ee ((R u v).length - 1)
        = s(wf ((R u v).length - 1), wf ((R u v).length)) := by
      have h := hedge ((R u v).length - 1) (by omega)
      rwa [show (R u v).length - 1 + 1 = (R u v).length from by omega] at h
    have hmem := hIotaVmem
    rw [hedgeE] at hmem
    rcases Sym2.mem_iff.mp hmem with h | h
    · exfalso
      by_cases hnn : (R u v).length = 1
      · rw [hnn] at h
        simp only [Nat.sub_self] at h
        rw [hwf0] at h
        exact hιuv h.symm
      · have hprev : wf ((R u v).length - 1) ∈ ee ((R u v).length - 2) := by
          have h2 := hwfMemPrev ((R u v).length - 2) (by omega)
          rwa [show (R u v).length - 2 + 1 = (R u v).length - 1 from by omega] at h2
        have h3 : ι v ∈ ee ((R u v).length - 2) := by rw [h]; exact hprev
        have h4 := hkeyNv ((R u v).length - 2) (by omega)
          (hstepN v ((R u v).length - 2) (by omega) h3)
        omega
    · exact h.symm
  ---------------------------------------------------------------------------
  -- 7.  `B` is a branch: its interior avoids the branch-vertices.
  ---------------------------------------------------------------------------
  have hBint : ∀ w ∈ trackInterior B, w ∉ branchVertices H := by
    intro w hw hbr
    rw [SubdivisionCounting.mem_trackInterior_iff] at hw
    obtain ⟨j, hj, hjw⟩ := hw
    have hi1 : 1 ≤ j + 1 := by omega
    have hin : j + 1 < (R u v).length := by omega
    have hwi : w = wf (j + 1) := by rw [← hjw]; exact hBget _ _
    rw [← hrange] at hbr
    obtain ⟨a, ha⟩ := hbr
    have haw : ι a = wf (j + 1) := ha.trans hwi
    have hmemA : wf (j + 1) ∈ ee j := hwfMemPrev j (by omega)
    have hmemB : wf (j + 1) ∈ ee (j + 1) := (hinv (j + 1) hin).1
    have hau : a = u ∨ a = v := hstepUV a (j + 1) hin (by rw [haw]; exact hmemB)
    rcases hau with hau1 | hau1
    · have hNa := hstepN a (j + 1) hin (by rw [haw]; exact hmemB)
      rw [hau1] at hNa
      have := hkeyNu (j + 1) hin hNa
      omega
    · have hNa := hstepN a j (by omega) (by rw [haw]; exact hmemA)
      rw [hau1] at hNa
      have := hkeyNv j (by omega) hNa
      omega
  have hBfrom : IsTrackFrom H B (ι u) (ι v) := ⟨hBtrack, hBhead, by rw [hBlast, hwfEnd]⟩
  have hBbranch : IsBranch H B := by
    refine isBranch_of_ends_branch hBfrom hιuv hBint ?_ ?_
    · rw [← hrange]; exact ⟨u, rfl⟩
    · rw [← hrange]; exact ⟨v, rfl⟩
  ---------------------------------------------------------------------------
  -- 8.  `φ` carries the edges of `B` onto the vertices of the rung.
  ---------------------------------------------------------------------------
  have htrackB : trackEdges B = {e : Sym2 W | ∃ i : ℕ, i < (R u v).length ∧ e = ee i} := by
    ext e
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i, by omega, ?_⟩
      rw [hBget i (by omega), hBget (i + 1) hi, hedge i (by omega)]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i, by omega, ?_⟩
      rw [hBget i (by omega), hBget (i + 1) (by omega), hedge i hi]
  have hφee : ∀ (i : ℕ) (hi : ee i ∈ H.edgeSet), (↑(φ ⟨ee i, hi⟩) : V) = idx i := by
    intro i hi
    have hsub : (⟨ee i, hi⟩ : H.edgeSet) = ef i := Subtype.ext (heedef i)
    rw [hsub, hefφ i]
  refine ⟨B, hBbranch, hBfrom, ?_, ?_⟩
  · rw [htrackB]
    exact ⟨0, by omega, hee0.symm⟩
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨e, he, hemem, rfl⟩
      rw [htrackB] at hemem
      obtain ⟨i, hi, rfl⟩ := hemem
      rw [hφee i he, hidxlt i hi]
      exact List.getElem_mem hi
    · intro hx
      obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
      refine ⟨ee i, heeEdge i, ?_, ?_⟩
      · rw [htrackB]; exact ⟨i, hi, rfl⟩
      · rw [hφee i (heeEdge i), hidxlt i hi]
        exact hxi.symm

end Main

/-! ## Step 3: the branch half of the rung dictionary -/

theorem branchRungDictionaryAt {V : Type*} [Fintype V] [DecidableEq V] {U W : Type*}
    [Fintype U] [Fintype W] (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V) (hForms : FormsLineGraph G J S N R H)
    (φ : H.lineGraph ≃g G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b})) :
    ∃ (ι : U → W) (B : U → U → List W),
      Function.Injective ι ∧ Set.range ι = branchVertices H ∧
      (∀ u v : U, J.Adj u v → IsBranch H (B u v) ∧ IsTrackFrom H (B u v) (ι u) (ι v)) ∧
      (∀ u v : U, J.Adj u v →
        {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
          e ∈ trackEdges (B u v) ∧ x = (↑(φ ⟨e, he⟩) : V)} = {x : V | x ∈ R u v}) ∧
      (∀ q : List W, IsBranch H q → ∃ u v : U, J.Adj u v ∧ trackEdges q = trackEdges (B u v)) := by
  classical
  obtain ⟨ι₀, T, hι₀, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hForms.2.1.1
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    fun u => SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  obtain ⟨ι, E, hιinj, hrange, hEedge, hincid, hEinj, hEφ⟩ :=
    rungEndDictionaryAt G J hJ S N hSN H R hForms φ
  -- the branch family
  have hex : ∀ u v : U, J.Adj u v → ∃ Bq : List W, IsBranch H Bq ∧
      IsTrackFrom H Bq (ι u) (ι v) ∧ E u v ∈ trackEdges Bq ∧
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges Bq ∧ x = (↑(φ ⟨e, he⟩) : V)} = {x : V | x ∈ R u v} := by
    intro u v huv
    exact branchOfRung G J hJ S N hSN H R hForms φ ι E hιinj hrange hEedge
      hincid hEinj hEφ u v huv
  choose! B hBbranch hBfrom hBedge hBrung using hex
  -- every vertex of `H` has a neighbour
  have hnbr : ∀ w : W, ∃ x : W, H.Adj w x := by
    intro w
    rcases hcover w with ⟨a, rfl⟩ | ⟨a, b, hab, hw⟩
    · have hb : ι₀ a ∈ branchVertices H :=
        SubdivisionCounting.range_subset_branchVertices hι₀ htrack hlen hdisjint hnew hdeg
          ⟨a, rfl⟩
      have h3 : 3 ≤ (H.neighborSet (ι₀ a)).ncard := hb
      obtain ⟨x, hx⟩ : (H.neighborSet (ι₀ a)).Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _)]; omega
      exact ⟨x, hx⟩
    · rw [SubdivisionCounting.mem_trackInterior_iff] at hw
      obtain ⟨j, hj, hjw⟩ := hw
      refine ⟨(T a b)[j + 2]'(by omega), ?_⟩
      rw [← hjw]
      exact (htrack a b hab).1.2.2 (j + 1) (by omega)
  -- surjectivity
  have hsurj : ∀ q : List W, IsBranch H q →
      ∃ u v : U, J.Adj u v ∧ trackEdges q = trackEdges (B u v) := by
    intro q hq
    have hq2 : 2 ≤ q.length := two_le_length_of_isBranch hnbr hq
    obtain ⟨a, b, hab, hqT⟩ :=
      BranchClassification.exists_trackEdges_eq_of_isBranch hι₀ htrack hlen hrev hdisjint
        hnew hcover hedges hdeg hq hq2
    -- the first edge of `T a b`
    have hTlen : 2 ≤ (T a b).length := by
      have := hlen a b hab
      simp only [trackLength] at this
      omega
    have hT0 : (T a b)[0]'(by omega) = ι₀ a :=
      SubdivisionCounting.track_head (htrack a b hab) (by omega)
    set f : Sym2 W := s((T a b)[0]'(by omega), (T a b)[1]'(by omega)) with hf
    have hfT : f ∈ trackEdges (T a b) := ⟨0, by omega, rfl⟩
    have hfE : f ∈ H.edgeSet := by
      have := (htrack a b hab).1.2.2 0 (by omega)
      exact this
    have hfmem : ι₀ a ∈ f := by
      rw [hf, ← hT0]
      exact Sym2.mem_mk_left _ _
    -- `ι₀ a` is a branch-vertex, hence `ι u` for some `u`
    have hbr : ι₀ a ∈ branchVertices H :=
      SubdivisionCounting.range_subset_branchVertices hι₀ htrack hlen hdisjint hnew hdeg
        ⟨a, rfl⟩
    obtain ⟨u, hu⟩ : ι₀ a ∈ Set.range ι := by rw [hrange]; exact hbr
    have hfincid : f ∈ incidentEdges H (ι u) := ⟨hfE, by rw [hu]; exact hfmem⟩
    rw [hincid u] at hfincid
    obtain ⟨w, huw, hfw⟩ := hfincid
    -- the branch `B u w` also carries the edge `f`
    have hBw2 : 2 ≤ (B u w).length := two_le_length_of_isBranch hnbr (hBbranch u w huw)
    obtain ⟨c, d, hcd, hBT⟩ :=
      BranchClassification.exists_trackEdges_eq_of_isBranch hι₀ htrack hlen hrev hdisjint
        hnew hcover hedges hdeg (hBbranch u w huw) hBw2
    have hfBT : f ∈ trackEdges (T c d) := by
      rw [← hBT, hfw]
      exact hBedge u w huw
    have hsym : s(c, d) = s(a, b) :=
      SubdivisionCounting.trackEdges_disjoint hι₀ htrack hlen hdisjint c d a b hcd hab f
        hfBT hfT
    have hTT : trackEdges (T c d) = trackEdges (T a b) := by
      rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · rw [hrev c d hcd, SubdivisionCounting.trackEdges_reverse]
    exact ⟨u, w, huw, by rw [hqT, ← hTT, hBT]⟩
  refine ⟨ι, B, hιinj, hrange, ?_, ?_, hsurj⟩
  · intro u v huv
    exact ⟨hBbranch u v huv, hBfrom u v huv⟩
  · intro u v huv
    exact hBrung u v huv

end Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
