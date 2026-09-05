import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58MinimalFIsPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm58MinimalFIsPath (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (F : Set V) (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hnotlocal : ¬ LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K})
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (↑(φ ⟨e, he⟩) : V) ∈ attachments G F₁ K} →
      F₁ = F)
    (x₁ x₂ : Sym2 (Fin n)) (hx₁ : x₁ ∈ H.edgeSet) (hx₂ : x₂ ∈ H.edgeSet)
    (hx₁att : (↑(φ ⟨x₁, hx₁⟩) : V) ∈ attachments G F K)
    (hx₂att : (↑(φ ⟨x₂, hx₂⟩) : V) ∈ attachments G F K)
    (hpair : ¬ LocalForLineGraph H {x₁, x₂}) :
    ∃ (P : List V) (p₁ pₙ : V),
      IsPathFrom G P p₁ pₙ ∧ {x : V | x ∈ P} = F ∧
      IsPathFrom G ((↑(φ ⟨x₁, hx₁⟩) : V) :: (P ++ [(↑(φ ⟨x₂, hx₂⟩) : V)]))
        (↑(φ ⟨x₁, hx₁⟩) : V) (↑(φ ⟨x₂, hx₂⟩) : V) ∧
      LocalForLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {pₙ}) K} ∧
      LocalForLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₁}) K} := by
  classical
  ------------------------------------------------------------------
  -- 0.  Generalities
  ------------------------------------------------------------------
  set u : V := (↑(φ ⟨x₁, hx₁⟩) : V) with hudef
  set v : V := (↑(φ ⟨x₂, hx₂⟩) : V) with hvdef
  have hlocmono : ∀ A B : Set (Sym2 (Fin n)), A ⊆ B →
      LocalForLineGraph H B → LocalForLineGraph H A := by
    rintro A B hAB (⟨c, hc, hs⟩ | ⟨q, hq, hs⟩)
    · exact Or.inl ⟨c, hc, hAB.trans hs⟩
    · exact Or.inr ⟨q, hq, hAB.trans hs⟩
  have hattmono : ∀ A B : Set V, A ⊆ B → attachments G A K ⊆ attachments G B K := by
    rintro A B hAB z ⟨hzK, f, hf, hadj⟩
    exact ⟨hzK, f, hAB hf, hadj⟩
  have hXmono : ∀ A B : Set V, A ⊆ B →
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G A K} ⊆
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G B K} := by
    rintro A B hAB e ⟨he, hm⟩
    exact ⟨he, hattmono A B hAB hm⟩
  ------------------------------------------------------------------
  -- 1.  Subdivision bookkeeping (only what claim (1)'s successor needs)
  ------------------------------------------------------------------
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub.1
  have hdeg : ∀ a : Fin m, 3 ≤ (J.neighborSet a).ncard := fun a =>
    SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  have hbv₁ : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlenT hdisjint hnew hdeg
  have hbv₂ : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  have hTint : ∀ a b : Fin m, J.Adj a b → ∀ w ∈ trackInterior (T a b),
      w ∉ branchVertices H := fun a b hab w hw hbr => hnew a b hab w hw (hbv₂ hbr)
  have hTbranch : ∀ a b : Fin m, J.Adj a b → IsBranch H (T a b) := by
    intro a b hab
    exact Thm82BranchDelta.isBranch_of_ends_branch (htrack a b hab)
      (fun h => hab.ne (hι h)) (hTint a b hab) (hbv₁ ⟨a, rfl⟩) (hbv₁ ⟨b, rfl⟩)
  have hedgeTrack : ∀ e ∈ H.edgeSet, ∃ a b : Fin m, J.Adj a b ∧ e ∈ trackEdges (T a b) := by
    intro e he
    rw [hedges] at he
    simp only [Set.mem_iUnion] at he
    obtain ⟨a, b, hab, h⟩ := he
    exact ⟨a, b, hab, h⟩
  have htrackEq : ∀ a b a' b' : Fin m, J.Adj a b → J.Adj a' b' → s(a, b) = s(a', b') →
      trackEdges (T a b) = trackEdges (T a' b') := by
    intro a b a' b' _ ha'b' hs
    rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hrev a' b' ha'b']
      exact SubdivisionCounting.trackEdges_reverse _
  -- a pair of edges of `H` with a common end is local
  have hcommon : ∀ (e f : Sym2 (Fin n)), e ∈ H.edgeSet → f ∈ H.edgeSet →
      ∀ w : Fin n, w ∈ e → w ∈ f → LocalForLineGraph H ({e, f} : Set (Sym2 (Fin n))) := by
    intro e f he hf w hwe hwf
    by_cases hwb : w ∈ branchVertices H
    · refine Or.inl ⟨w, hwb, ?_⟩
      rintro g hg
      rcases hg with rfl | hg
      · exact ⟨he, hwe⟩
      · have : g = f := hg
        rw [this]; exact ⟨hf, hwf⟩
    · rcases hcover w with ⟨a, ha⟩ | ⟨a, b, hab, hwint⟩
      · exact absurd (hbv₁ ⟨a, ha.symm⟩) hwb
      · have key : ∀ g ∈ H.edgeSet, w ∈ g → g ∈ trackEdges (T a b) := by
          intro g hg hwg
          obtain ⟨a', b', ha'b', hgt⟩ := hedgeTrack g hg
          obtain ⟨d, rfl⟩ := Sym2.mem_iff_exists.mp hwg
          have hwT : w ∈ T a' b' := (BranchClassification.mem_of_mem_trackEdges hgt).1
          by_cases hs : s(a, b) = s(a', b')
          · rw [htrackEq a b a' b' hab ha'b' hs]; exact hgt
          · exact absurd hwT (hdisjint a b a' b' hab ha'b' hs w hwint)
        refine Or.inr ⟨T a b, hTbranch a b hab, ?_⟩
        rintro g hg
        rcases hg with rfl | hg
        · exact key _ he hwe
        · have : g = f := hg
          rw [this]; exact key _ hf hwf
  ------------------------------------------------------------------
  -- 2.  `u ≠ v` and `u` is not adjacent to `v`
  ------------------------------------------------------------------
  have huK : u ∈ K := Subtype.coe_prop _
  have hvK : v ∈ K := Subtype.coe_prop _
  have huF : u ∉ F := fun hc => (hFK hc) huK
  have hvF : v ∉ F := fun hc => (hFK hc) hvK
  have huv : u ≠ v := by
    intro hc
    apply hpair
    have hx : x₁ = x₂ := congrArg Subtype.val (φ.injective (Subtype.ext hc))
    obtain ⟨a, b, hab, hxt⟩ := hedgeTrack x₁ hx₁
    refine Or.inr ⟨T a b, hTbranch a b hab, ?_⟩
    rintro g hg
    rcases hg with rfl | hg
    · exact hxt
    · have hgf : g = x₂ := hg
      rw [hgf, ← hx]; exact hxt
  have hnadj : ¬ G.Adj u v := by
    intro hadj
    apply hpair
    have hLadj : H.lineGraph.Adj ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ := by
      refine φ.map_rel_iff.mp ?_
      show G.Adj (↑(φ ⟨x₁, hx₁⟩) : V) (↑(φ ⟨x₂, hx₂⟩) : V)
      exact hadj
    obtain ⟨-, w, hw1, hw2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hLadj
    exact hcommon x₁ x₂ hx₁ hx₂ w hw1 hw2
  ------------------------------------------------------------------
  -- 3.  The path with interior in `F`
  ------------------------------------------------------------------
  obtain ⟨-, hu1⟩ := hx₁att
  obtain ⟨-, hv1⟩ := hx₂att
  obtain ⟨p, hp, h3, hintF, hintconn, ⟨d₁, hd₁, hud₁⟩, ⟨d₂, hd₂, hvd₂⟩⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hFconn huv hnadj huF hvF hu1 hv1
  have hPlist : IsPathList G (SPGT.interior p) := by
    rw [PathBasics.interior_eq_drop_take]
    exact PathBasics.isPathList_take
      (PathBasics.isPathList_drop hp.1 (by omega)) (by omega)
  have hPne : SPGT.interior p ≠ [] := PathBasics.interior_ne_nil hp.1 h3
  have hPnd : (SPGT.interior p).Nodup := hPlist.2.1
  -- minimality forces the interior to be all of `F`
  have hPF : {z : V | z ∈ SPGT.interior p} = F := by
    refine hFmin _ (fun z hz => hintF z hz) hintconn ?_
    intro hc
    refine hpair (hlocmono _ _ ?_ hc)
    rintro g hg
    rcases hg with rfl | hg
    · exact ⟨hx₁, ⟨huK, d₁, hd₁, hud₁⟩⟩
    · have hgf : g = x₂ := hg
      rw [hgf]
      exact ⟨hx₂, ⟨hvK, d₂, hd₂, hvd₂⟩⟩
  ------------------------------------------------------------------
  -- 4.  Naming the two ends of the interior, and the decomposition of `p`
  ------------------------------------------------------------------
  obtain ⟨p1, hp1⟩ : ∃ a : V, (SPGT.interior p).head? = some a :=
    ⟨(SPGT.interior p).head hPne, List.head?_eq_some_head hPne⟩
  obtain ⟨pn, hpn⟩ : ∃ a : V, (SPGT.interior p).getLast? = some a :=
    ⟨(SPGT.interior p).getLast hPne, List.getLast?_eq_some_getLast hPne⟩
  have hPfrom : IsPathFrom G (SPGT.interior p) p1 pn := ⟨hPlist, hp1, hpn⟩
  have hlastEq : (SPGT.interior p).getLast hPne = pn := by
    have := (List.getLast?_eq_some_getLast hPne).symm.trans hpn
    exact Option.some_injective _ this
  have hdecomp : p = u :: (SPGT.interior p ++ [v]) := by
    have hpne : p ≠ [] := hp.1.1
    obtain ⟨a0, t0, rfl⟩ : ∃ a0 t0, p = a0 :: t0 := by
      cases p with
      | nil => exact absurd rfl hpne
      | cons a t => exact ⟨a, t, rfl⟩
    have ha0 : a0 = u := by
      have hh := hp.2.1
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact hh
    have ht0ne : t0 ≠ [] := by
      intro hc
      rw [hc] at h3
      simp at h3
    have hsplit : t0 = t0.dropLast ++ [t0.getLast ht0ne] :=
      (List.dropLast_append_getLast ht0ne).symm
    have hlastv : t0.getLast ht0ne = v := by
      have hg : (a0 :: t0).getLast (List.cons_ne_nil a0 t0) = v := by
        have hh := hp.2.2
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a0 t0)] at hh
        exact Option.some_injective _ hh
      rw [← hg]
      exact (List.getLast_cons ht0ne).symm
    show a0 :: t0 = u :: (t0.dropLast ++ [v])
    rw [ha0, ← hlastv, ← hsplit]
  have hthird : IsPathFrom G (u :: (SPGT.interior p ++ [v])) u v := by
    rw [← hdecomp]; exact hp
  ------------------------------------------------------------------
  -- 5.  `X₁` and `X₂` are local
  ------------------------------------------------------------------
  have hdropPath : ∀ l : List V, IsPathList G l → 2 ≤ l.length → IsPathList G l.dropLast := by
    intro l h h2
    rw [List.dropLast_eq_take]
    exact PathBasics.isPathList_take h (by omega)
  have hconnNil : ConnectedSet G {z : V | z ∈ ([] : List V)} := by
    intro a b
    exact absurd a.2 (by simp)
  have hconnDrop : ∀ l : List V, IsPathList G l → ConnectedSet G {z : V | z ∈ l.dropLast} := by
    intro l h
    by_cases hd : l.dropLast = []
    · rw [hd]; exact hconnNil
    · have h1 : 0 < l.dropLast.length := List.length_pos_of_ne_nil hd
      rw [List.length_dropLast] at h1
      exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (hdropPath l h (by omega))
  have hpnF : pn ∈ F := by
    rw [← hPF]; exact PathBasics.getLast_mem hpn
  have hp1F : p1 ∈ F := by
    rw [← hPF]; exact PathBasics.head_mem hp1
  -- `F \ {pₙ}`
  have hFdiff1 : F \ {pn} = {z : V | z ∈ (SPGT.interior p).dropLast} := by
    rw [← hPF]
    ext z
    simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [PathBasics.mem_dropLast_iff hPnd hPne, hlastEq]
  -- `F \ {p₁}`, via the reversed path
  have hQlist : IsPathList G (SPGT.interior p).reverse := PathBasics.isPathList_reverse hPlist
  have hQne : (SPGT.interior p).reverse ≠ [] := by
    simpa using hPne
  have hQlastEq : (SPGT.interior p).reverse.getLast hQne = p1 := by
    have h1 : (SPGT.interior p).reverse.getLast? = some p1 := by
      rw [List.getLast?_reverse]; exact hp1
    have := (List.getLast?_eq_some_getLast hQne).symm.trans h1
    exact Option.some_injective _ this
  have hFdiff2 : F \ {p1} = {z : V | z ∈ (SPGT.interior p).reverse.dropLast} := by
    rw [← hPF]
    ext z
    simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [PathBasics.mem_dropLast_iff hQlist.2.1 hQne, hQlastEq, List.mem_reverse]
  have hlocal1 : LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {pn}) K} := by
    by_contra hc
    have hconn1 : ConnectedSet G (F \ {pn}) := by
      rw [hFdiff1]; exact hconnDrop _ hPlist
    have heq := hFmin (F \ {pn}) Set.diff_subset hconn1 hc
    have hmem : pn ∈ F \ {pn} := by rw [heq]; exact hpnF
    exact hmem.2 rfl
  have hlocal2 : LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p1}) K} := by
    by_contra hc
    have hconn2 : ConnectedSet G (F \ {p1}) := by
      rw [hFdiff2]; exact hconnDrop _ hQlist
    have heq := hFmin (F \ {p1}) Set.diff_subset hconn2 hc
    have hmem : p1 ∈ F \ {p1} := by rw [heq]; exact hp1F
    exact hmem.2 rfl
  exact ⟨SPGT.interior p, p1, pn, hPfrom, hPF, hthird, hlocal1, hlocal2⟩

end Workspace.ProofLemmas.Thm58MinimalFIsPath
