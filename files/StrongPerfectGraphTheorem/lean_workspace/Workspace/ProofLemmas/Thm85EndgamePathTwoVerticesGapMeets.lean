import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameK4Shape
import Workspace.ProofLemmas.Thm85EndgameOptimalChoice

/-!
# 8.5, the closing paragraph for `n = 1`: the `K₄` structure

`Thm85EndgameOptimalChoice.attachment_edges_meet_traversal` and
`Thm85EndgameClosing.k4_neighbourhoods` are the two steps of the closing paragraph of 8.5 that
produce the `K₄`.  Both are stated with claim (4) in its *ordered* form
`HasUniqueTraversal`, and `k4_neighbourhoods` additionally asks the two choices of rungs to be
optimal.  Neither restriction is needed:

* `attachment_edges_meet_traversal` uses claim (4) only through
  `obtain ⟨i, j, htrav, -⟩`, that is, only the existence of a traversal;
* `k4_neighbourhoods` uses optimality only through `optimal_traversal_meets`, whose conclusion
  is exactly the conclusion of `attachment_edges_meet_traversal`.

The `n = 1` case of the closing paragraph
(`Thm85EndgamePathTwoVerticesGap.n1_different_traversals_absurd`) has `f₁ = f_n`, and then the
ordered uniqueness of a traversal is false, so this file repeats the two steps with claim (4)
in the existence form and with plain choices of rungs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapMeets

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-- **"`K` consists precisely of the edges of `J` with exactly one end in common with `hi`,
together possibly with `hi` itself"** (printed p. 44), the containment `⊇`: the first bullet of
claim (4) puts the `N_h`-end of the selected `hw`-rung next to `f₁`. -/
theorem attachment_at_traversal_end {G : SimpleGraph V} {J : SimpleGraph U}
    {S : U → U → Set V} {N : U → Set V}
    {R : U → U → List V} (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {F : Set V} {f₁ fn : V} (hf₁ : f₁ ∈ F) {h i : U}
    (htrav : IsTraversal G J N F f₁ fn R h i)
    {w : U} (hw : w ≠ i) (hhw : J.Adj h w) :
    (attachments G F (stripSystemVertices J S) ∩ S h w).Nonempty := by
  obtain ⟨r, hrR, hrN, -, -, hadj, -⟩ := htrav.2.1 w hw hhw
  have hrS : r ∈ S h w := StripSystemBasics.rung_subset_strip (hR h w hhw) r hrR
  exact ⟨r, ⟨StripSystemBasics.strip_subset_vertices hhw hrS, f₁, hf₁, hadj⟩, hrS⟩

/-- `Thm85EndgameOptimalChoice.attachment_edges_meet_traversal` with claim (4) supplied only as
the existence of a traversal.  The proof is the printed one, unchanged. -/
theorem meets_traversal [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rc a b} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (hclaim4 : ∀ Rc : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc →
      ∃ p q : U, IsTraversal G J N F f₁ fn Rc p q)
    (hclaim5 : ∀ Rc : U → U → List V, RungChoice G J S N Rc →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc)
    (R : U → U → List V) (hR : RungChoice G J S N R) (i j : U)
    (htrav : IsTraversal G J N F f₁ fn R i j)
    {u v : U} (huv : J.Adj u v)
    (hK : (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty) :
    u = i ∨ u = j ∨ v = i ∨ v = j := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hui, huj, hvi, hvj⟩ := hcon
  have hij : J.Adj i j := htrav.1
  have hijne : i ≠ j := hij.ne
  have huvne : u ≠ v := huv.ne
  have hnd : [u, v, i, j].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or]
    tauto
  obtain ⟨x, hxX, hxS⟩ := hK
  obtain ⟨L, hL, hxL⟩ := StripSystemBasics.exists_rung hSN huv hxS
  obtain ⟨R₂, hR₂, hR₂uv, hR₂eq⟩ :=
    Thm85EndgameOptimalChoice.exists_rung_choice_replacing hSN R hR huv hL
  obtain ⟨i₂, j₂, htrav₂⟩ := hclaim4 R₂ (hclaim5 R₂ hR₂)
  have hi₂j₂ : J.Adj i₂ j₂ := htrav₂.1
  have hedgeI : ∀ w : U, J.Adj i w → s(i, w) ≠ s(u, v) := by
    intro w hiw h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hui h1.symm
    · exact hvi h1.symm
  have hedgeJ : ∀ w : U, J.Adj j w → s(j, w) ≠ s(u, v) := by
    intro w hjw h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact huj h1.symm
    · exact hvj h1.symm
  have hb1 : ∀ w : U, w ≠ j → J.Adj i w →
      ∃ r : V, r ∈ R₂ i w ∧ r ∈ N i ∧ UniqueEdgeBetween G {z : V | z ∈ R₂ i w} F r f₁ := by
    intro w hw hiw
    rw [hR₂eq i w hiw (hedgeI w hiw)]
    exact htrav.2.1 w hw hiw
  have hb2 : ∀ w : U, w ≠ i → J.Adj j w →
      ∃ r : V, r ∈ R₂ j w ∧ r ∈ N j ∧ UniqueEdgeBetween G {z : V | z ∈ R₂ j w} F r fn := by
    intro w hw hjw
    rw [hR₂eq j w hjw (hedgeJ w hjw)]
    exact htrav.2.2.1 w hw hjw
  obtain ⟨-, f, hfF, hxf⟩ := hxX
  have hmemx : x ∈ {z : V | z ∈ R₂ u v} := by
    show x ∈ R₂ u v
    rw [hR₂uv]
    exact hxL
  by_cases hiT : i = i₂ ∨ i = j₂
  · by_cases hjT : j = i₂ ∨ j = j₂
    · have hcases : (i₂ = i ∧ j₂ = j) ∨ (i₂ = j ∧ j₂ = i) := by
        rcases hiT with h | h
        · rcases hjT with h' | h'
          · exact absurd (h.trans h'.symm) hijne
          · exact Or.inl ⟨h.symm, h'.symm⟩
        · rcases hjT with h' | h'
          · exact Or.inr ⟨h'.symm, h.symm⟩
          · exact absurd (h.trans h'.symm) hijne
      have hnd2 : [u, v, i₂, j₂].Nodup := by
        rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or] <;> tauto
      exact htrav₂.2.2.2 u v huv hnd2 x hmemx f hfF hxf
    · push_neg at hjT
      refine Thm85EndgameK4Shape.not_two_neighbours hJ j i₂ j₂ ?_
      intro w hjw
      by_cases hwi : w = i
      · rcases hiT with h | h
        · exact Or.inl (hwi.trans h)
        · exact Or.inr (hwi.trans h)
      · obtain ⟨r, -, -, hu⟩ := hb2 w hwi hjw
        by_contra hw2
        push_neg at hw2
        have hjwne : j ≠ w := hjw.ne
        have hi₂j₂ne : i₂ ≠ j₂ := hi₂j₂.ne
        have hnd3 : [j, w, i₂, j₂].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or]
          have ha := hjT.1
          have hb := hjT.2
          have hc := hw2.1
          have hd := hw2.2
          tauto
        exact htrav₂.2.2.2 j w hjw hnd3 r hu.1 fn hu.2.1 hu.2.2.1
  · by_cases hjT : j = i₂ ∨ j = j₂
    · push_neg at hiT
      refine Thm85EndgameK4Shape.not_two_neighbours hJ i i₂ j₂ ?_
      intro w hiw
      by_cases hwj : w = j
      · rcases hjT with h | h
        · exact Or.inl (hwj.trans h)
        · exact Or.inr (hwj.trans h)
      · obtain ⟨r, -, -, hu⟩ := hb1 w hwj hiw
        by_contra hw2
        push_neg at hw2
        have hiwne : i ≠ w := hiw.ne
        have hi₂j₂ne : i₂ ≠ j₂ := hi₂j₂.ne
        have hnd3 : [i, w, i₂, j₂].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or]
          have ha := hiT.1
          have hb := hiT.2
          have hc := hw2.1
          have hd := hw2.2
          tauto
        exact htrav₂.2.2.2 i w hiw hnd3 r hu.1 f₁ hu.2.1 hu.2.2.1
    · push_neg at hiT hjT
      have hi₂j₂ne : i₂ ≠ j₂ := hi₂j₂.ne
      have hnd3 : [i, j, i₂, j₂].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          and_true, not_or]
        have ha := hiT.1
        have hb := hiT.2
        have hc := hjT.1
        have hd := hjT.2
        tauto
      exact Thm85EndgameK4Shape.disjoint_traversals_absurd G hG J hJ S N hSN F f₁ fn
        hclaim1 R₂ hR₂ i j i₂ j₂ hnd3 hij hb1 hb2 htrav₂

/-- **"Hence `J = K₄` and `jk` is disjoint from `hi`"** (printed p. 44), with claim (4) in the
existence form and with plain choices of rungs.  This is
`Thm85EndgameClosing.k4_neighbourhoods` with `optimal_traversal_meets` replaced by
`meets_traversal`, which has the same conclusion but does not need optimality. -/
theorem k4_neighbourhoods [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V) (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rc a b} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (hclaim4 : ∀ Rc : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc →
      ∃ p q : U, IsTraversal G J N F f₁ fn Rc p q)
    (hclaim5 : ∀ Rc : U → U → List V, RungChoice G J S N Rc →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc)
    {R R' : U → U → List V} {h i j k : U}
    (hR : RungChoice G J S N R) (hR' : RungChoice G J S N R')
    (htrav : IsTraversal G J N F f₁ fn R h i)
    (htrav' : IsTraversal G J N F f₁ fn R' j k)
    (hne : s(h, i) ≠ s(j, k)) :
    [h, i, j, k].Nodup ∧
      (∀ w : U, J.Adj h w ↔ (w = i ∨ w = j ∨ w = k)) ∧
      (∀ w : U, J.Adj i w ↔ (w = h ∨ w = j ∨ w = k)) ∧
      (∀ w : U, J.Adj j w ↔ (w = h ∨ w = i ∨ w = k)) ∧
      (∀ w : U, J.Adj k w ↔ (w = h ∨ w = i ∨ w = j)) := by
  classical
  have hhi : J.Adj h i := htrav.1
  have hjk : J.Adj j k := htrav'.1
  have hmeet : ∀ w : U, w ≠ i → J.Adj h w → (w = j ∨ w = k ∨ h = j ∨ h = k) := by
    intro w hw hhw
    rcases meets_traversal G hG J hJ S N hSN F f₁ fn hclaim1 hclaim4 hclaim5 R' hR' j k htrav'
      hhw (attachment_at_traversal_end hR.1 hf₁ htrav hw hhw) with hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  have hmeet' : ∀ w : U, w ≠ h → J.Adj i w → (w = j ∨ w = k ∨ i = j ∨ i = k) := by
    intro w hw hiw
    obtain ⟨r, hrR, hrN, -, -, hadj, -⟩ := htrav.2.2.1 w hw hiw
    have hrS : r ∈ S i w := StripSystemBasics.rung_subset_strip (hR.1 i w hiw) r hrR
    have hKne : (attachments G F (stripSystemVertices J S) ∩ S i w).Nonempty :=
      ⟨r, ⟨StripSystemBasics.strip_subset_vertices hiw hrS, fn, hfn, hadj⟩, hrS⟩
    rcases meets_traversal G hG J hJ S N hSN F f₁ fn hclaim1 hclaim4 hclaim5 R' hR' j k htrav'
      hiw hKne with hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  have hmeetj : ∀ w : U, w ≠ k → J.Adj j w → (w = h ∨ w = i ∨ j = h ∨ j = i) := by
    intro w hw hjw
    rcases meets_traversal G hG J hJ S N hSN F f₁ fn hclaim1 hclaim4 hclaim5 R hR h i htrav
      hjw (attachment_at_traversal_end hR'.1 hf₁ htrav' hw hjw) with hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  have hmeetk : ∀ w : U, w ≠ j → J.Adj k w → (w = h ∨ w = i ∨ k = h ∨ k = i) := by
    intro w hw hkw
    obtain ⟨r, hrR, hrN, -, -, hadj, -⟩ := htrav'.2.2.1 w hw hkw
    have hrS : r ∈ S k w := StripSystemBasics.rung_subset_strip (hR'.1 k w hkw) r hrR
    have hKne : (attachments G F (stripSystemVertices J S) ∩ S k w).Nonempty :=
      ⟨r, ⟨StripSystemBasics.strip_subset_vertices hkw hrS, fn, hfn, hadj⟩, hrS⟩
    rcases meets_traversal G hG J hJ S N hSN F f₁ fn hclaim1 hclaim4 hclaim5 R hR h i htrav
      hkw hKne with hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  have hdeg : ∀ a : U, 3 ≤ (J.neighborSet a).ncard :=
    fun a => SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  have hthree : ∀ (a b c : U), (∀ w : U, J.Adj a w → (w = b ∨ w = c)) → False := by
    intro a b c hsub
    have hle : (J.neighborSet a).ncard ≤ ({b, c} : Set U).ncard :=
      Set.ncard_le_ncard (fun w hw => by
        rcases hsub w hw with h | h
        · exact Or.inl h
        · exact Or.inr h) (Set.toFinite _)
    have : ({b, c} : Set U).ncard ≤ 2 := by
      refine le_trans (Set.ncard_insert_le _ _) ?_
      simp [Set.ncard_singleton]
    have := hdeg a
    omega
  have hhj : h ≠ j := by
    intro heq
    have hik : i ≠ k := by
      intro heq2
      exact hne (by rw [heq, heq2])
    refine hthree i h k ?_
    intro w hw
    by_cases hwh : w = h
    · exact Or.inl hwh
    · rcases hmeet' w hwh hw with hc | hc | hc | hc
      · exact Or.inl (hc.trans heq.symm)
      · exact Or.inr hc
      · exact absurd (hc.trans heq.symm) hhi.ne'
      · exact absurd hc hik
  have hhk : h ≠ k := by
    intro heq
    have hij2 : i ≠ j := by
      intro heq2
      exact hne (by rw [heq, heq2, Sym2.eq_swap])
    refine hthree i h j ?_
    intro w hw
    by_cases hwh : w = h
    · exact Or.inl hwh
    · rcases hmeet' w hwh hw with hc | hc | hc | hc
      · exact Or.inr hc
      · exact Or.inl (hc.trans heq.symm)
      · exact absurd hc hij2
      · exact absurd (hc.trans heq.symm) hhi.ne'
  have hij' : i ≠ j := by
    intro heq
    refine hthree h i k ?_
    intro w hw
    by_cases hwi : w = i
    · exact Or.inl hwi
    · rcases hmeet w hwi hw with hc | hc | hc | hc
      · exact Or.inl (hc.trans heq.symm)
      · exact Or.inr hc
      · exact absurd hc hhj
      · exact absurd hc hhk
  have hik' : i ≠ k := by
    intro heq
    refine hthree h i j ?_
    intro w hw
    by_cases hwi : w = i
    · exact Or.inl hwi
    · rcases hmeet w hwi hw with hc | hc | hc | hc
      · exact Or.inr hc
      · exact Or.inl (hc.trans heq.symm)
      · exact absurd hc hhj
      · exact absurd hc hhk
  have hnd : [h, i, j, k].Nodup := by
    have h1 : h ≠ i := hhi.ne
    have h2 : j ≠ k := hjk.ne
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or]
    tauto
  have hsubh : ∀ w : U, J.Adj h w → (w = i ∨ w = j ∨ w = k) := by
    intro w hw
    by_cases hwi : w = i
    · exact Or.inl hwi
    · rcases hmeet w hwi hw with hc | hc | hc | hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
      · exact absurd hc hhj
      · exact absurd hc hhk
  have hsubi : ∀ w : U, J.Adj i w → (w = h ∨ w = j ∨ w = k) := by
    intro w hw
    by_cases hwh : w = h
    · exact Or.inl hwh
    · rcases hmeet' w hwh hw with hc | hc | hc | hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
      · exact absurd hc hij'
      · exact absurd hc hik'
  have hsubj : ∀ w : U, J.Adj j w → (w = h ∨ w = i ∨ w = k) := by
    intro w hw
    by_cases hwk : w = k
    · exact Or.inr (Or.inr hwk)
    · rcases hmeetj w hwk hw with hc | hc | hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
      · exact absurd hc.symm hhj
      · exact absurd hc.symm hij'
  have hsubk : ∀ w : U, J.Adj k w → (w = h ∨ w = i ∨ w = j) := by
    intro w hw
    by_cases hwj : w = j
    · exact Or.inr (Or.inr hwj)
    · rcases hmeetk w hwj hw with hc | hc | hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
      · exact absurd hc.symm hhk
      · exact absurd hc.symm hik'
  have hfill : ∀ (a b c d : U), b ≠ c → b ≠ d → c ≠ d →
      (∀ w : U, J.Adj a w → (w = b ∨ w = c ∨ w = d)) →
      (∀ w : U, J.Adj a w ↔ (w = b ∨ w = c ∨ w = d)) := by
    intro a b c d hbc hbd hcd hsub
    have hsub' : J.neighborSet a ⊆ ({b, c, d} : Set U) := by
      intro w hw
      rcases hsub w hw with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr hh)
    have hcard : ({b, c, d} : Set U).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨b, c, d, hbc, hbd, hcd, rfl⟩
    have heq : J.neighborSet a = ({b, c, d} : Set U) :=
      Set.eq_of_subset_of_ncard_le hsub' (by rw [hcard]; exact hdeg a) (Set.toFinite _)
    intro w
    constructor
    · intro hw; exact hsub w hw
    · intro hw
      have : w ∈ J.neighborSet a := by
        rw [heq]
        rcases hw with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr hh)
      exact this
  exact ⟨hnd, hfill h i j k hij' hik' hjk.ne hsubh, hfill i h j k hhj hhk hjk.ne hsubi,
    hfill j h i k hhi.ne hhk hik' hsubj, hfill k h i j hhi.ne hhj hij' hsubk⟩

end Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapMeets
