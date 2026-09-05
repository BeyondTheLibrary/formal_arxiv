import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameK4Shape
import Workspace.ProofLemmas.Thm85EndgameOptimalChoice

/-!
# 8.5, the closing paragraph

PAPER (printed p. 44):

*"Let us say a choice `R_uv` (`uv ∈ E(J)`) is **optimal** if `R_uv` has a vertex in `X` for all
edges `uv` in `K`.  For any choice of rungs, there is an optimal choice with the same traversal
(just replace rungs that miss `X` by rungs that meet `X` wherever possible); so (6) implies that
there are two optimal choices of rungs with different traversals.  Now for any optimal choice of
rungs, if `hi` is its traversal, then by (4) and the optimality of the choice, it follows that
`K` consists precisely of the edges of `J` with exactly one end in common with `hi`, together
possibly with `hi` itself.  In particular `hi` meets all edges in `K`.  We may assume that some
other edge `jk` is the traversal for some other optimal choice; and hence (since `J` is
3-connected) it follows that `J = K₄` and `jk` is disjoint from `hi`, and neither edge is in
`K`.  Hence `V(J) = {h,i,j,k}`. …"*

This module proves the printed sentences down to *"Hence `V(J) = {h,i,j,k}`"*, in the following
pieces.

* `attachment_at_traversal_end` is *"`K` contains every edge of `J` with exactly one end in
  common with `hi`"*: the first two bullets of (4) put the end of every rung at `h` other than
  `R_hi` into `X`.
* `optimal_traversal_meets` is *"`hi` meets all edges in `K`"*: the third bullet of (4) makes the
  selected rung of an edge disjoint from `hi` anticomplete to `F`, and optimality says that this
  rung meets `X` whenever the strip does.
* `k4_neighbourhoods` combines the two for two optimal choices with different traversals: the
  two traversal edges are disjoint and each of `h,i,j,k` is adjacent exactly to the other three.

Two steps remain open and are isolated below with the printed sentence each encodes:
`optimal_with_same_traversal` and `k4_endgame`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgameClosing

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-! ## `K` contains every edge with exactly one end on the traversal -/

/-- **"`K` consists precisely of the edges of `J` with exactly one end in common with `hi`,
together possibly with `hi` itself"**, the containment `⊇` (printed p. 44).

The first bullet of (4) says that the `N_h`-end of the selected `hw`-rung is adjacent to `f₁`,
so it is an attachment of `F` lying in the strip `S_hw`. -/
theorem attachment_at_traversal_end {G : SimpleGraph V} {J : SimpleGraph U}
    {S : U → U → Set V} {N : U → Set V} (hSN : IsJStripSystem G J S N)
    {R : U → U → List V} (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {F : Set V} {f₁ fn : V} (hf₁ : f₁ ∈ F) {h i : U}
    (htrav : IsTraversal G J N F f₁ fn R h i)
    {w : U} (hw : w ≠ i) (hhw : J.Adj h w) :
    (attachments G F (stripSystemVertices J S) ∩ S h w).Nonempty := by
  obtain ⟨r, hrR, hrN, -, -, hadj, -⟩ := htrav.2.1 w hw hhw
  have hrS : r ∈ S h w := StripSystemBasics.rung_subset_strip (hR h w hhw) r hrR
  exact ⟨r, ⟨StripSystemBasics.strip_subset_vertices hhw hrS, f₁, hf₁, hadj⟩, hrS⟩

/-- **"In particular `hi` meets all edges in `K`"** (printed p. 44).

The third bullet of (4) makes the selected rung of an edge disjoint from `hi` anticomplete to
`F`; optimality says that this rung meets `X` as soon as the strip does. -/
theorem optimal_traversal_meets {G : SimpleGraph V} {J : SimpleGraph U}
    {S : U → U → Set V} {N : U → Set V}
    {R : U → U → List V} {F : Set V} {f₁ fn : V} {h i : U}
    (hopt : OptimalChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    (htrav : IsTraversal G J N F f₁ fn R h i)
    {u v : U} (huv : J.Adj u v)
    (hK : (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty) :
    u = h ∨ u = i ∨ v = h ∨ v = i := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxX, hxR⟩ := hopt.2 u v huv hK
  obtain ⟨-, f, hfF, hadj⟩ := hxX
  have hnd : [u, v, h, i].Nodup := by
    have h1 : u ≠ v := huv.ne
    have h2 : h ≠ i := htrav.1.ne
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or]
    tauto
  exact htrav.2.2.2 u v huv hnd x hxR f hfF hadj

/-! ## The `K₄` structure -/

/-- **"Hence `J = K₄` and `jk` is disjoint from `hi`"** (printed p. 44), in the form of the
adjacencies: the two traversal edges are disjoint, and each of the four vertices is adjacent to
the other three and to nothing else. -/
theorem k4_neighbourhoods [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
    (hJ : IsKConnected J 3) {S : U → U → Set V} {N : U → Set V}
    (hSN : IsJStripSystem G J S N) {F : Set V} {f₁ fn : V} (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    {R R' : U → U → List V} {h i j k : U}
    (hopt : OptimalChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    (hopt' : OptimalChoice G J S N (attachments G F (stripSystemVertices J S)) R')
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
  -- every edge at an end of one traversal, other than that traversal, meets the other
  have hmeet : ∀ w : U, w ≠ i → J.Adj h w → (w = j ∨ w = k ∨ h = j ∨ h = k) := by
    intro w hw hhw
    rcases optimal_traversal_meets hopt' htrav' hhw
      (attachment_at_traversal_end hSN hopt.1.1 hf₁ htrav hw hhw) with
      hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  have hmeet' : ∀ w : U, w ≠ h → J.Adj i w → (w = j ∨ w = k ∨ i = j ∨ i = k) := by
    intro w hw hiw
    have hiw' : J.Adj i w := hiw
    obtain ⟨r, hrR, hrN, -, -, hadj, -⟩ := htrav.2.2.1 w hw hiw'
    have hrS : r ∈ S i w := StripSystemBasics.rung_subset_strip (hopt.1.1 i w hiw') r hrR
    have hKne : (attachments G F (stripSystemVertices J S) ∩ S i w).Nonempty :=
      ⟨r, ⟨StripSystemBasics.strip_subset_vertices hiw' hrS, fn, hfn, hadj⟩, hrS⟩
    rcases optimal_traversal_meets hopt' htrav' hiw' hKne with hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  have hmeetj : ∀ w : U, w ≠ k → J.Adj j w → (w = h ∨ w = i ∨ j = h ∨ j = i) := by
    intro w hw hjw
    rcases optimal_traversal_meets hopt htrav hjw
      (attachment_at_traversal_end hSN hopt'.1.1 hf₁ htrav' hw hjw) with
      hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  have hmeetk : ∀ w : U, w ≠ j → J.Adj k w → (w = h ∨ w = i ∨ k = h ∨ k = i) := by
    intro w hw hkw
    have hkw' : J.Adj k w := hkw
    obtain ⟨r, hrR, hrN, -, -, hadj, -⟩ := htrav'.2.2.1 w hw hkw'
    have hrS : r ∈ S k w := StripSystemBasics.rung_subset_strip (hopt'.1.1 k w hkw') r hrR
    have hKne : (attachments G F (stripSystemVertices J S) ∩ S k w).Nonempty :=
      ⟨r, ⟨StripSystemBasics.strip_subset_vertices hkw' hrS, fn, hfn, hadj⟩, hrS⟩
    rcases optimal_traversal_meets hopt htrav hkw' hKne with hc | hc | hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
  -- degrees are at least three
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
  -- the two traversal edges are disjoint
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
  -- each neighbourhood is contained in the other three vertices, hence equal to them
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
  -- three distinct vertices in a neighbourhood of size at least three fill it
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


/-! ## The two steps that remain open -/

/-- **Gap: "For any choice of rungs, there is an optimal choice with the same traversal"**
(printed p. 44).

PAPER: *"Let us say a choice `R_uv` (`uv ∈ E(J)`) is optimal if `R_uv` has a vertex in `X` for
all edges `uv` in `K`.  For any choice of rungs, there is an optimal choice with the same
traversal (just replace rungs that miss `X` by rungs that meet `X` wherever possible)."* -/
theorem optimal_with_same_traversal [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rc a b} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P})
    (hclaim4 : ∀ Rc : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc →
      HasUniqueTraversal G J N F f₁ fn Rc)
    (hclaim5 : ∀ Rc : U → U → List V, RungChoice G J S N Rc →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc)
    (R : U → U → List V) (hR : RungChoice G J S N R)
    (i j : U) (htrav : IsTraversal G J N F f₁ fn R i j) :
    ∃ R' : U → U → List V,
      OptimalChoice G J S N (attachments G F (stripSystemVertices J S)) R' ∧
      IsTraversal G J N F f₁ fn R' i j := by
  classical
  have hij : J.Adj i j := htrav.1
  have hijne : i ≠ j := hij.ne
  -- no strip of an edge disjoint from `ij` meets `X`, so only the rung on `ij` needs changing
  have hA : ∀ {u v : U}, J.Adj u v →
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty →
      u = i ∨ u = j ∨ v = i ∨ v = j := fun {u v} huv hK =>
    Thm85EndgameOptimalChoice.attachment_edges_meet_traversal G hG J hJ S N hSN F f₁ fn
      hclaim1 hclaim4 hclaim5 R hR i j htrav huv hK
  -- choose a rung on `ij` through `X` if there is one
  obtain ⟨L, hL, hLX⟩ : ∃ L : List V, IsUVRung G J S N i j L ∧
      ((attachments G F (stripSystemVertices J S) ∩ S i j).Nonempty →
        ∃ z ∈ attachments G F (stripSystemVertices J S), z ∈ L) := by
    by_cases hne : (attachments G F (stripSystemVertices J S) ∩ S i j).Nonempty
    · obtain ⟨z, hzX, hzS⟩ := hne
      obtain ⟨L, hL, hzL⟩ := StripSystemBasics.exists_rung hSN hij hzS
      exact ⟨L, hL, fun _ => ⟨z, hzX, hzL⟩⟩
    · exact ⟨R i j, hR.1 i j hij, fun hc => absurd hc hne⟩
  obtain ⟨R', hR', hR'ij, hR'eq⟩ :=
    Thm85EndgameOptimalChoice.exists_rung_choice_replacing hSN R hR hij hL
  -- the rungs of the edges at `i` and at `j` already meet `X`
  have hmeetI : ∀ w : U, w ≠ j → J.Adj i w →
      ∃ z ∈ attachments G F (stripSystemVertices J S), z ∈ R i w := by
    intro w hw hiw
    obtain ⟨r, hrR, -, hu⟩ := htrav.2.1 w hw hiw
    exact ⟨r, ⟨StripSystemBasics.strip_subset_vertices hiw
      (StripSystemBasics.rung_subset_strip (hR.1 i w hiw) r hrR), f₁, hu.2.1, hu.2.2.1⟩, hrR⟩
  have hmeetJ : ∀ w : U, w ≠ i → J.Adj j w →
      ∃ z ∈ attachments G F (stripSystemVertices J S), z ∈ R j w := by
    intro w hw hjw
    obtain ⟨r, hrR, -, hu⟩ := htrav.2.2.1 w hw hjw
    exact ⟨r, ⟨StripSystemBasics.strip_subset_vertices hjw
      (StripSystemBasics.rung_subset_strip (hR.1 j w hjw) r hrR), fn, hu.2.1, hu.2.2.1⟩, hrR⟩
  refine ⟨R', ⟨hR', ?_⟩, hij, ?_, ?_, ?_⟩
  · -- optimality
    intro u v huv hXuv
    by_cases hs : s(u, v) = s(i, j)
    · have hXij : (attachments G F (stripSystemVertices J S) ∩ S i j).Nonempty := by
        rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hXuv
        · rwa [StripSystemBasics.strip_symm hSN huv] at hXuv
      obtain ⟨z, hzX, hzL⟩ := hLX hXij
      rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨z, hzX, by rw [hR'ij]; exact hzL⟩
      · refine ⟨z, hzX, ?_⟩
        rw [hR'.2 v u huv.symm, hR'ij, List.mem_reverse]
        exact hzL
    · rw [hR'eq u v huv hs]
      have hvj : u = i → v ≠ j := by rintro rfl rfl; exact hs rfl
      have hvi : u = j → v ≠ i := by rintro rfl rfl; exact hs Sym2.eq_swap
      have huj : v = i → u ≠ j := by rintro rfl rfl; exact hs Sym2.eq_swap
      have hui : v = j → u ≠ i := by rintro rfl rfl; exact hs rfl
      rcases hA huv hXuv with h | h | h | h
      · subst h
        exact hmeetI v (hvj rfl) huv
      · subst h
        exact hmeetJ v (hvi rfl) huv
      · subst h
        obtain ⟨z, hzX, hzR⟩ := hmeetI u (huj rfl) huv.symm
        exact ⟨z, hzX, by rw [hR.2 v u huv.symm, List.mem_reverse]; exact hzR⟩
      · subst h
        obtain ⟨z, hzX, hzR⟩ := hmeetJ u (hui rfl) huv.symm
        exact ⟨z, hzX, by rw [hR.2 v u huv.symm, List.mem_reverse]; exact hzR⟩
  · intro w hw hiw
    rw [hR'eq i w hiw (by
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hw h2
      · exact hijne h1)]
    exact htrav.2.1 w hw hiw
  · intro w hw hjw
    rw [hR'eq j w hjw (by
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hijne h1.symm
      · exact hw h2)]
    exact htrav.2.2.1 w hw hjw
  · intro u v huv hnd
    have hd : u ≠ i ∧ u ≠ j ∧ v ≠ i ∧ v ≠ j := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or] at hnd
      tauto
    rw [hR'eq u v huv (by
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hd.1 h1
      · exact hd.2.1 h1)]
    exact htrav.2.2.2 u v huv hnd

/-- **Gap: the last two paragraphs of the proof of 8.5** (printed pp. 44–45).

PAPER: *"Hence `V(J) = {h,i,j,k}`.  Now since the strip system is not degenerate, there is one
of the four edges `hj, hk, ij, ik` whose strip contains a rung of nonzero length; some `hj`-rung
`R` has length `> 0` say.  From (4) it follows that exactly one vertex of `R` is in `X`, one of
its ends; say the end in `N_h`.  Let `R_uv` (`uv ∈ E(J)`) be any choice of rungs such that
`R_hj = R`.  Since the end of `R` in `N_j` does not belong to `X`, it follows from (4) that for
each of `R_hk, R_ij, R_ik`, its unique vertex in `X` is its end in `N_h ∪ N_i`.  Since the choice
of these rungs was arbitrary, it follows that `X ∩ S_hk = N_hk`, `X ∩ S_ij = N_ij`, and
`X ∩ S_ik = N_ik`.  If also `X ∩ S_hj = N_hj` then `hi` is the traversal for every choice of
rungs, contrary to (6), so `X ∩ S_hj ≠ N_hj`.  It follows that every `ij`-rung has length 0; for
if one, `R'` say, has length `> 0`, then its unique vertex in `X` is its end in `N_i`, and by
exchanging `h` and `i` it follows that `X ∩ S_hj = N_hj`, a contradiction.  Similarly all `hk`-
and `ik`-rungs have length 0, and therefore all `hj`-rungs have even length, since `G` is Berge.
From (1), we may assume that `f₁` is adjacent to `r_hj` and complete to `S_hk`, and `f_n` is
complete to `S_ij ∪ S_ik`, and there are no other edges between `F` and
`S_hk ∪ S_ij ∪ S_ik ∪ {r_hj}`.  Let `R'` be an `hj`-rung such that its vertex in `N_h`
(`r'_hj`, say) is not its unique vertex in `X`.  Consequently, its other end (`r'_jh`) is its
unique vertex in `X`.  By the same argument with `hi` and `jk` exchanged, it follows that one of
`f₁, f_n` is complete to `S_ij ∪ {r'_jh}` and the other to `S_hk ∪ S_ik`; and hence `n = 1`.
But then the path `f₁-r_hj-R_hj-r_jh-r_ji-f₁` is an odd hole, a contradiction.  This proves
8.5."*

The `K₄` structure reached by `k4_neighbourhoods` is supplied as the four neighbourhood
descriptions; the printed sentence *"Hence `V(J) = {h,i,j,k}`"* follows from them and the
3-connectivity of `J`. -/
theorem k4_endgame [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
          (phi : H.lineGraph ≃g G.induce K'),
        IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' phi)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ Rc u v} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P})
    (hclaim4 : ∀ Rc : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc →
      HasUniqueTraversal G J N F f₁ fn Rc)
    (hclaim5 : ∀ Rc : U → U → List V, RungChoice G J S N Rc →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc)
    (h i j k : U) (hnd : [h, i, j, k].Nodup)
    (hNh : ∀ w : U, J.Adj h w ↔ (w = i ∨ w = j ∨ w = k))
    (hNi : ∀ w : U, J.Adj i w ↔ (w = h ∨ w = j ∨ w = k))
    (hNj : ∀ w : U, J.Adj j w ↔ (w = h ∨ w = i ∨ w = k))
    (hNk : ∀ w : U, J.Adj k w ↔ (w = h ∨ w = i ∨ w = j))
    (R R' : U → U → List V)
    (hopt : OptimalChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    (hopt' : OptimalChoice G J S N (attachments G F (stripSystemVertices J S)) R')
    (htrav : IsTraversal G J N F f₁ fn R h i)
    (htrav' : IsTraversal G J N F f₁ fn R' j k) :
    False := by
  classical
  -- the six edges of `K₄`
  have hhi : J.Adj h i := (hNh i).mpr (Or.inl rfl)
  have hhj : J.Adj h j := (hNh j).mpr (Or.inr (Or.inl rfl))
  have hhk : J.Adj h k := (hNh k).mpr (Or.inr (Or.inr rfl))
  have hijA : J.Adj i j := (hNi j).mpr (Or.inr (Or.inl rfl))
  have hik : J.Adj i k := (hNi k).mpr (Or.inr (Or.inr rfl))
  have hd : h ≠ i ∧ h ≠ j ∧ h ≠ k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd
    tauto
  obtain ⟨ehi, ehj, ehk, eij, eik, ejk⟩ := hd
  have hcover : ∀ c : U, c = h ∨ c = i ∨ c = j ∨ c = k :=
    Thm85EndgameK4Shape.cover_of_hub_neighbourhoods hJ ehj ehk eij eik
      (fun w hw => (hNh w).mp hw) (fun w hw => (hNi w).mp hw)
  have hf₁F : f₁ ∈ F := by
    rw [hPF]
    exact List.mem_of_mem_head? hP.2.1
  have hfnF : fn ∈ F := by
    rw [hPF]
    exact List.mem_of_getLast? hP.2.2
  -- the four strips `S_hj, S_hk, S_ij, S_ik` all meet `X`
  have hXh : ∀ w : U, w ≠ i → J.Adj h w →
      (attachments G F (stripSystemVertices J S) ∩ S h w).Nonempty :=
    fun w hw hhw => attachment_at_traversal_end hSN hopt.1.1 hf₁F htrav hw hhw
  have hXi : ∀ w : U, w ≠ h → J.Adj i w →
      (attachments G F (stripSystemVertices J S) ∩ S i w).Nonempty := by
    intro w hw hiw
    obtain ⟨r, hrR, -, hu⟩ := htrav.2.2.1 w hw hiw
    have hrS := StripSystemBasics.rung_subset_strip (hopt.1.1 i w hiw) r hrR
    exact ⟨r, ⟨StripSystemBasics.strip_subset_vertices hiw hrS, fn, hu.2.1, hu.2.2.1⟩, hrS⟩
  -- change the choice `R` on the edge `ij` to the `ij`-rung of `R'`
  obtain ⟨R₂, hR₂, hR₂ij, hR₂eq⟩ :=
    Thm85EndgameOptimalChoice.exists_rung_choice_replacing hSN R hopt.1 hijA
      (hopt'.1.1 i j hijA)
  obtain ⟨p, q, htrav₂, -⟩ := hclaim4 R₂ (hclaim5 R₂ hR₂)
  have hA2 : ∀ {u v : U}, J.Adj u v →
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty →
      u = p ∨ u = q ∨ v = p ∨ v = q := fun {u v} huv hK =>
    Thm85EndgameOptimalChoice.attachment_edges_meet_traversal G hG J hJ S N hSN F f₁ fn
      hclaim1 hclaim4 hclaim5 R₂ hR₂ p q htrav₂ huv hK
  have hfour := Thm85EndgameK4Shape.edge_meeting_four hnd hcover htrav₂.1.ne
    (hA2 hhj (hXh j eij.symm hhj)) (hA2 hhk (hXh k eik.symm hhk))
    (hA2 hijA (hXi j ehj.symm hijA)) (hA2 hik (hXi k ehk.symm hik))
  -- comparing the traversal of `R₂` with those of `R` and `R'` on a common edge gives `n = 1`
  have hfeq : f₁ = fn := by
    rcases hfour with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq] at htrav₂
    · obtain ⟨r, -, -, hu⟩ := htrav₂.2.2.1 j ehj.symm hijA
      rw [hR₂ij] at hu
      obtain ⟨r', hr'R, -, hu'⟩ := htrav'.2.1 i eik hijA.symm
      have hr'mem : r' ∈ {z : V | z ∈ R' i j} := by
        show r' ∈ R' i j
        rw [hopt'.1.2 i j hijA, List.mem_reverse] at hr'R
        exact hr'R
      exact (hu.2.2.2 r' hr'mem f₁ hu'.2.1 hu'.2.2.1).2
    · obtain ⟨r, -, -, hu⟩ := htrav₂.2.1 k ehk.symm hik
      rw [hR₂eq i k hik (by
        intro hc
        rcases Sym2.eq_iff.mp hc with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact ejk.symm h2
        · exact eij h1)] at hu
      obtain ⟨r', hr'R, -, hu'⟩ := htrav.2.2.1 k ehk.symm hik
      exact ((hu.2.2.2 r' hu'.1 fn hu'.2.1 hu'.2.2.1).2).symm
    · obtain ⟨r, -, -, hu⟩ := htrav₂.2.2.1 h ehj hhk.symm
      rw [hR₂eq k h hhk.symm (by
        intro hc
        rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact eik.symm h1
        · exact ejk.symm h1)] at hu
      obtain ⟨r', hr'R, -, hu'⟩ := htrav.2.1 k eik.symm hhk
      have hr'mem : r' ∈ {z : V | z ∈ R k h} := by
        show r' ∈ R k h
        rw [hopt.1.2 h k hhk, List.mem_reverse]
        exact hr'R
      exact (hu.2.2.2 r' hr'mem f₁ hu'.2.1 hu'.2.2.1).2
    · obtain ⟨r, -, -, hu⟩ := htrav₂.2.2.1 h ehk hhj.symm
      rw [hR₂eq j h hhj.symm (by
        intro hc
        rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact eij.symm h1
        · exact ehi h2)] at hu
      obtain ⟨r', hr'R, -, hu'⟩ := htrav.2.1 j eij.symm hhj
      have hr'mem : r' ∈ {z : V | z ∈ R j h} := by
        show r' ∈ R j h
        rw [hopt.1.2 h j hhj, List.mem_reverse]
        exact hr'R
      exact (hu.2.2.2 r' hr'mem f₁ hu'.2.1 hu'.2.2.1).2
  -- with `f₁ = f_n` the reversed pair is a traversal too, contrary to the uniqueness in (4)
  subst hfeq
  have hswap : IsTraversal G J N F f₁ f₁ R i h := by
    refine ⟨hhi.symm, htrav.2.2.1, htrav.2.1, ?_⟩
    intro u v huv hnd2
    refine htrav.2.2.2 u v huv ?_
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd2 ⊢
    tauto
  obtain ⟨p', q', -, huniq⟩ := hclaim4 R (hclaim5 R hopt.1)
  exact ehi ((huniq h i htrav).1.trans (huniq i h hswap).1.symm)

/-! ## The closing paragraph -/

/-- **The closing paragraph of the proof of 8.5** (printed pp. 44–45). -/
theorem closing [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
          (phi : H.lineGraph ≃g G.induce K'),
        IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' phi)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ Rc u v} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P})
    (hclaim4 : ∀ Rc : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc →
      HasUniqueTraversal G J N F f₁ fn Rc)
    (hclaim5 : ∀ Rc : U → U → List V, RungChoice G J S N Rc →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc)
    (hclaim6 : HasDifferentTraversals G J S N F f₁ fn) :
    False := by
  classical
  obtain ⟨R₀, R₀', a, b, a', b', hR₀, hR₀', htrav₀, htrav₀', hdiff⟩ := hclaim6
  obtain ⟨R, hopt, htrav⟩ := optimal_with_same_traversal G hG J hJ S N hSN F hFcompl hFmin
    hclaim1 P f₁ fn hP hPF hclaim4 hclaim5 R₀ hR₀ a b htrav₀
  obtain ⟨R', hopt', htrav'⟩ := optimal_with_same_traversal G hG J hJ S N hSN F hFcompl hFmin
    hclaim1 P f₁ fn hP hPF hclaim4 hclaim5 R₀' hR₀' a' b' htrav₀'
  have hf₁F : f₁ ∈ F := by
    rw [hPF]
    exact List.mem_of_mem_head? hP.2.1
  have hfnF : fn ∈ F := by
    rw [hPF]
    exact List.mem_of_getLast? hP.2.2
  obtain ⟨hnd, hNa, hNb, hNa', hNb'⟩ :=
    k4_neighbourhoods hJ hSN hf₁F hfnF hopt hopt' htrav htrav' hdiff
  exact k4_endgame G hG J hJ S N hSN hK₄ F hFcompl hFmin hclaim1 P f₁ fn hP hPF
    hclaim4 hclaim5 a b a' b' hnd hNa hNb hNa' hNb' R R' hopt hopt' htrav htrav'

end Workspace.ProofLemmas.Thm85EndgameClosing
