import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm82RungFamily
import Workspace.ProofLemmas.Thm85RungChoice
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameK4Shape

/-!
# 8.5: changing a choice of rungs on a single edge

PAPER (printed p. 44): *"For any choice of rungs, there is an optimal choice with the same
traversal (just replace rungs that miss `X` by rungs that meet `X` wherever possible)."*

The recipe works because of the two facts proved here.

* `exists_rung_choice_replacing` performs one replacement: it turns a choice of rungs into a
  choice that agrees with it away from one prescribed edge and takes a prescribed rung there.
* `attachment_edges_meet_traversal` is *"`K` consists precisely of the edges of `J` with exactly
  one end in common with `hi`, together possibly with `hi` itself"* for a choice that is not yet
  optimal: no strip of an edge disjoint from the traversal meets `X`.  So the only rung the
  recipe ever has to replace is the rung of the traversal edge itself, and the traversal edge is
  the one edge that the definition of a traversal says nothing about.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgameOptimalChoice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-- **"Take another choice of rungs, differing from this one on only one edge"** (printed
p. 44).  Any prescribed rung on one edge extends to a choice of rungs that is unchanged
elsewhere. -/
theorem exists_rung_choice_replacing [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
    {S : U → U → Set V} {N : U → Set V} (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : RungChoice G J S N R)
    {u v : U} (huv : J.Adj u v) {L : List V} (hL : IsUVRung G J S N u v L) :
    ∃ R₂ : U → U → List V, RungChoice G J S N R₂ ∧ R₂ u v = L ∧
      ∀ a b : U, J.Adj a b → s(a, b) ≠ s(u, v) → R₂ a b = R a b := by
  classical
  set C : U → U → List V :=
    fun a b => if a = u ∧ b = v then L else if a = v ∧ b = u then L.reverse else R a b with hC
  have huvne : u ≠ v := huv.ne
  have hCrung : ∀ a b : U, J.Adj a b → IsUVRung G J S N a b (C a b) := by
    intro a b hab
    by_cases h1 : a = u ∧ b = v
    · obtain ⟨rfl, rfl⟩ := h1
      simpa [hC] using hL
    · by_cases h2 : a = v ∧ b = u
      · obtain ⟨rfl, rfl⟩ := h2
        have : C a b = L.reverse := by simp [hC, h1, huvne.symm]
        rw [this]
        exact Thm82RungFamily.rung_reverse hSN hL
      · have : C a b = R a b := by simp [hC, h1, h2]
        rw [this]
        exact hR.1 a b hab
  obtain ⟨R₂, hfam, hsym, hchoice⟩ :=
    Thm85RungChoice.exists_symmetric_rung_family_of_choice hSN C hCrung
  refine ⟨R₂, ⟨hfam, hsym⟩, ?_, ?_⟩
  · have hCuv : C u v = L := by simp [hC]
    have hCvu : C v u = L.reverse := by simp [hC, huvne.symm, huvne]
    rcases hchoice u v huv with h | h
    · rw [h, hCuv]
    · rw [h, hCvu, List.reverse_reverse]
  · intro a b hab hne
    have h1 : ¬ (a = u ∧ b = v) := by
      rintro ⟨rfl, rfl⟩; exact hne rfl
    have h2 : ¬ (a = v ∧ b = u) := by
      rintro ⟨rfl, rfl⟩; exact hne (Sym2.eq_swap)
    have h3 : ¬ (b = u ∧ a = v) := by
      rintro ⟨rfl, rfl⟩; exact h2 ⟨rfl, rfl⟩
    have h4 : ¬ (b = v ∧ a = u) := by
      rintro ⟨rfl, rfl⟩; exact h1 ⟨rfl, rfl⟩
    have hCab : C a b = R a b := by simp [hC, h1, h2]
    have hCba : C b a = R b a := by simp [hC, h3, h4]
    rcases hchoice a b hab with h | h
    · rw [h, hCab]
    · rw [h, hCba, hR.2 a b hab, List.reverse_reverse]

/-- **"`K` consists precisely of the edges of `J` with exactly one end in common with `hi`,
together possibly with `hi` itself"** (printed p. 44), in the form used by the closing
paragraph: for any choice of rungs with traversal `ij`, no strip of an edge disjoint from `ij`
meets the attachment set `X`.

If it did, one would change the choice on that one edge so that its rung passes through the
attachment.  The changed choice still satisfies the first two bullets of claim (4) at `(i,j)`,
so its own traversal is either `ij` itself — impossible, since the third bullet would make the
changed rung anticomplete to `F` — or an edge meeting `ij` in one vertex, which strands one of
`i, j` with only two neighbours, or an edge disjoint from `ij`, which is the degenerate `K₄` of
`Thm85EndgameK4Shape.disjoint_traversals_absurd`. -/
theorem attachment_edges_meet_traversal [Fintype V] [DecidableEq V] [Fintype U]
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
      HasUniqueTraversal G J N F f₁ fn Rc)
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
  -- change the choice on the edge `uv` so that its rung passes through an attachment
  obtain ⟨x, hxX, hxS⟩ := hK
  obtain ⟨L, hL, hxL⟩ := StripSystemBasics.exists_rung hSN huv hxS
  obtain ⟨R₂, hR₂, hR₂uv, hR₂eq⟩ := exists_rung_choice_replacing hSN R hR huv hL
  obtain ⟨i₂, j₂, htrav₂, -⟩ := hclaim4 R₂ (hclaim5 R₂ hR₂)
  have hi₂j₂ : J.Adj i₂ j₂ := htrav₂.1
  -- the two bullets of claim (4) at `(i,j)` survive the change
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
  -- the new rung on `uv` is not anticomplete to `F`
  obtain ⟨-, f, hfF, hxf⟩ := hxX
  have hmemx : x ∈ {z : V | z ∈ R₂ u v} := by
    show x ∈ R₂ u v
    rw [hR₂uv]
    exact hxL
  by_cases hiT : i = i₂ ∨ i = j₂
  · by_cases hjT : j = i₂ ∨ j = j₂
    · -- the new traversal is `ij` again, and its third bullet kills the new rung
      have hcases : (i₂ = i ∧ j₂ = j) ∨ (i₂ = j ∧ j₂ = i) := by
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
    · -- `i` is an end of the new traversal but `j` is not: `j` is left with two neighbours
      push_neg at hjT
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
    · -- symmetrically, `i` is left with two neighbours
      push_neg at hiT
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
    · -- the new traversal is disjoint from `ij`: the printed `K₄` argument
      push_neg at hiT hjT
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

end Workspace.ProofLemmas.Thm85EndgameOptimalChoice
