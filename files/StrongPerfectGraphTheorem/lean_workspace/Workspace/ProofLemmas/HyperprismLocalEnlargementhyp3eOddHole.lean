import Workspace.ProofLemmas.HyperprismSplit
import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue

/-!
# `A'ᵢ` is complete to `A''ᵢ` (10.6, even case, printed p. 62)

This module formalizes the last displayed odd hole of the `n`-even block of claim (2) of
**10.6**:

> *"We claim that `A'ᵢ` is complete to `A''ᵢ`.  For if not, let `R''` be an `i`-rung with ends
> `a'' ∈ A''ᵢ` and `b'' ∈ B''ᵢ`, and let `a' ∈ A'ᵢ` be nonadjacent to `a''`.  Since we have seen
> that `fn` has neighbours in at least two of `B₁, B₂, B₃`, it follows that at least two of
> `A''₁, A''₂, A''₃` are nonempty, and therefore we may choose `a ∈ A''ⱼ` for some `j ≠ i`.
> Then*
>
> `a-a'-f₁-⋯-fn-b''-R''-a''-a`
>
> *is an odd hole, a contradiction.  So `A'ᵢ` is complete to `A''ᵢ` for each `i`, and similarly
> `B'ᵢ` is complete to `B''ᵢ` for each `i`."*

`P = A'` and `Q = B'`, so `A i \ P i = A''ᵢ` and `B i \ Q i = B''ᵢ`.  The cycle above is
`(a :: a' :: f) ++ R''.reverse`; it has `3 + f.length + pathLength R''` edges, which is odd
because `f.length` is even (the `n`-even case) and every rung of a Berge hyperprism has even
length.  The *"and similarly"* sentence is obtained by swapping `A` with `B` and reversing `f`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3e

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.HyperprismSplit

/-- *"We claim that `A'ᵢ` is complete to `A''ᵢ`."*  The hypotheses say that `P i` is the set of
neighbours of `f₁` in `A i` and that `B i \ Q i` is the set of neighbours of `fn` in `B i`, that
`f` has no other neighbours in the hyperprism, and (`hDoubleSupport`) that for each `i` some
other strip has a nonempty `A''`. -/
theorem primeCompleteA
    {V : Type*} (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q)
    (hDoubleSupport : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (A j \ P j).Nonempty)
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn)
    (heven : Even f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hAedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ a ∈ A i,
      G.Adj z a → z = f₁ ∧ a ∈ P i)
    (hBedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ b ∈ B i,
      G.Adj z b → z = fn ∧ b ∉ Q i)
    (hPadj : ∀ (i : Fin 3), ∀ a ∈ P i, G.Adj f₁ a)
    (hQadj : ∀ (i : Fin 3), ∀ b ∈ B i, b ∉ Q i → G.Adj fn b)
    (hCnone : ∀ z ∈ f, ∀ (i : Fin 3) (c : V), c ∈ C i → ¬ G.Adj z c) :
    ∀ i : Fin 3, Complete G (P i) (A i \ P i) := by
  intro i a' ha' a'' ha''
  by_contra hnadj
  -- *"let `R''` be an `i`-rung with ends `a'' ∈ A''ᵢ` and `b'' ∈ B''ᵢ`"*
  obtain ⟨R, b'', hR, hb''⟩ := exists_rung_dprime_of_notMem_P hH hs ha''.1 ha''.2
  -- *"we may choose `a ∈ A''ⱼ` for some `j ≠ i`"*
  obtain ⟨j, hji, aa, haa⟩ := hDoubleSupport i
  have ha'A : a' ∈ A i := hs.PA i ha'
  have hf₁mem : f₁ ∈ f := PathBasics.head_mem hf.2.1
  have hfnmem : fn ∈ f := PathBasics.getLast_mem hf.2.2
  have hf₁a' : G.Adj f₁ a' := hPadj i a' ha'
  have hfnb'' : G.Adj fn b'' := hQadj i b'' hR.2.1 hb''
  have ha'nf : a' ∉ f := fun h =>
    hfout a' h (mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inl ha'A)⟩)
  have haanf : aa ∉ f := fun h =>
    hfout aa h (mem_hyperVerts_iff.mpr ⟨j, Or.inl (Or.inl haa.1)⟩)
  have haaNotS : aa ∉ A i ∪ B i ∪ C i := notMem_S hH hji (Or.inl (Or.inl haa.1))
  have haa_ne_a' : aa ≠ a' := by
    intro h
    exact haaNotS (by rw [h]; exact Or.inl (Or.inl ha'A))
  -- the path `a'-f₁-⋯-fn`
  have hP1 : IsPathFrom G (a' :: f) a' fn := by
    refine PathAttach.isPathFrom_cons hf hf₁a'.symm ha'nf ?_
    intro x hx hxf₁ hadj
    exact hxf₁ (hAedges i x hx a' ha'A hadj.symm).1
  have haaa' : G.Adj aa a' := complete_A hH hji aa haa.1 a' ha'A
  -- the path `a-a'-f₁-⋯-fn`
  have hP2 : IsPathFrom G (aa :: (a' :: f)) aa fn := by
    refine PathAttach.isPathFrom_cons hP1 haaa' ?_ ?_
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact haa_ne_a' h
      · exact haanf h
    · intro x hx hxa' hadj
      rcases List.mem_cons.mp hx with h | hx
      · exact hxa' h
      · exact haa.2 (hAedges j x hx aa haa.1 hadj.symm).2
  have hRrev : IsPathFrom G R.reverse b'' a'' := PathBasics.isPathFrom_reverse hR.2.2.1
  have hRmemS : ∀ y ∈ R, y ∈ A i ∪ B i ∪ C i := rung_mem_S hR
  have hdisj : ∀ x ∈ aa :: (a' :: f), x ∉ R.reverse := by
    intro x hx hxR
    rw [List.mem_reverse] at hxR
    rcases List.mem_cons.mp hx with rfl | hx
    · exact haaNotS (hRmemS x hxR)
    rcases List.mem_cons.mp hx with rfl | hx
    · have h := rung_eq_A hH hR hxR ha'A
      rw [h] at ha'
      exact ha''.2 ha'
    · exact hfout x hx (rung_subset_hyperVerts hR x hxR)
  have hcross : ∀ x ∈ aa :: (a' :: f), ∀ y ∈ R.reverse,
      (G.Adj x y ↔ (x = fn ∧ y = b'') ∨ (x = aa ∧ y = a'')) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    have hyS := hRmemS y hy
    rcases List.mem_cons.mp hx with hxeq | hx
    · rw [hxeq]
      constructor
      · intro hadj
        rcases cross hH hji (Or.inl (Or.inl haa.1)) hyS hadj with h | h
        · exact Or.inr ⟨rfl, rung_eq_A hH hR hy h.2⟩
        · exact absurd h.1 (Set.disjoint_left.mp (hH.2.1 j j) haa.1)
      · rintro (⟨hxfn, -⟩ | ⟨-, hya⟩)
        · rw [hxfn] at haanf
          exact absurd hfnmem haanf
        · rw [hya]
          exact complete_A hH hji aa haa.1 a'' ha''.1
    rcases List.mem_cons.mp hx with hxeq | hx
    · rw [hxeq]
      have hnadj' : ¬ G.Adj a' y := by
        rcases hyS with (hyA | hyB) | hyC
        · rw [rung_eq_A hH hR hy hyA]
          exact hnadj
        · refine no_edge_prime_dprime hH hs i (Or.inl ha') (Or.inr ⟨hyB, ?_⟩)
          rw [rung_eq_B hH hR hy hyB]
          exact hb''
        · have hyint : y ∈ SPGT.interior R := by
            rw [PathBasics.mem_interior_iff_of_pathFrom hR.2.2.1]
            refine ⟨hy, ?_, ?_⟩
            · intro h
              exact Set.disjoint_left.mp (hH.2.2.1 i i) ha''.1 (h ▸ hyC)
            · intro h
              exact Set.disjoint_left.mp (hH.2.2.2.1 i i) hR.2.1 (h ▸ hyC)
          exact no_edge_prime_dprime hH hs i (Or.inl ha')
            (Or.inl ⟨R, a'', b'', hR, ha''.2, hb'', hyint⟩)
      refine iff_of_false hnadj' ?_
      rintro (⟨hxfn, -⟩ | ⟨hxaa, -⟩)
      · rw [hxfn] at ha'nf
        exact ha'nf hfnmem
      · exact haa_ne_a' hxaa.symm
    · have hxnotaa : x ≠ aa := by
        intro h
        rw [h] at hx
        exact haanf hx
      constructor
      · intro hadj
        rcases hyS with (hyA | hyB) | hyC
        · have h2 := (hAedges i x hx y hyA hadj).2
          rw [rung_eq_A hH hR hy hyA] at h2
          exact absurd h2 ha''.2
        · exact Or.inl ⟨(hBedges i x hx y hyB hadj).1, rung_eq_B hH hR hy hyB⟩
        · exact absurd hadj (hCnone x hx i y hyC)
      · rintro (⟨hx1, hy1⟩ | ⟨hx1, -⟩)
        · rw [hx1, hy1]
          exact hfnb''
        · exact absurd hx1 hxnotaa
  have hflen : 0 < f.length := PathBasics.path_length_pos hf.1
  have hRlen2 : 2 ≤ R.length := rung_two_le_length hH hR
  have hlen : 4 ≤ (aa :: (a' :: f)).length + R.reverse.length := by
    simp only [List.length_cons, List.length_reverse]
    omega
  have hhole := PathGlue.glue_hole hP2 hRrev hdisj hcross hlen
  have hev := hG.1 _ hhole
  have hRlen : R.length = SPGT.pathLength R + 1 :=
    PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
  have hReven := rung_even hG hH hR
  rw [holeLength, List.length_append, List.length_reverse] at hev
  simp only [List.length_cons] at hev
  rw [Nat.even_iff] at hev heven hReven
  omega

/-- *"and similarly `B'ᵢ` is complete to `B''ᵢ` for each `i`"* — `primeCompleteA` applied to the
hyperprism with `A` and `B` exchanged and the path `f` reversed. -/
theorem primeCompleteB
    {V : Type*} (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q)
    (hPrimeSupport : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (Q j).Nonempty)
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn)
    (heven : Even f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hAedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ a ∈ A i,
      G.Adj z a → z = f₁ ∧ a ∈ P i)
    (hBedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ b ∈ B i,
      G.Adj z b → z = fn ∧ b ∉ Q i)
    (hPadj : ∀ (i : Fin 3), ∀ a ∈ P i, G.Adj f₁ a)
    (hQadj : ∀ (i : Fin 3), ∀ b ∈ B i, b ∉ Q i → G.Adj fn b)
    (hCnone : ∀ z ∈ f, ∀ (i : Fin 3) (c : V), c ∈ C i → ¬ G.Adj z c) :
    ∀ i : Fin 3, Complete G (Q i) (B i \ Q i) := by
  have hswap : IsRungSplit G B A C (fun k => B k \ Q k) (fun k => A k \ P k) := by
    refine ⟨fun m => Set.diff_subset, fun m => Set.diff_subset, ?_⟩
    intro m p a b hp
    have hrev : IsRungFrom G A B C m p.reverse b a := by
      refine ⟨hp.2.1, hp.1, PathBasics.isPathFrom_reverse hp.2.2.1, ?_⟩
      intro w hw
      exact hp.2.2.2 w (PathBasics.mem_interior_reverse.mp hw)
    rcases hs.dich m p.reverse b a hrev with ⟨hbP, haQ⟩ | ⟨hbP, haQ⟩
    · exact Or.inr ⟨fun h => h.2 haQ, fun h => h.2 hbP⟩
    · exact Or.inl ⟨⟨hp.1, haQ⟩, ⟨hp.2.1, hbP⟩⟩
  have hDS : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (B j \ (B j \ Q j)).Nonempty := by
    intro i
    obtain ⟨j, hji, q, hq⟩ := hPrimeSupport i
    exact ⟨j, hji, q, hs.QB j hq, fun h => h.2 hq⟩
  have key := primeCompleteA G B A C (fun k => B k \ Q k) (fun k => A k \ P k) hG
    (HyperprismTwoAttachments.isHyperprism_swap hH) hswap hDS
    (PathBasics.isPathFrom_reverse hf)
    (by simpa using heven)
    (by
      intro z hz hmem
      rw [List.mem_reverse] at hz
      exact hfout z hz (by rwa [hyperVerts_swap'] at hmem))
    (by
      intro k z hz a ha hadj
      rw [List.mem_reverse] at hz
      obtain ⟨h1, h2⟩ := hBedges k z hz a ha hadj
      exact ⟨h1, ha, h2⟩)
    (by
      intro k z hz b hb hadj
      rw [List.mem_reverse] at hz
      obtain ⟨h1, h2⟩ := hAedges k z hz b hb hadj
      exact ⟨h1, fun h => h.2 h2⟩)
    (fun k a ha => hQadj k a ha.1 ha.2)
    (by
      intro k b hb hbn
      refine hPadj k b ?_
      by_contra hcon
      exact hbn ⟨hb, hcon⟩)
    (by
      intro z hz
      rw [List.mem_reverse] at hz
      exact hCnone z hz)
  intro i b' hb' b'' hb''
  have hb'B : b' ∈ B i := hs.QB i hb'
  exact (key i b'' hb'' b' ⟨hb'B, fun h => h.2 hb'⟩).symm

end Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3e
