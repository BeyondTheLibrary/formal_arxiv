import Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality
import Workspace.ProofLemmas.HyperprismLocalEnlargementPathFacts
import Workspace.ProofLemmas.HyperprismSplit
import Workspace.ProofLemmas.PathAttach

/-!
# The odd block of claim (2) of 10.6 — the odd-hole steps

This module collects the "… is not an odd hole" steps of the paragraph of 10.6 that
begins *"Now assume `n` is odd."* (printed p. 62).  Throughout, `f = f₁-⋯-fₙ` is the
attachment path, which now has **odd** length as a list of vertices, so every cycle
built from it and one rung of the (even) hyperprism has odd length.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oCore

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.HyperprismSplit

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

/-- Gluing two paths along their two ends produces a hole, so in a Berge graph the total
number of vertices is even. -/
theorem glue_even (hG : Berge G) {P Q : List V} {u₀ u₁ w₀ w₁ : V}
    (hP : IsPathFrom G P u₀ u₁) (hQ : IsPathFrom G Q w₀ w₁)
    (hdisj : ∀ x ∈ P, x ∉ Q)
    (hcross : ∀ x ∈ P, ∀ y ∈ Q, (G.Adj x y ↔ (x = u₁ ∧ y = w₀) ∨ (x = u₀ ∧ y = w₁)))
    (hlen : 4 ≤ P.length + Q.length) : Even (P.length + Q.length) := by
  have h := hG.1 _ (PathGlue.glue_hole hP hQ hdisj hcross hlen)
  simpa [holeLength] using h

/-- In a hyperprism of a Berge graph there is no edge from any `A`-set to any `B`-set:
inside a strip such an edge would be a rung of length one, and between two strips the
"no other edges" clause forbids it. -/
theorem no_edge_A_B_any (hG : Berge G) (hH : IsHyperprism G A B C) {m m' : Fin 3} {a b : V}
    (ha : a ∈ A m) (hb : b ∈ B m') : ¬ G.Adj a b := by
  by_cases h : m = m'
  · subst h
    exact no_edge_A_B hG hH m ha hb
  · intro hadj
    rcases cross hH h (Or.inl (Or.inl ha)) (Or.inl (Or.inr hb)) hadj with hh | hh
    · exact Set.disjoint_left.mp (hH.2.1 m' m') hh.2 hb
    · exact Set.disjoint_left.mp (hH.2.1 m m) ha hh.1

/-- PAPER (10.6, odd case, printed p. 62): *"Since `a₁-f₁-⋯-fₙ-b₂-b₁-R₁-a₁` is not an odd
hole, it follows that `b₁ ∈ X`."*  Here `xA = a₁`, `xB = b₂` and `b₀ = b₁`. -/
theorem endAttachmentB (hG : Berge G) (hH : IsHyperprism G A B C)
    {f R : List V} {f₁ fn xA xB b₀ : V}
    (hf : IsPathFrom G f f₁ fn) (hodd : Odd f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    {i j : Fin 3} (hij : i ≠ j) (hxAA : xA ∈ A i) (hxBB : xB ∈ B j)
    (hR : IsRungFrom G A B C i R xA b₀)
    (hxAf₁ : G.Adj xA f₁) (hfnxB : G.Adj fn xB)
    (hleft : ∀ z ∈ f, G.Adj xA z → z = f₁)
    (hright : ∀ z ∈ f, G.Adj xB z → z = fn)
    (hCnone : ∀ z ∈ f, ∀ (m : Fin 3) (c : V), c ∈ C m → ¬ G.Adj z c) :
    ∃ z ∈ f, G.Adj z b₀ := by
  by_contra hcon
  push_neg at hcon
  have hxBnf : xB ∉ f := fun h =>
    hfout xB h (mem_hyperVerts_iff.mpr ⟨j, Or.inl (Or.inr hxBB)⟩)
  have hP : IsPathFrom G (f ++ [xB]) f₁ xB :=
    PathAttach.isPathFrom_concat hf hfnxB.symm hxBnf
      (fun x hx hxn hadj => hxn (hright x hx hadj))
  have hQ : IsPathFrom G R.reverse b₀ xA := PathBasics.isPathFrom_reverse hR.2.2.1
  have hdisj : ∀ x ∈ f ++ [xB], x ∉ R.reverse := by
    intro x hx hxR
    rw [List.mem_reverse] at hxR
    rcases List.mem_append.mp hx with hxf | hxb
    · exact hfout x hxf (rung_subset_hyperVerts hR x hxR)
    · have : x = xB := by simpa using hxb
      subst x
      exact notMem_S hH (Ne.symm hij) (Or.inl (Or.inr hxBB)) (rung_mem_S hR xB hxR)
  have hcross : ∀ x ∈ f ++ [xB], ∀ y ∈ R.reverse,
      (G.Adj x y ↔ (x = xB ∧ y = b₀) ∨ (x = f₁ ∧ y = xA)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    have hyS := rung_mem_S hR y hy
    rcases List.mem_append.mp hx with hxf | hxb
    · have hxnB : x ≠ xB := fun h => hxBnf (h ▸ hxf)
      constructor
      · intro hadj
        rcases hyS with (hyA | hyB) | hyC
        · have hya : y = xA := rung_eq_A hH hR hy hyA
          exact Or.inr ⟨hleft x hxf (hya ▸ hadj.symm), hya⟩
        · have hyb : y = b₀ := rung_eq_B hH hR hy hyB
          exact absurd (hyb ▸ hadj) (hcon x hxf)
        · exact absurd hadj (hCnone x hxf i y hyC)
      · rintro (⟨h, -⟩ | ⟨rfl, rfl⟩)
        · exact absurd h hxnB
        · exact hxAf₁.symm
    · have hxeq : x = xB := by simpa using hxb
      subst x
      constructor
      · intro hadj
        rcases cross hH (Ne.symm hij) (Or.inl (Or.inr hxBB)) hyS hadj with hh | hh
        · exact absurd hxBB (Set.disjoint_left.mp (hH.2.1 j j) hh.1)
        · exact Or.inl ⟨rfl, rung_eq_B hH hR hy hh.2⟩
      · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
        · exact complete_B hH (Ne.symm hij) xB hxBB _ hR.2.1
        · exact absurd h.symm (fun hh => hxBnf (hh ▸ PathBasics.head_mem hf.2.1))
  have hRlen : R.length = pathLength R + 1 :=
    PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
  have hRev := rung_even hG hH hR
  have hR2 : 2 ≤ R.length := rung_two_le_length hH hR
  have hflen : 0 < f.length := PathBasics.path_length_pos hf.1
  have := glue_even hG hP hQ hdisj hcross (by
    simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
    omega)
  simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil] at this
  rw [Nat.even_iff] at this
  rw [Nat.even_iff] at hRev
  rw [Nat.odd_iff] at hodd
  omega

/-- The mirror of `endAttachmentB`: *"and similarly `a₂ ∈ X`"*. -/
theorem endAttachmentA (hG : Berge G) (hH : IsHyperprism G A B C)
    {f R : List V} {f₁ fn xA xB a₁ : V}
    (hf : IsPathFrom G f f₁ fn) (hodd : Odd f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    {i j : Fin 3} (hij : i ≠ j) (hxAA : xA ∈ A i) (hxBB : xB ∈ B j)
    (hR : IsRungFrom G A B C j R a₁ xB)
    (hxAf₁ : G.Adj xA f₁) (hfnxB : G.Adj fn xB)
    (hleft : ∀ z ∈ f, G.Adj xA z → z = f₁)
    (hright : ∀ z ∈ f, G.Adj xB z → z = fn)
    (hCnone : ∀ z ∈ f, ∀ (m : Fin 3) (c : V), c ∈ C m → ¬ G.Adj z c) :
    ∃ z ∈ f, G.Adj z a₁ := by
  by_contra hcon
  push_neg at hcon
  have hxAnf : xA ∉ f := fun h =>
    hfout xA h (mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inl hxAA)⟩)
  have hfrev : IsPathFrom G f.reverse fn f₁ := PathBasics.isPathFrom_reverse hf
  have hP : IsPathFrom G (f.reverse ++ [xA]) fn xA := by
    refine PathAttach.isPathFrom_concat hfrev hxAf₁ (by simpa using hxAnf) ?_
    intro x hx hxn hadj
    rw [List.mem_reverse] at hx
    exact hxn (hleft x hx hadj)
  have hdisj : ∀ x ∈ f.reverse ++ [xA], x ∉ R := by
    intro x hx hxR
    rcases List.mem_append.mp hx with hxf | hxa
    · rw [List.mem_reverse] at hxf
      exact hfout x hxf (rung_subset_hyperVerts hR x hxR)
    · have : x = xA := by simpa using hxa
      subst x
      exact notMem_S hH hij (Or.inl (Or.inl hxAA)) (rung_mem_S hR xA hxR)
  have hcross : ∀ x ∈ f.reverse ++ [xA], ∀ y ∈ R,
      (G.Adj x y ↔ (x = xA ∧ y = a₁) ∨ (x = fn ∧ y = xB)) := by
    intro x hx y hy
    have hyS := rung_mem_S hR y hy
    rcases List.mem_append.mp hx with hxf | hxa
    · rw [List.mem_reverse] at hxf
      have hxnA : x ≠ xA := fun h => hxAnf (h ▸ hxf)
      constructor
      · intro hadj
        rcases hyS with (hyA | hyB) | hyC
        · have hya : y = a₁ := rung_eq_A hH hR hy hyA
          exact absurd (hya ▸ hadj) (hcon x hxf)
        · have hyb : y = xB := rung_eq_B hH hR hy hyB
          refine Or.inr ⟨hright x hxf ?_, hyb⟩
          rw [hyb] at hadj
          exact hadj.symm
        · exact absurd hadj (hCnone x hxf j y hyC)
      · rintro (⟨h, -⟩ | ⟨rfl, rfl⟩)
        · exact absurd h hxnA
        · exact hfnxB
    · have hxeq : x = xA := by simpa using hxa
      subst x
      constructor
      · intro hadj
        rcases cross hH hij (Or.inl (Or.inl hxAA)) hyS hadj with hh | hh
        · exact Or.inl ⟨rfl, rung_eq_A hH hR hy hh.2⟩
        · exact absurd hh.1 (Set.disjoint_left.mp (hH.2.1 i i) hxAA)
      · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
        · exact complete_A hH hij xA hxAA _ hR.1
        · exact absurd h.symm (fun hh => hxAnf (hh ▸ PathBasics.getLast_mem hf.2.2))
  have hRlen : R.length = pathLength R + 1 :=
    PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
  have hRev := rung_even hG hH hR
  have hR2 : 2 ≤ R.length := rung_two_le_length hH hR
  have hflen : 0 < f.length := PathBasics.path_length_pos hf.1
  have := glue_even hG hP hR.2.2.1 hdisj hcross (by
    simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
    omega)
  simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil] at this
  rw [Nat.even_iff] at this
  rw [Nat.even_iff] at hRev
  rw [Nat.odd_iff] at hodd
  omega


/-- PAPER (10.6, odd case, printed p. 62): *"Suppose that `fₙ` is not adjacent to `b₁`; so
`f₁` is adjacent to `b₁`, and `n ≥ 2`, and `fₙ` is adjacent to `a₂`.  But then
`b₁-f₁-⋯-fₙ-b₂-b₁` is an odd hole, a contradiction."* -/
theorem shortOddHole (hG : Berge G) (hH : IsHyperprism G A B C)
    {f : List V} {f₁ fn b₀ xB : V}
    (hf : IsPathFrom G f f₁ fn) (hodd : Odd f.length) (h2 : 2 ≤ f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    {i j : Fin 3} (hij : i ≠ j) (hb₀ : b₀ ∈ B i) (hxBB : xB ∈ B j)
    (hf₁b₀ : G.Adj f₁ b₀) (hfnxB : G.Adj fn xB)
    (hb₀only : ∀ z ∈ f, G.Adj z b₀ → z = f₁)
    (hxBonly : ∀ z ∈ f, G.Adj z xB → z = fn) : False := by
  have hbne : xB ≠ b₀ := fun h => Set.disjoint_left.mp (hH.2.2.2.2.2.1 j i hij.symm)
    (h ▸ hxBB) hb₀
  have hQ : IsPathFrom G [xB, b₀] xB b₀ :=
    ⟨PathBasics.isPathList_pair (complete_B hH hij.symm xB hxBB b₀ hb₀), rfl, rfl⟩
  have hxBnf : xB ∉ f := fun h =>
    hfout xB h (mem_hyperVerts_iff.mpr ⟨j, Or.inl (Or.inr hxBB)⟩)
  have hb₀nf : b₀ ∉ f := fun h =>
    hfout b₀ h (mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inr hb₀)⟩)
  have hdisj : ∀ x ∈ f, x ∉ [xB, b₀] := by
    intro x hx hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact hxBnf hx
    · exact hb₀nf hx
  have hcross : ∀ x ∈ f, ∀ y ∈ [xB, b₀],
      (G.Adj x y ↔ (x = fn ∧ y = xB) ∨ (x = f₁ ∧ y = b₀)) := by
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · constructor
      · intro hadj
        exact Or.inl ⟨hxBonly x hx hadj, rfl⟩
      · rintro (⟨rfl, -⟩ | ⟨-, h⟩)
        · exact hfnxB
        · exact absurd h hbne
    · constructor
      · intro hadj
        exact Or.inr ⟨hb₀only x hx hadj, rfl⟩
      · rintro (⟨-, h⟩ | ⟨rfl, -⟩)
        · exact absurd h.symm hbne
        · exact hf₁b₀
  have := glue_even hG hf hQ hdisj hcross (by simp; omega)
  simp only [List.length_cons, List.length_nil] at this
  rw [Nat.even_iff] at this
  rw [Nat.odd_iff] at hodd
  omega

/-- PAPER (10.6, odd case, printed p. 62): *"Hence for all `1 ≤ i ≤ 3`, and for every `i`-rung
with ends `a ∈ A` and `b ∈ B`, `a ∈ X` if and only if `b ∈ X`, and if so then `f₁` is adjacent
to `a` and `fₙ` to `b`."*

Both implications come from an odd cycle built out of the rung, the path `f`, and one further
end of the hyperprism in a strip other than the rung's own. -/
theorem rungXnor (hG : Berge G) (hH : IsHyperprism G A B C)
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn) (hodd : Odd f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hAuniq : ∀ (k : Fin 3), ∀ z ∈ f, ∀ a ∈ A k, G.Adj z a → z = f₁)
    (hBuniq : ∀ (k : Fin 3), ∀ z ∈ f, ∀ b ∈ B k, G.Adj z b → z = fn)
    (hCnone : ∀ z ∈ f, ∀ (m : Fin 3) (c : V), c ∈ C m → ¬ G.Adj z c)
    {m : Fin 3} {R : List V} {a b : V} (hR : IsRungFrom G A B C m R a b)
    {t : Fin 3} (htm : t ≠ m) {a' b' : V} (ha' : a' ∈ A t) (hb' : b' ∈ B t)
    (hf₁a' : G.Adj f₁ a') (hfnb' : G.Adj fn b') :
    (G.Adj f₁ a ↔ G.Adj fn b) := by
  have hf₁f : f₁ ∈ f := PathBasics.head_mem hf.2.1
  have hfnf : fn ∈ f := PathBasics.getLast_mem hf.2.2
  have hRlen : R.length = pathLength R + 1 :=
    PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
  have hRev := rung_even hG hH hR
  have hR2 : 2 ≤ R.length := rung_two_le_length hH hR
  have hflen : 0 < f.length := PathBasics.path_length_pos hf.1
  have ha'nf : a' ∉ f := fun h =>
    hfout a' h (mem_hyperVerts_iff.mpr ⟨t, Or.inl (Or.inl ha')⟩)
  have hb'nf : b' ∉ f := fun h =>
    hfout b' h (mem_hyperVerts_iff.mpr ⟨t, Or.inl (Or.inr hb')⟩)
  constructor
  · intro hfa
    by_contra hnb
    have hP : IsPathFrom G (f ++ [b']) f₁ b' := by
      refine PathAttach.isPathFrom_concat hf hfnb'.symm hb'nf ?_
      intro x hx hxn hadj
      exact hxn (hBuniq t x hx b' hb' hadj.symm)
    have hdisj : ∀ x ∈ f ++ [b'], x ∉ R.reverse := by
      intro x hx hxR
      rw [List.mem_reverse] at hxR
      rcases List.mem_append.mp hx with hxf | hxb
      · exact hfout x hxf (rung_subset_hyperVerts hR x hxR)
      · have hxe : x = b' := by simpa using hxb
        subst x
        exact notMem_S hH htm (Or.inl (Or.inr hb')) (rung_mem_S hR b' hxR)
    have hcross : ∀ x ∈ f ++ [b'], ∀ y ∈ R.reverse,
        (G.Adj x y ↔ (x = b' ∧ y = b) ∨ (x = f₁ ∧ y = a)) := by
      intro x hx y hy
      rw [List.mem_reverse] at hy
      have hyS := rung_mem_S hR y hy
      rcases List.mem_append.mp hx with hxf | hxb
      · have hxnb' : x ≠ b' := fun h => hb'nf (h ▸ hxf)
        constructor
        · intro hadj
          rcases hyS with (hyA | hyB) | hyC
          · exact Or.inr ⟨hAuniq m x hxf y hyA hadj, rung_eq_A hH hR hy hyA⟩
          · have hyb : y = b := rung_eq_B hH hR hy hyB
            have hxfn : x = fn := hBuniq m x hxf y hyB hadj
            rw [hxfn, hyb] at hadj
            exact absurd hadj hnb
          · exact absurd hadj (hCnone x hxf m y hyC)
        · rintro (⟨h, -⟩ | ⟨rfl, rfl⟩)
          · exact absurd h hxnb'
          · exact hfa
      · have hxe : x = b' := by simpa using hxb
        subst x
        constructor
        · intro hadj
          rcases cross hH htm (Or.inl (Or.inr hb')) hyS hadj with hh | hh
          · exact absurd hb' (Set.disjoint_left.mp (hH.2.1 t t) hh.1)
          · exact Or.inl ⟨rfl, rung_eq_B hH hR hy hh.2⟩
        · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
          · exact complete_B hH htm b' hb' _ hR.2.1
          · exact absurd (h ▸ hf₁f) hb'nf
    have := glue_even hG hP (PathBasics.isPathFrom_reverse hR.2.2.1) hdisj hcross (by
      simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
      omega)
    simp only [List.length_append, List.length_reverse, List.length_cons,
      List.length_nil] at this
    rw [Nat.even_iff] at this
    rw [Nat.even_iff] at hRev
    rw [Nat.odd_iff] at hodd
    omega
  · intro hfb
    by_contra hna
    have hfrev : IsPathFrom G f.reverse fn f₁ := PathBasics.isPathFrom_reverse hf
    have hP : IsPathFrom G (f.reverse ++ [a']) fn a' := by
      refine PathAttach.isPathFrom_concat hfrev hf₁a'.symm (by simpa using ha'nf) ?_
      intro x hx hxn hadj
      rw [List.mem_reverse] at hx
      exact hxn (hAuniq t x hx a' ha' hadj.symm)
    have hdisj : ∀ x ∈ f.reverse ++ [a'], x ∉ R := by
      intro x hx hxR
      rcases List.mem_append.mp hx with hxf | hxa
      · rw [List.mem_reverse] at hxf
        exact hfout x hxf (rung_subset_hyperVerts hR x hxR)
      · have hxe : x = a' := by simpa using hxa
        subst x
        exact notMem_S hH htm (Or.inl (Or.inl ha')) (rung_mem_S hR a' hxR)
    have hcross : ∀ x ∈ f.reverse ++ [a'], ∀ y ∈ R,
        (G.Adj x y ↔ (x = a' ∧ y = a) ∨ (x = fn ∧ y = b)) := by
      intro x hx y hy
      have hyS := rung_mem_S hR y hy
      rcases List.mem_append.mp hx with hxf | hxa
      · rw [List.mem_reverse] at hxf
        have hxna' : x ≠ a' := fun h => ha'nf (h ▸ hxf)
        constructor
        · intro hadj
          rcases hyS with (hyA | hyB) | hyC
          · have hya : y = a := rung_eq_A hH hR hy hyA
            have hxf₁ : x = f₁ := hAuniq m x hxf y hyA hadj
            rw [hxf₁, hya] at hadj
            exact absurd hadj hna
          · exact Or.inr ⟨hBuniq m x hxf y hyB hadj, rung_eq_B hH hR hy hyB⟩
          · exact absurd hadj (hCnone x hxf m y hyC)
        · rintro (⟨h, -⟩ | ⟨rfl, rfl⟩)
          · exact absurd h hxna'
          · exact hfb
      · have hxe : x = a' := by simpa using hxa
        subst x
        constructor
        · intro hadj
          rcases cross hH htm (Or.inl (Or.inl ha')) hyS hadj with hh | hh
          · exact Or.inl ⟨rfl, rung_eq_A hH hR hy hh.2⟩
          · exact absurd ha' (Set.disjoint_left.mp (hH.2.1 t t) · hh.1)
        · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
          · exact complete_A hH htm a' ha' _ hR.1
          · exact absurd (h ▸ hfnf) ha'nf
    have := glue_even hG hP hR.2.2.1 hdisj hcross (by
      simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
      omega)
    simp only [List.length_append, List.length_reverse, List.length_cons,
      List.length_nil] at this
    rw [Nat.even_iff] at this
    rw [Nat.even_iff] at hRev
    rw [Nat.odd_iff] at hodd
    omega

end Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oCore
