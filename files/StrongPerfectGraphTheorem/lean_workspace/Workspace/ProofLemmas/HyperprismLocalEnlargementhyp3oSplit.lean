import Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oCore

/-!
# The odd block of claim (2) of 10.6 — `A'ᵢ` is complete to `A''ᵢ`

PAPER (10.6, odd case, printed p. 62):

> *"Let `1 ≤ i ≤ 3`; we claim that `A'ᵢ` is complete to `A''ᵢ`.  For we may assume that
> `i = 1`; suppose that `a' ∈ A'₁` and `a'' ∈ A''₁` are nonadjacent, and let `R''` be a
> `1`-rung with ends `a'', b''`.  Choose `a ∈ A''₂ ∪ A''₃` and `b ∈ B'₂ ∪ B'₃`; then `a, b`
> are not adjacent since all rungs have even length, and so
> `a-a'-f₁-⋯-fₙ-b-b''-R''-a''-a` is an odd hole, a contradiction.  This proves that `A'ᵢ`
> is complete to `A''ᵢ` for `i = 1, 2, 3`, and similarly `B'ᵢ` is complete to `B''ᵢ`."*
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oSplit

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.HyperprismSplit
open Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oCore

variable {V : Type*} {G : SimpleGraph V} {A B C P Q : Fin 3 → Set V}

/-- The two completeness statements of the displayed paragraph, in the odd block. -/
theorem oddSplitCompleteness (hG : Berge G) (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q)
    (hAsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (A j \ P j).Nonempty)
    (hBsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (B j \ Q j).Nonempty)
    (hPsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (P j).Nonempty)
    (hQsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (Q j).Nonempty)
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn) (hodd : Odd f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hAedges : ∀ (i : Fin 3), ∀ z ∈ f, ∀ a ∈ A i, G.Adj z a → z = f₁ ∧ a ∈ P i)
    (hBedges : ∀ (i : Fin 3), ∀ z ∈ f, ∀ b ∈ B i, G.Adj z b → z = fn ∧ b ∈ Q i)
    (hPadj : ∀ (i : Fin 3), ∀ a ∈ P i, G.Adj f₁ a)
    (hQadj : ∀ (i : Fin 3), ∀ b ∈ Q i, G.Adj fn b)
    (hCnone : ∀ z ∈ f, ∀ (m : Fin 3) (c : V), c ∈ C m → ¬ G.Adj z c) :
    (∀ i : Fin 3, Complete G (P i) (A i \ P i)) ∧
      (∀ i : Fin 3, Complete G (Q i) (B i \ Q i)) := by
  have hflen : 0 < f.length := PathBasics.path_length_pos hf.1
  have hf₁f : f₁ ∈ f := PathBasics.head_mem hf.2.1
  have hfnf : fn ∈ f := PathBasics.getLast_mem hf.2.2
  constructor
  · -- `A'ᵢ` is complete to `A''ᵢ`
    intro i a' ha' a'' ha''
    by_contra hnadj
    obtain ⟨R, b'', hR, hb''Q⟩ := exists_rung_dprime_of_notMem_P hH hs ha''.1 ha''.2
    obtain ⟨t, htne, a, ha⟩ := hAsupp i
    obtain ⟨s, hsne, b, hb⟩ := hQsupp i
    have ha'A : a' ∈ A i := hs.PA i ha'
    have hbB : b ∈ B s := hs.QB s hb
    have hb''B : b'' ∈ B i := hR.2.1
    have hf₁a' : G.Adj f₁ a' := hPadj i a' ha'
    have hfnb : G.Adj fn b := hQadj s b hb
    have ha'nf : a' ∉ f := fun h =>
      hfout a' h (mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inl ha'A)⟩)
    have hbnf : b ∉ f := fun h =>
      hfout b h (mem_hyperVerts_iff.mpr ⟨s, Or.inl (Or.inr hbB)⟩)
    have hanf : a ∉ f := fun h =>
      hfout a h (mem_hyperVerts_iff.mpr ⟨t, Or.inl (Or.inl ha.1)⟩)
    -- the interior of `R` lies in `C''ᵢ`
    have hint : ∀ y ∈ R, y ∈ C i → y ∈ Cpp G A B C P Q i := by
      intro y hy hyC
      refine ⟨R, a'', b'', hR, ha''.2, hb''Q, ?_⟩
      rw [PathBasics.mem_interior_iff_of_pathFrom hR.2.2.1]
      refine ⟨hy, ?_, ?_⟩
      · intro h
        exact Set.disjoint_left.mp (hH.2.2.1 i i) (h ▸ ha''.1) hyC
      · intro h
        exact Set.disjoint_left.mp (hH.2.2.2.1 i i) (h ▸ hb''B) hyC
    have hP₁ : IsPathFrom G (a' :: (f ++ [b])) a' b := by
      refine PathAttach.isPathFrom_cons_concat hf hf₁a'.symm hfnb.symm
        (no_edge_A_B_any hG hH ha'A hbB) ?_ ha'nf hbnf ?_ ?_
      · intro h
        exact Set.disjoint_left.mp (hH.2.1 i s) ha'A (h ▸ hbB)
      · intro x hx hxn hadj
        exact hxn ((hAedges i x hx a' ha'A hadj.symm).1)
      · intro x hx hxn hadj
        exact hxn ((hBedges s x hx b hbB hadj.symm).1)
    have hanR : a ∉ R := fun h =>
      notMem_S hH htne (Or.inl (Or.inl ha.1)) (rung_mem_S hR a h)
    have hQ₁ : IsPathFrom G (R.reverse ++ [a]) b'' a := by
      refine PathAttach.isPathFrom_concat (PathBasics.isPathFrom_reverse hR.2.2.1)
        (complete_A hH htne a ha.1 a'' hR.1) (by simpa using hanR) ?_
      intro x hx hxn hadj
      rw [List.mem_reverse] at hx
      rcases cross hH htne (Or.inl (Or.inl ha.1)) (rung_mem_S hR x hx) hadj with hh | hh
      · exact hxn (rung_eq_A hH hR hx hh.2)
      · exact Set.disjoint_left.mp (hH.2.1 t t) ha.1 hh.1
    have hdisj : ∀ x ∈ a' :: (f ++ [b]), x ∉ R.reverse ++ [a] := by
      intro x hx hmem
      rcases List.mem_append.mp hmem with hxR | hxa
      · rw [List.mem_reverse] at hxR
        rcases PathAttach.mem_cons_append_singleton.mp hx with rfl | hxf | rfl
        · exact ha''.2 (rung_eq_A hH hR hxR ha'A ▸ ha')
        · exact hfout x hxf (rung_subset_hyperVerts hR x hxR)
        · exact notMem_S hH hsne (Or.inl (Or.inr hbB)) (rung_mem_S hR x hxR)
      · have hxe : x = a := by simpa using hxa
        subst x
        rcases PathAttach.mem_cons_append_singleton.mp hx with rfl | hxf | rfl
        · exact Set.disjoint_left.mp (hH.2.2.2.2.1 i t (Ne.symm htne)) ha'A ha.1
        · exact hanf hxf
        · exact Set.disjoint_left.mp (hH.2.1 t s) ha.1 hbB
    have hcross : ∀ x ∈ a' :: (f ++ [b]), ∀ y ∈ R.reverse ++ [a],
        (G.Adj x y ↔ (x = b ∧ y = b'') ∨ (x = a' ∧ y = a)) := by
      intro x hx y hy
      have hycase : (y ∈ R ∧ y ≠ a) ∨ y = a := by
        rcases List.mem_append.mp hy with hyR | hya
        · rw [List.mem_reverse] at hyR
          exact Or.inl ⟨hyR, fun h => hanR (h ▸ hyR)⟩
        · exact Or.inr (by simpa using hya)
      rcases PathAttach.mem_cons_append_singleton.mp hx with rfl | hxf | rfl
      · -- `x = a'`
        rcases hycase with ⟨hyR, hyna⟩ | rfl
        · have hyS := rung_mem_S hR y hyR
          constructor
          · intro hadj
            exfalso
            rcases hyS with (hyA | hyB) | hyC
            · exact hnadj (rung_eq_A hH hR hyR hyA ▸ hadj)
            · exact no_edge_A_B_any hG hH ha'A hyB hadj
            · exact no_edge_prime_dprime hH hs i (Or.inl ha')
                (Or.inl (hint y hyR hyC)) hadj
          · rintro (⟨h, -⟩ | ⟨-, h⟩)
            · exact absurd (h ▸ ha'A) (fun hh =>
                Set.disjoint_left.mp (hH.2.1 i s) hh hbB)
            · exact absurd h hyna
        · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩,
            fun _ => (complete_A hH (Ne.symm htne) _ ha'A _ ha.1)⟩
      · -- `x ∈ f`
        rcases hycase with ⟨hyR, hyna⟩ | rfl
        · have hyS := rung_mem_S hR y hyR
          constructor
          · intro hadj
            exfalso
            rcases hyS with (hyA | hyB) | hyC
            · exact ha''.2 ((rung_eq_A hH hR hyR hyA) ▸ (hAedges i x hxf y hyA hadj).2)
            · exact hb''Q ((rung_eq_B hH hR hyR hyB) ▸ (hBedges i x hxf y hyB hadj).2)
            · exact hCnone x hxf i y hyC hadj
          · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
            · exact absurd hxf hbnf
            · exact absurd hxf ha'nf
        · constructor
          · intro hadj
            exact absurd ((hAedges t x hxf _ ha.1 hadj).2) ha.2
          · rintro (⟨-, h⟩ | ⟨rfl, -⟩)
            · exact absurd h.symm (fun hh =>
                Set.disjoint_left.mp (hH.2.1 t i) (hh ▸ ha.1) hb''B)
            · exact absurd hxf ha'nf
      · -- `x = b`
        rcases hycase with ⟨hyR, hyna⟩ | rfl
        · have hyS := rung_mem_S hR y hyR
          constructor
          · intro hadj
            rcases id hyS with (hyA | hyB) | hyC
            · exact absurd hadj (fun hh => no_edge_A_B_any hG hH hyA hbB hh.symm)
            · exact Or.inl ⟨rfl, rung_eq_B hH hR hyR hyB⟩
            · exfalso
              rcases cross hH hsne (Or.inl (Or.inr hbB)) hyS hadj with hh | hh
              · exact Set.disjoint_left.mp (hH.2.1 s s) hh.1 hbB
              · exact Set.disjoint_left.mp (hH.2.2.2.1 i i) hh.2 hyC
          · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
            · exact complete_B hH hsne _ hbB _ hb''B
            · exact absurd (h ▸ hbB) (fun hh =>
                Set.disjoint_left.mp (hH.2.1 i s) ha'A hh)
        · constructor
          · intro hadj
            exact absurd hadj (fun hh => no_edge_A_B_any hG hH ha.1 hbB hh.symm)
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · exact absurd h.symm (fun hh =>
                Set.disjoint_left.mp (hH.2.1 t i) (hh ▸ ha.1) hb''B)
            · exact absurd (h ▸ hbB) (fun hh =>
                Set.disjoint_left.mp (hH.2.1 i s) ha'A hh)
    have hRlen : R.length = pathLength R + 1 :=
      PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
    have hRev := rung_even hG hH hR
    have hR2 : 2 ≤ R.length := rung_two_le_length hH hR
    have := glue_even hG hP₁ hQ₁ hdisj hcross (by
      simp only [List.length_cons, List.length_append, List.length_reverse, List.length_nil]
      omega)
    simp only [List.length_cons, List.length_append, List.length_reverse,
      List.length_nil] at this
    rw [Nat.even_iff] at this
    rw [Nat.even_iff] at hRev
    rw [Nat.odd_iff] at hodd
    omega
  · -- `B'ᵢ` is complete to `B''ᵢ`
    intro i b' hb' b'' hb''
    by_contra hnadj
    obtain ⟨R, a'', hR, ha''P⟩ := exists_rung_dprime_of_notMem_Q hH hs hb''.1 hb''.2
    obtain ⟨t, htne, b, hb⟩ := hBsupp i
    obtain ⟨s, hsne, a, ha⟩ := hPsupp i
    have hb'B : b' ∈ B i := hs.QB i hb'
    have haA : a ∈ A s := hs.PA s ha
    have ha''A : a'' ∈ A i := hR.1
    have hfnb' : G.Adj fn b' := hQadj i b' hb'
    have hf₁a : G.Adj f₁ a := hPadj s a ha
    have hb'nf : b' ∉ f := fun h =>
      hfout b' h (mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inr hb'B)⟩)
    have hanf : a ∉ f := fun h =>
      hfout a h (mem_hyperVerts_iff.mpr ⟨s, Or.inl (Or.inl haA)⟩)
    have hbnf : b ∉ f := fun h =>
      hfout b h (mem_hyperVerts_iff.mpr ⟨t, Or.inl (Or.inr hb.1)⟩)
    have hint : ∀ y ∈ R, y ∈ C i → y ∈ Cpp G A B C P Q i := by
      intro y hy hyC
      refine ⟨R, a'', b'', hR, ha''P, hb''.2, ?_⟩
      rw [PathBasics.mem_interior_iff_of_pathFrom hR.2.2.1]
      refine ⟨hy, ?_, ?_⟩
      · intro h
        exact Set.disjoint_left.mp (hH.2.2.1 i i) (h ▸ ha''A) hyC
      · intro h
        exact Set.disjoint_left.mp (hH.2.2.2.1 i i) (h ▸ hb''.1) hyC
    have hfrev : IsPathFrom G f.reverse fn f₁ := PathBasics.isPathFrom_reverse hf
    have hP₁ : IsPathFrom G (b' :: (f.reverse ++ [a])) b' a := by
      refine PathAttach.isPathFrom_cons_concat hfrev hfnb'.symm hf₁a.symm ?_ ?_
        (by simpa using hb'nf) (by simpa using hanf) ?_ ?_
      · intro hadj
        exact no_edge_A_B_any hG hH haA hb'B hadj.symm
      · intro h
        exact Set.disjoint_left.mp (hH.2.1 s i) haA (h ▸ hb'B)
      · intro x hx hxn hadj
        rw [List.mem_reverse] at hx
        exact hxn ((hBedges i x hx b' hb'B hadj.symm).1)
      · intro x hx hxn hadj
        rw [List.mem_reverse] at hx
        exact hxn ((hAedges s x hx a haA hadj.symm).1)
    have hbnR : b ∉ R := fun h =>
      notMem_S hH htne (Or.inl (Or.inr hb.1)) (rung_mem_S hR b h)
    have hQ₁ : IsPathFrom G (R ++ [b]) a'' b := by
      refine PathAttach.isPathFrom_concat hR.2.2.1
        (complete_B hH htne b hb.1 b'' hb''.1) hbnR ?_
      intro x hx hxn hadj
      rcases cross hH htne (Or.inl (Or.inr hb.1)) (rung_mem_S hR x hx) hadj with hh | hh
      · exact Set.disjoint_left.mp (hH.2.1 t t) hh.1 hb.1
      · exact hxn (rung_eq_B hH hR hx hh.2)
    have hdisj : ∀ x ∈ b' :: (f.reverse ++ [a]), x ∉ R ++ [b] := by
      intro x hx hmem
      have hxcase : x = b' ∨ x ∈ f ∨ x = a := by
        rcases PathAttach.mem_cons_append_singleton.mp hx with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_reverse.mp h))
        · exact Or.inr (Or.inr h)
      rcases List.mem_append.mp hmem with hxR | hxb
      · rcases hxcase with rfl | hxf | rfl
        · exact hb''.2 (rung_eq_B hH hR hxR hb'B ▸ hb')
        · exact hfout x hxf (rung_subset_hyperVerts hR x hxR)
        · exact notMem_S hH hsne (Or.inl (Or.inl haA)) (rung_mem_S hR x hxR)
      · have hxe : x = b := by simpa using hxb
        subst x
        rcases hxcase with rfl | hxf | rfl
        · exact Set.disjoint_left.mp (hH.2.2.2.2.2.1 i t (Ne.symm htne)) hb'B hb.1
        · exact hbnf hxf
        · exact Set.disjoint_left.mp (hH.2.1 s t) haA hb.1
    have hcross : ∀ x ∈ b' :: (f.reverse ++ [a]), ∀ y ∈ R ++ [b],
        (G.Adj x y ↔ (x = a ∧ y = a'') ∨ (x = b' ∧ y = b)) := by
      intro x hx y hy
      have hycase : (y ∈ R ∧ y ≠ b) ∨ y = b := by
        rcases List.mem_append.mp hy with hyR | hyb
        · exact Or.inl ⟨hyR, fun h => hbnR (h ▸ hyR)⟩
        · exact Or.inr (by simpa using hyb)
      have hxcase : x = b' ∨ x ∈ f ∨ x = a := by
        rcases PathAttach.mem_cons_append_singleton.mp hx with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_reverse.mp h))
        · exact Or.inr (Or.inr h)
      rcases hxcase with rfl | hxf | rfl
      · -- `x = b'`
        rcases hycase with ⟨hyR, hynb⟩ | rfl
        · have hyS := rung_mem_S hR y hyR
          constructor
          · intro hadj
            exfalso
            rcases hyS with (hyA | hyB) | hyC
            · exact no_edge_A_B_any hG hH hyA hb'B hadj.symm
            · exact hnadj (rung_eq_B hH hR hyR hyB ▸ hadj)
            · exact no_edge_dprime_prime hH hs i (Or.inr (hint y hyR hyC))
                (Or.inr hb') hadj.symm
          · rintro (⟨h, -⟩ | ⟨-, h⟩)
            · exact absurd (h ▸ hb'B) (fun hh =>
                Set.disjoint_left.mp (hH.2.1 s i) haA hh)
            · exact absurd h hynb
        · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩,
            fun _ => complete_B hH (Ne.symm htne) _ hb'B _ hb.1⟩
      · -- `x ∈ f`
        rcases hycase with ⟨hyR, hynb⟩ | rfl
        · have hyS := rung_mem_S hR y hyR
          constructor
          · intro hadj
            exfalso
            rcases hyS with (hyA | hyB) | hyC
            · exact ha''P ((rung_eq_A hH hR hyR hyA) ▸ (hAedges i x hxf y hyA hadj).2)
            · exact hb''.2 ((rung_eq_B hH hR hyR hyB) ▸ (hBedges i x hxf y hyB hadj).2)
            · exact hCnone x hxf i y hyC hadj
          · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
            · exact absurd hxf hanf
            · exact absurd hxf hb'nf
        · constructor
          · intro hadj
            exact absurd ((hBedges t x hxf _ hb.1 hadj).2) hb.2
          · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
            · exact absurd hxf hanf
            · exact absurd hxf hb'nf
      · -- `x = a`
        rcases hycase with ⟨hyR, hynb⟩ | rfl
        · have hyS := rung_mem_S hR y hyR
          constructor
          · intro hadj
            rcases id hyS with (hyA | hyB) | hyC
            · exact Or.inl ⟨rfl, rung_eq_A hH hR hyR hyA⟩
            · exact absurd hadj (no_edge_A_B_any hG hH haA hyB)
            · exfalso
              rcases cross hH hsne (Or.inl (Or.inl haA)) hyS hadj with hh | hh
              · exact Set.disjoint_left.mp (hH.2.2.1 i i) hh.2 hyC
              · exact Set.disjoint_left.mp (hH.2.1 s s) haA hh.1
          · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
            · exact complete_A hH hsne _ haA _ ha''A
            · exact absurd (h ▸ haA) (fun hh =>
                Set.disjoint_left.mp (hH.2.1 s i) hh hb'B)
        · constructor
          · intro hadj
            exact absurd hadj (no_edge_A_B_any hG hH haA hb.1)
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · exact absurd h.symm (fun hh =>
                Set.disjoint_left.mp (hH.2.1 i t) (hh ▸ ha''A) hb.1)
            · exact absurd (h ▸ haA) (fun hh =>
                Set.disjoint_left.mp (hH.2.1 s i) hh hb'B)
    have hRlen : R.length = pathLength R + 1 :=
      PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
    have hRev := rung_even hG hH hR
    have hR2 : 2 ≤ R.length := rung_two_le_length hH hR
    have := glue_even hG hP₁ hQ₁ hdisj hcross (by
      simp only [List.length_cons, List.length_append, List.length_reverse, List.length_nil]
      omega)
    simp only [List.length_cons, List.length_append, List.length_reverse,
      List.length_nil] at this
    rw [Nat.even_iff] at this
    rw [Nat.even_iff] at hRev
    rw [Nat.odd_iff] at hodd
    omega

end Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oSplit
