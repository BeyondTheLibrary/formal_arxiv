import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm101Assembly
import Workspace.ProofLemmas.Thm101ClaimOne
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.Statements.S07.Thm_7_2

/-!
# 10.1, claim (3): `X₁ ⊆ A` and `X₂ ⊆ B` — the parity argument

PAPER (proof of 10.1, printed pp. 57–58):

> *"From (2), since both `X₁` and `X₂` are local, we may assume that either `X₁ ⊆ A` and
> `X₂ ⊆ B`, or `X₁ ⊆ V(R₂)` and `X₂ ⊆ V(R₁)`.  In either case `X₁ ∩ X₂ = ∅`, so none of
> `f₂, …, fₙ₋₁` has any neighbours in `V(K)`.  Therefore `X₁` is the set of neighbours of `fₙ`
> in `V(K)`, and `X₂` is the set of neighbours of `f₁` in `V(K)`."*
>
> **(3) If `X₁ ⊆ A` and `X₂ ⊆ B` then the theorem holds.**
>
> *"For then we may assume that `fₙ` is adjacent to `a₁` and `f₁` to `b₂`.  Suppose first that
> `n` has the same parity as the length of `R₁`.  Since `a₂-R₂-b₂-f₁-⋯-fₙ-a₂` is not an odd
> hole, it follows that `fₙ` is not adjacent to `a₂`, and similarly `f₁` is not adjacent to
> `b₁`.  Since `a₃-R₃-b₃-b₂-f₁-⋯-fₙ-a₁-a₃` is not an odd hole, either `fₙ` is adjacent to `a₃`
> or `f₁` to `b₃`, and not both, as we saw before.  But then statement 4 of the theorem holds.
> Now suppose that `n` has different parity from the length of `R₁`.  Since
> `a₁-a₂-R₂-b₂-f₁-⋯-fₙ-a₁` is not an odd hole, `fₙ` is adjacent to `a₂`, and similarly `f₁` to
> `b₁`.  If there are no more edges between `F` and `V(K)` then statement 3 of the theorem
> holds, so we may assume that `fₙ` is adjacent to `a₃`.  By the same argument as before it
> follows that `f₁` is adjacent to `b₃`, and then statement 2 of the theorem holds.  This proves
> (3)."*

This is the only one of the five carve-outs whose argument is a parity/hole argument rather
than an application of 2.4: each of the four displayed cycles is closed into a hole by
`Workspace.ProofLemmas.PrismBasics.isHoleList_of_path_add_vertex` /
`isHoleList_of_path_add_two_vertices`, and `hG : Berge G` forbids it being odd.  The paper's
*"we may assume that `fₙ` is adjacent to `a₁` and `f₁` to `b₂`"* is the relabelling handled by
`Thm101Assembly.concl_perm`; it is legitimate precisely because `hFloc` forces `X₁` and `X₂` to
be nonempty and to sit over two *different* indices.

**Call site**: the proof of `Workspace.Statements.S10.SPGT.thm_10_1`, the `n ≥ 2` branch, first
of the two surviving cases left by claim (2).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm101ClaimThree

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem fin3_cases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

private theorem perm_of_three : ∀ i j m : Fin 3, i ≠ j → i ≠ m → j ≠ m →
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j ∧ σ 2 = m := by decide

private theorem fin3_third : ∀ i j : Fin 3, i ≠ j →
    ∃ m : Fin 3, m ≠ i ∧ m ≠ j := by decide

private theorem mem_aTriple_on_path_eq {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (i : Fin 3) {x : V} (hxA : x ∈ ({a 0, a 1, a 2} : Set V)) (hxi : x ∈ R i) :
    x = a i := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxA
  rcases hxA with rfl | rfl | rfl
  · exact congrArg a (Thm101ClaimOne.tri_own_path hprism i 0 hxi)
  · exact congrArg a (Thm101ClaimOne.tri_own_path hprism i 1 hxi)
  · exact congrArg a (Thm101ClaimOne.tri_own_path hprism i 2 hxi)

private theorem mem_bTriple_on_path_eq {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (i : Fin 3) {x : V} (hxB : x ∈ ({b 0, b 1, b 2} : Set V)) (hxi : x ∈ R i) :
    x = b i := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxB
  rcases hxB with rfl | rfl | rfl
  · exact congrArg b (Thm101ClaimOne.tri_own_path' hprism i 0 hxi)
  · exact congrArg b (Thm101ClaimOne.tri_own_path' hprism i 1 hxi)
  · exact congrArg b (Thm101ClaimOne.tri_own_path' hprism i 2 hxi)

/-- Removing the first vertex of an induced path leaves a path beginning at its unique
neighbour of the old first vertex.  This is the small list fact used twice in the parity
cycles below. -/
private theorem drop_one_data {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (hlen : 2 ≤ p.length) :
    IsPathFrom G (p.drop 1) (p[1]'(by omega)) v ∧
      u ∉ p.drop 1 ∧
      ∀ x ∈ p.drop 1, (G.Adj x u ↔ x = p[1]'(by omega)) := by
  have h0 : p[0]'(by omega) = u :=
    PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
  have hnd : p.Nodup := PathBasics.path_nodup hp.1
  refine ⟨Thm101ClaimOne.drop_pathFrom hp (by omega), ?_, ?_⟩
  · intro hu
    obtain ⟨s, hs, heq⟩ := Thm101ClaimOne.mem_drop_iff.mp hu
    have helem : p[1 + s]'hs = p[0]'(by omega) := heq.trans h0.symm
    have hi := hnd.getElem_inj_iff.mp helem
    omega
  · intro x hx
    obtain ⟨s, hs, heq⟩ := Thm101ClaimOne.mem_drop_iff.mp hx
    constructor
    · intro hadj
      have hadj' : G.Adj (p[1 + s]'hs) (p[0]'(by omega)) := by
        rw [heq, h0]
        exact hadj
      have hi := (PathBasics.path_adj_iff hp.1 hs (by omega)).mp hadj'
      have hs0 : s = 0 := by omega
      subst s
      simpa using heq.symm
    · intro hx1
      have hadj : G.Adj (p[1]'(by omega)) (p[0]'(by omega)) :=
        (PathBasics.path_adj_iff hp.1 (by omega) (by omega)).mpr (Or.inr rfl)
      rw [hx1, ← h0]
      exact hadj

/-- The parity argument after relabelling the two known endpoint attachments to
`fn-a 0` and `f₁-b 1`. -/
private theorem claim_three_core (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length)
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({a 0, a 1, a 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ ({b 0, b 1, b 2} : Set V))
    (hfn0 : G.Adj fn (a 0)) (hf₁b1 : G.Adj f₁ (b 1)) :
    Thm101Assembly.Concl G a b R K f f₁ fn ∨
      Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  classical
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ :=
    PrismSymmetry.formPrism_family.mp hprism
  have hlen : ∀ i : Fin 3, 2 ≤ (R i).length := Thm101ClaimOne.two_le_length hprism
  have hfne : f₁ ≠ fn :=
    PathBasics.isPathFrom_ends_ne hf (by change 1 ≤ f.length - 1; omega)
  have hf₁F : f₁ ∈ F := by rw [hfF]; exact PathBasics.head_mem hf.2.1
  have hfnF : fn ∈ F := by rw [hfF]; exact PathBasics.getLast_mem hf.2.2
  have hRK : ∀ i : Fin 3, ∀ x : V, x ∈ R i → x ∈ K := by
    intro i x hx
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i := by
    intro x hx i hxi
    exact (hFK (by rw [hfF]; exact hx)) (hRK i x hxi)
  have hmemA : ∀ i : Fin 3, a i ∈ R i :=
    fun i => PathBasics.head_mem (hp i).2.1
  have hmemB : ∀ i : Fin 3, b i ∈ R i :=
    fun i => PathBasics.getLast_mem (hp i).2.2
  have hAcross : ∀ i j : Fin 3, i ≠ j → ¬ G.Adj (a i) (b j) := by
    intro i j hij hadj
    rcases (hedge i j hij (a i) (hmemA i) (b j) (hmemB j)).mp hadj with h | h
    · exact hABne j j h.2.symm
    · exact hABne i i h.1
  have hcrossOnly : ∀ i : Fin 3, ∀ r ∈ R i, ∀ x ∈ f, G.Adj r x →
      (r = a i ∧ x = fn) ∨ (r = b i ∧ x = f₁) := by
    intro i r hr x hx hadj
    have hxF : x ∈ F := by rw [hfF]; exact hx
    by_cases hx1 : x = f₁
    · subst x
      have hrB : r ∈ ({b 0, b 1, b 2} : Set V) :=
        hX2 ⟨hRK i r hr, f₁, ⟨hf₁F, by simp [hfne]⟩, hadj⟩
      exact Or.inr ⟨mem_bTriple_on_path_eq hprism i hrB hr, rfl⟩
    · have hrA : r ∈ ({a 0, a 1, a 2} : Set V) :=
        hX1 ⟨hRK i r hr, x, ⟨hxF, by simpa using hx1⟩, hadj⟩
      have hra : r = a i := mem_aTriple_on_path_eq hprism i hrA hr
      refine Or.inl ⟨hra, ?_⟩
      by_contra hxn
      have hrB : r ∈ ({b 0, b 1, b 2} : Set V) :=
        hX2 ⟨hRK i r hr, x, ⟨hxF, by simpa using hxn⟩, hadj⟩
      have hrb : r = b i := mem_bTriple_on_path_eq hprism i hrB hr
      exact hABne i i (hra.symm.trans hrb)
  have haOnly : ∀ i : Fin 3, ∀ x ∈ f, G.Adj (a i) x → x = fn := by
    intro i x hx hadj
    rcases hcrossOnly i (a i) (hmemA i) x hx hadj with h | h
    · exact h.2
    · exact False.elim (hABne i i h.1)
  have hbOnly : ∀ i : Fin 3, ∀ x ∈ f, G.Adj (b i) x → x = f₁ := by
    intro i x hx hadj
    rcases hcrossOnly i (b i) (hmemB i) x hx hadj with h | h
    · exact False.elim (hABne i i h.1.symm)
    · exact h.2
  have hdirect : ∀ i : Fin 3, G.Adj fn (a i) → G.Adj f₁ (b i) →
      Even ((R i).length + f.length) := by
    intro i hfna hfb
    have hhole : IsHoleList G (R i ++ f) := by
      refine PathGlue.glue_hole (hp i) hf ?_ ?_ (by have := hlen i; omega)
      · intro r hr hrf
        exact hfK r hrf i hr
      · intro r hr x hx
        constructor
        · intro hadj
          rcases hcrossOnly i r hr x hx hadj with h | h
          · exact Or.inr h
          · exact Or.inl h
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hfb.symm
          · exact hfna.symm
    simpa only [holeLength, List.length_append] using hG.1 _ hhole
  have hlongA : ∀ i j : Fin 3, i ≠ j → G.Adj fn (a i) → G.Adj f₁ (b j) →
      ¬ G.Adj fn (a j) → Even ((R j).length + f.length + 1) := by
    intro i j hij hfni hfbj hnot
    have hpath : IsPathFrom G (R j ++ f) (a j) fn := by
      refine PathGlue.glue_path (hp j) hf ?_ ?_
      · intro r hr hrf
        exact hfK r hrf j hr
      · intro r hr x hx
        constructor
        · intro hadj
          rcases hcrossOnly j r hr x hx hadj with h | h
          · exact False.elim (hnot (by rw [h.1, h.2] at hadj; exact hadj.symm))
          · exact h
        · rintro ⟨rfl, rfl⟩
          exact hfbj.symm
    have hai : a i ∉ R j ++ f := by
      intro hm
      rcases List.mem_append.mp hm with hr | hfmem
      · exact hij (Thm101ClaimOne.tri_own_path hprism j i hr)
      · exact hfK (a i) hfmem i (hmemA i)
    have hint : ∀ x ∈ interior (R j ++ f), ¬ G.Adj (a i) x := by
      intro x hxint hadj
      have hx := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hxint
      rcases List.mem_append.mp hx.1 with hxR | hxf
      · rcases (hedge i j hij (a i) (hmemA i) x hxR).mp hadj with h | h
        · exact hx.2.1 h.2
        · exact hABne i i h.1
      · exact hx.2.2 (haOnly i x hxf hadj)
    have hhole : IsHoleList G (a i :: (R j ++ f)) :=
      PrismBasics.isHoleList_of_path_add_vertex hpath
        (by
          have hj := hlen j
          have hff := hn
          rw [PathBasics.pathLength_eq, List.length_append]
          omega)
        (hAtri i j hij) hfni.symm hai hint
    simpa only [holeLength, List.length_cons, List.length_append, Nat.add_assoc] using
      hG.1 _ hhole
  have hlongB : ∀ i j : Fin 3, i ≠ j → G.Adj fn (a i) → G.Adj f₁ (b j) →
      ¬ G.Adj f₁ (b i) → Even ((R i).length + f.length + 1) := by
    intro i j hij hfni hfbj hnot
    have hpath : IsPathFrom G (f ++ R i) f₁ (b i) := by
      refine PathGlue.glue_path hf (hp i) ?_ ?_
      · intro x hx hxi
        exact hfK x hx i hxi
      · intro x hx r hr
        constructor
        · intro hadj
          rcases hcrossOnly i r hr x hx hadj.symm with h | h
          · exact h.symm
          · exact False.elim (hnot (by rw [h.1, h.2] at hadj; exact hadj))
        · rintro ⟨rfl, rfl⟩
          exact hfni
    have hbj : b j ∉ f ++ R i := by
      intro hm
      rcases List.mem_append.mp hm with hfmem | hr
      · exact hfK (b j) hfmem j (hmemB j)
      · exact (Ne.symm hij) (Thm101ClaimOne.tri_own_path' hprism i j hr)
    have hint : ∀ x ∈ interior (f ++ R i), ¬ G.Adj (b j) x := by
      intro x hxint hadj
      have hx := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hxint
      rcases List.mem_append.mp hx.1 with hxf | hxR
      · exact hx.2.1 (hbOnly j x hxf hadj)
      · rcases (hedge i j hij x hxR (b j) (hmemB j)).mp hadj.symm with h | h
        · exact hABne j j h.2.symm
        · exact hx.2.2 h.1
    have hhole : IsHoleList G (b j :: (f ++ R i)) :=
      PrismBasics.isHoleList_of_path_add_vertex hpath
        (by
          have hi := hlen i
          have hff := hn
          rw [PathBasics.pathLength_eq, List.length_append]
          omega)
        hfbj.symm (hBtri j i (Ne.symm hij)) hbj hint
    have hev := hG.1 _ hhole
    simpa only [holeLength, List.length_cons, List.length_append, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hev
  have hnoneThird : ¬ G.Adj fn (a 2) → ¬ G.Adj f₁ (b 2) →
      Even ((R 2).length + f.length + 2) := by
    intro hfn2 hfb2
    have hq : IsPathFrom G (b 1 :: f) (b 1) fn := by
      refine PathAttach.isPathFrom_cons hf hf₁b1.symm ?_ ?_
      · intro hbmem
        exact hfK (b 1) hbmem 1 (hmemB 1)
      · intro x hx hxne hadj
        exact hxne (hbOnly 1 x hx hadj)
    have hpath : IsPathFrom G (R 2 ++ (b 1 :: f)) (a 2) fn := by
      refine PathGlue.glue_path (hp 2) hq ?_ ?_
      · intro r hr hrq
        rcases List.mem_cons.mp hrq with hrb | hrf
        · subst r
          exact Thm101ClaimOne.paths_disjoint hprism (by decide : (2 : Fin 3) ≠ 1)
            hr (hmemB 1)
        · exact hfK r hrf 2 hr
      · intro r hr y hy
        constructor
        · intro hadj
          rcases List.mem_cons.mp hy with hyb | hyf
          · subst y
            rcases (hedge 2 1 (by decide) r hr (b 1) (hmemB 1)).mp hadj with h | h
            · exact False.elim (hABne 1 1 h.2.symm)
            · exact ⟨h.1, rfl⟩
          · rcases hcrossOnly 2 r hr y hyf hadj with h | h
            · exact False.elim (hfn2 (by rw [h.1, h.2] at hadj; exact hadj.symm))
            · exact False.elim (hfb2 (by rw [h.1, h.2] at hadj; exact hadj.symm))
        · rintro ⟨rfl, rfl⟩
          exact hBtri 2 1 (by decide)
    have ha0not : a 0 ∉ R 2 ++ (b 1 :: f) := by
      intro hm
      rcases List.mem_append.mp hm with hr | hqmem
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (Thm101ClaimOne.tri_own_path hprism 2 0 hr)
      · rcases List.mem_cons.mp hqmem with hab | hfm
        · exact hABne 0 1 hab
        · exact hfK (a 0) hfm 0 (hmemA 0)
    have hint : ∀ x ∈ interior (R 2 ++ (b 1 :: f)), ¬ G.Adj (a 0) x := by
      intro x hxint hadj
      have hx := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hxint
      rcases List.mem_append.mp hx.1 with hxR | hxq
      · rcases (hedge 0 2 (by decide) (a 0) (hmemA 0) x hxR).mp hadj with h | h
        · exact hx.2.1 h.2
        · exact hABne 0 0 h.1
      · rcases List.mem_cons.mp hxq with hxb | hxf
        · subst x
          exact hAcross 0 1 (by decide) hadj
        · exact hx.2.2 (haOnly 0 x hxf hadj)
    have hhole : IsHoleList G (a 0 :: (R 2 ++ (b 1 :: f))) :=
      PrismBasics.isHoleList_of_path_add_vertex hpath
        (by
          have hr := hlen 2
          have hff := hn
          rw [PathBasics.pathLength_eq, List.length_append, List.length_cons]
          omega)
        (hAtri 0 2 (by decide)) hfn0.symm ha0not hint
    simpa only [holeLength, List.length_cons, List.length_append, Nat.add_assoc] using
      hG.1 _ hhole
  have hforceB : G.Adj fn (a 2) → ¬ G.Adj f₁ (b 2) →
      Even ((R 2).length + f.length + 1) := by
    intro hfn2 hfb2
    obtain ⟨hP, ha2P, hPfirst⟩ := drop_one_data (hp 2) (hlen 2)
    let d : V := (R 2)[1]'(by have := hlen 2; omega)
    have hdP : d ∈ (R 2).drop 1 := by
      apply Thm101ClaimOne.mem_drop_iff.mpr
      exact ⟨0, by have := hlen 2; omega, rfl⟩
    have hQ : IsPathFrom G (b 1 :: (f ++ [a 2])) (b 1) (a 2) := by
      refine PathAttach.isPathFrom_cons_concat hf hf₁b1.symm hfn2.symm ?_ ?_ ?_ ?_ ?_ ?_
      · intro hadj
        exact hAcross 2 1 (by decide) hadj.symm
      · exact (hABne 2 1).symm
      · intro hbmem
        exact hfK (b 1) hbmem 1 (hmemB 1)
      · intro hamem
        exact hfK (a 2) hamem 2 (hmemA 2)
      · intro x hx hxne hadj
        exact hxne (hbOnly 1 x hx hadj)
      · intro x hx hxne hadj
        exact hxne (haOnly 2 x hx hadj)
    have hdisj : ∀ x ∈ (R 2).drop 1, x ∉ b 1 :: (f ++ [a 2]) := by
      intro x hxP hxQ
      have hxR : x ∈ R 2 := List.mem_of_mem_drop hxP
      rcases (PathAttach.mem_cons_append_singleton.mp hxQ) with hxb | hxf | hxa
      · subst x
        exact Thm101ClaimOne.paths_disjoint hprism (by decide : (2 : Fin 3) ≠ 1)
          hxR (hmemB 1)
      · exact hfK x hxf 2 hxR
      · subst x
        exact ha2P hxP
    have hcross : ∀ x ∈ (R 2).drop 1, ∀ y ∈ b 1 :: (f ++ [a 2]),
        (G.Adj x y ↔
          (x = b 2 ∧ y = b 1) ∨ (x = d ∧ y = a 2)) := by
      intro x hxP y hyQ
      have hxR : x ∈ R 2 := List.mem_of_mem_drop hxP
      constructor
      · intro hadj
        rcases (PathAttach.mem_cons_append_singleton.mp hyQ) with hyb | hyf | hya
        · subst y
          rcases (hedge 2 1 (by decide) x hxR (b 1) (hmemB 1)).mp hadj with h | h
          · exact False.elim (hABne 1 1 h.2.symm)
          · exact Or.inl ⟨h.1, rfl⟩
        · rcases hcrossOnly 2 x hxR y hyf hadj with h | h
          · exact False.elim (ha2P (h.1 ▸ hxP))
          · exact False.elim (hfb2 (by rw [h.1, h.2] at hadj; exact hadj.symm))
        · subst y
          exact Or.inr ⟨(hPfirst x hxP).mp hadj, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hBtri 2 1 (by decide)
        · exact (hPfirst d hdP).mpr rfl
    have hhole : IsHoleList G ((R 2).drop 1 ++ (b 1 :: (f ++ [a 2]))) :=
      PathGlue.glue_hole hP hQ hdisj hcross (by
        have hr := hlen 2
        have hff := hn
        simp only [List.length_drop, List.length_cons, List.length_append, List.length_nil,
          Nat.add_zero]
        omega)
    have hev := hG.1 _ hhole
    have heq : ((R 2).drop 1).length + (b 1 :: (f ++ [a 2])).length =
        (R 2).length + f.length + 1 := by
      have hr := hlen 2
      simp only [List.length_drop, List.length_cons, List.length_append, List.length_nil,
        Nat.add_zero]
      omega
    rw [holeLength, List.length_append, heq] at hev
    exact hev
  have hforceA : G.Adj f₁ (b 2) → ¬ G.Adj fn (a 2) →
      Even ((R 2).length + f.length + 1) := by
    intro hfb2 hfn2
    have hpR : IsPathFrom G (R 2).reverse (b 2) (a 2) :=
      PathBasics.isPathFrom_reverse (hp 2)
    have hlenR : 2 ≤ (R 2).reverse.length := by simpa using hlen 2
    obtain ⟨hP, hb2P, hPfirst⟩ := drop_one_data hpR hlenR
    let d : V := (R 2).reverse[1]'(by omega)
    have hdP : d ∈ (R 2).reverse.drop 1 := by
      apply Thm101ClaimOne.mem_drop_iff.mpr
      exact ⟨0, by omega, rfl⟩
    have hQ : IsPathFrom G (a 0 :: (f.reverse ++ [b 2])) (a 0) (b 2) := by
      refine PathAttach.isPathFrom_cons_concat (PathBasics.isPathFrom_reverse hf)
        hfn0.symm hfb2.symm (hAcross 0 2 (by decide)) (hABne 0 2) ?_ ?_ ?_ ?_
      · intro hamem
        exact hfK (a 0) (List.mem_reverse.mp hamem) 0 (hmemA 0)
      · intro hbmem
        exact hfK (b 2) (List.mem_reverse.mp hbmem) 2 (hmemB 2)
      · intro x hx hxne hadj
        exact hxne (haOnly 0 x (List.mem_reverse.mp hx) hadj)
      · intro x hx hxne hadj
        exact hxne (hbOnly 2 x (List.mem_reverse.mp hx) hadj)
    have hdisj : ∀ x ∈ (R 2).reverse.drop 1, x ∉ a 0 :: (f.reverse ++ [b 2]) := by
      intro x hxP hxQ
      have hxR : x ∈ R 2 := List.mem_reverse.mp (List.mem_of_mem_drop hxP)
      rcases (PathAttach.mem_cons_append_singleton.mp hxQ) with hxa | hxf | hxb
      · subst x
        exact (by decide : (0 : Fin 3) ≠ 2)
          (Thm101ClaimOne.tri_own_path hprism 2 0 hxR)
      · exact hfK x (List.mem_reverse.mp hxf) 2 hxR
      · subst x
        exact hb2P hxP
    have hcross : ∀ x ∈ (R 2).reverse.drop 1, ∀ y ∈ a 0 :: (f.reverse ++ [b 2]),
        (G.Adj x y ↔ (x = a 2 ∧ y = a 0) ∨ (x = d ∧ y = b 2)) := by
      intro x hxP y hyQ
      have hxR : x ∈ R 2 := List.mem_reverse.mp (List.mem_of_mem_drop hxP)
      constructor
      · intro hadj
        rcases (PathAttach.mem_cons_append_singleton.mp hyQ) with hya | hyf | hyb
        · subst y
          rcases (hedge 2 0 (by decide) x hxR (a 0) (hmemA 0)).mp hadj with h | h
          · exact Or.inl ⟨h.1, rfl⟩
          · exact False.elim (hABne 0 0 h.2)
        · have hyf' : y ∈ f := List.mem_reverse.mp hyf
          rcases hcrossOnly 2 x hxR y hyf' hadj with h | h
          · exact False.elim (hfn2 (by rw [h.1, h.2] at hadj; exact hadj.symm))
          · exact False.elim (hb2P (by
              have : b 2 ∈ (R 2).reverse.drop 1 := h.1 ▸ hxP
              exact this))
        · subst y
          exact Or.inr ⟨(hPfirst x hxP).mp hadj, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hAtri 2 0 (by decide)
        · exact (hPfirst d hdP).mpr rfl
    have hhole : IsHoleList G ((R 2).reverse.drop 1 ++ (a 0 :: (f.reverse ++ [b 2]))) :=
      PathGlue.glue_hole hP hQ hdisj hcross (by
        have hr := hlen 2
        have hff := hn
        simp only [List.length_drop, List.length_reverse, List.length_cons,
          List.length_append, List.length_nil, Nat.add_zero]
        omega)
    have hev := hG.1 _ hhole
    have heq : ((R 2).reverse.drop 1).length + (a 0 :: (f.reverse ++ [b 2])).length =
        (R 2).length + f.length + 1 := by
      have hr := hlen 2
      simp only [List.length_drop, List.length_reverse, List.length_cons,
        List.length_append, List.length_nil, Nat.add_zero]
      omega
    rw [holeLength, List.length_append, heq] at hev
    exact hev
  have hAindex : ∀ x : V, x ∈ ({a 0, a 1, a 2} : Set V) →
      ∃ i : Fin 3, x = a i := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hBindex : ∀ x : V, x ∈ ({b 0, b 1, b 2} : Set V) →
      ∃ i : Fin 3, x = b i := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hABdisj : ∀ x : V, x ∈ ({a 0, a 1, a 2} : Set V) →
      x ∈ ({b 0, b 1, b 2} : Set V) → False := by
    intro x hxA hxB
    obtain ⟨i, hi⟩ := hAindex x hxA
    obtain ⟨j, hj⟩ := hBindex x hxB
    exact hABne i j (hi.symm.trans hj)
  have hEdge : ∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
      (x = f₁ ∧ ∃ i : Fin 3, k = b i) ∨ (x = fn ∧ ∃ i : Fin 3, k = a i) := by
    intro x hx k hk hadj
    have hxF : x ∈ F := by rw [hfF]; exact hx
    by_cases hx1 : x = f₁
    · left
      subst x
      have hkB : k ∈ ({b 0, b 1, b 2} : Set V) :=
        hX2 ⟨hk, f₁, ⟨hf₁F, by simp [hfne]⟩, hadj.symm⟩
      exact ⟨rfl, hBindex k hkB⟩
    · have hkA : k ∈ ({a 0, a 1, a 2} : Set V) :=
        hX1 ⟨hk, x, ⟨hxF, by simpa using hx1⟩, hadj.symm⟩
      right
      refine ⟨?_, hAindex k hkA⟩
      by_contra hxn
      have hkB : k ∈ ({b 0, b 1, b 2} : Set V) :=
        hX2 ⟨hk, x, ⟨hxF, by simpa using hxn⟩, hadj.symm⟩
      exact hABdisj k hkA hkB
  have concl2 (hfn1 : G.Adj fn (a 1)) (hfn2 : G.Adj fn (a 2))
      (hfb0 : G.Adj f₁ (b 0)) (hfb2 : G.Adj f₁ (b 2)) :
      Thm101Assembly.Concl G a b R K f f₁ fn := by
    refine ⟨b, a, R, Equiv.refl (Fin 3), rfl, Or.inr ⟨rfl, rfl⟩,
      Or.inr (Or.inl ⟨hn, ?_, ?_, ?_⟩)⟩
    · intro i
      rcases fin3_cases i with rfl | rfl | rfl
      exacts [hfb0, hf₁b1, hfb2]
    · intro i
      rcases fin3_cases i with rfl | rfl | rfl
      exacts [hfn0, hfn1, hfn2]
    · exact hEdge
  have concl3 (hfn1 : G.Adj fn (a 1)) (hfb0 : G.Adj f₁ (b 0))
      (hfn2 : ¬ G.Adj fn (a 2)) (hfb2 : ¬ G.Adj f₁ (b 2)) :
      Thm101Assembly.Concl G a b R K f f₁ fn := by
    refine ⟨b, a, R, Equiv.refl (Fin 3), rfl, Or.inr ⟨rfl, rfl⟩,
      Or.inr (Or.inr (Or.inl ⟨hn, hfb0, hf₁b1, hfn0, hfn1, ?_⟩))⟩
    intro x hx k hk hadj
    rcases hEdge x hx k hk hadj with ⟨hx1, i, hi⟩ | ⟨hxn, i, hi⟩
    · left
      refine ⟨hx1, ?_⟩
      rcases fin3_cases i with rfl | rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
      · exact False.elim (hfb2 (by rw [hx1, hi] at hadj; exact hadj))
    · right
      refine ⟨hxn, ?_⟩
      rcases fin3_cases i with rfl | rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
      · exact False.elim (hfn2 (by rw [hxn, hi] at hadj; exact hadj))
  have concl4fn (hfn2 : G.Adj fn (a 2))
      (hfb0 : ¬ G.Adj f₁ (b 0)) (hfb2 : ¬ G.Adj f₁ (b 2)) :
      Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
    obtain ⟨σ, hσ0, hσ1, hσ2⟩ :=
      perm_of_three (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)
        (by decide) (by decide) (by decide)
    refine ⟨fun i => a (σ i), fun i => b (σ i), fun i => R (σ i), σ,
      rfl, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩))⟩
    · simpa only [hσ0] using hfn0
    · simpa only [hσ1] using hfn2
    · refine ⟨b 1, by simpa only [hσ2] using hmemB 1, ?_, hf₁b1⟩
      simpa only [hσ2] using (hABne 1 1).symm
    · intro x hx k hk hkne hadj
      have hxf : x ∈ f := List.mem_reverse.mp hx
      rcases hEdge x hxf k hk hadj with ⟨hx1, i, hi⟩ | ⟨hxn, i, hi⟩
      · right
        refine ⟨hx1, ?_⟩
        rcases fin3_cases i with rfl | rfl | rfl
        · exact False.elim (hfb0 (by rw [hx1, hi] at hadj; exact hadj))
        · simpa only [hσ2, hi] using hmemB 1
        · exact False.elim (hfb2 (by rw [hx1, hi] at hadj; exact hadj))
      · left
        refine ⟨hxn, ?_⟩
        rcases fin3_cases i with rfl | rfl | rfl
        · exact Or.inl (by simpa only [hσ0] using hi)
        · exact False.elim (hkne (by simpa only [hσ2] using hi))
        · exact Or.inr (by simpa only [hσ1] using hi)
  have concl4f (hfb2 : G.Adj f₁ (b 2))
      (hfn1 : ¬ G.Adj fn (a 1)) (hfn2 : ¬ G.Adj fn (a 2)) :
      Thm101Assembly.Concl G a b R K f f₁ fn := by
    obtain ⟨σ, hσ0, hσ1, hσ2⟩ :=
      perm_of_three (1 : Fin 3) (2 : Fin 3) (0 : Fin 3)
        (by decide) (by decide) (by decide)
    refine ⟨fun i => b (σ i), fun i => a (σ i), fun i => R (σ i), σ,
      rfl, Or.inr ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩))⟩
    · simpa only [hσ0] using hf₁b1
    · simpa only [hσ1] using hfb2
    · refine ⟨a 0, by simpa only [hσ2] using hmemA 0, ?_, hfn0⟩
      simpa only [hσ2] using hABne 0 0
    · intro x hx k hk hkne hadj
      rcases hEdge x hx k hk hadj with ⟨hx1, i, hi⟩ | ⟨hxn, i, hi⟩
      · left
        refine ⟨hx1, ?_⟩
        rcases fin3_cases i with rfl | rfl | rfl
        · exact False.elim (hkne (by simpa only [hσ2] using hi))
        · exact Or.inl (by simpa only [hσ0] using hi)
        · exact Or.inr (by simpa only [hσ1] using hi)
      · right
        refine ⟨hxn, ?_⟩
        rcases fin3_cases i with rfl | rfl | rfl
        · simpa only [hσ2, hi] using hmemA 0
        · exact False.elim (hfn1 (by rw [hxn, hi] at hadj; exact hadj))
        · exact False.elim (hfn2 (by rw [hxn, hi] at hadj; exact hadj))
  have h72 := Workspace.Statements.S07.SPGT.thm_7_2 G hG a b (R 0) (R 1) (R 2) hprism
  have hlen01 : Even (R 0).length ↔ Even (R 1).length := by
    rw [PathBasics.length_eq_pathLength_add_one (hp 0).1,
      PathBasics.length_eq_pathLength_add_one (hp 1).1,
      Nat.even_add_one, Nat.even_add_one]
    exact not_congr h72.1
  have hlen02 : Even (R 0).length ↔ Even (R 2).length := by
    rw [PathBasics.length_eq_pathLength_add_one (hp 0).1,
      PathBasics.length_eq_pathLength_add_one (hp 2).1,
      Nat.even_add_one, Nat.even_add_one]
    exact not_congr h72.2
  have htotal : ∀ i : Fin 3,
      Even ((R i).length + f.length) ↔ Even ((R 0).length + f.length) := by
    intro i
    rcases fin3_cases i with rfl | rfl | rfl
    · rfl
    · rw [Nat.even_add, Nat.even_add]
      constructor
      · intro h
        exact ⟨fun h0 => h.mp (hlen01.mp h0), fun hf' => hlen01.mpr (h.mpr hf')⟩
      · intro h
        exact ⟨fun h1 => h.mp (hlen01.mpr h1), fun hf' => hlen01.mp (h.mpr hf')⟩
    · rw [Nat.even_add, Nat.even_add]
      constructor
      · intro h
        exact ⟨fun h0 => h.mp (hlen02.mp h0), fun hf' => hlen02.mpr (h.mpr hf')⟩
      · intro h
        exact ⟨fun h2 => h.mp (hlen02.mpr h2), fun hf' => hlen02.mp (h.mpr hf')⟩
  by_cases heven : Even ((R 0).length + f.length)
  · have hfn1 : G.Adj fn (a 1) := by
      by_contra hnot
      have hh := hlongA 0 1 (by decide) hfn0 hf₁b1 hnot
      exact (Nat.even_add_one.mp hh) ((htotal 1).mpr heven)
    have hfb0 : G.Adj f₁ (b 0) := by
      by_contra hnot
      have hh := hlongB 0 1 (by decide) hfn0 hf₁b1 hnot
      exact (Nat.even_add_one.mp hh) heven
    by_cases hfn2 : G.Adj fn (a 2)
    · have hfb2 : G.Adj f₁ (b 2) := by
        by_contra hnot
        have hh := hforceB hfn2 hnot
        exact (Nat.even_add_one.mp hh) ((htotal 2).mpr heven)
      exact Or.inl (concl2 hfn1 hfn2 hfb0 hfb2)
    · by_cases hfb2 : G.Adj f₁ (b 2)
      · have hh := hforceA hfb2 hfn2
        exact False.elim ((Nat.even_add_one.mp hh) ((htotal 2).mpr heven))
      · exact Or.inl (concl3 hfn1 hfb0 hfn2 hfb2)
  · have hfn1 : ¬ G.Adj fn (a 1) := by
      intro hadj
      exact heven ((htotal 1).mp (hdirect 1 hadj hf₁b1))
    have hfb0 : ¬ G.Adj f₁ (b 0) := by
      intro hadj
      exact heven (hdirect 0 hfn0 hadj)
    have hnotBoth : ¬ (G.Adj fn (a 2) ∧ G.Adj f₁ (b 2)) := by
      rintro ⟨ha2, hb2⟩
      exact heven ((htotal 2).mp (hdirect 2 ha2 hb2))
    have hsome : G.Adj fn (a 2) ∨ G.Adj f₁ (b 2) := by
      by_contra hnone
      push_neg at hnone
      have hh := hnoneThird hnone.1 hnone.2
      have ht2 : Even ((R 2).length + f.length) := by
        rw [Nat.even_add] at hh
        exact hh.mpr (by norm_num)
      exact heven ((htotal 2).mp ht2)
    rcases hsome with hfn2 | hfb2
    · exact Or.inr (concl4fn hfn2 hfb0 (fun h => hnotBoth ⟨hfn2, h⟩))
    · exact Or.inl (concl4f hfb2 hfn1 (fun h => hnotBoth ⟨h, hfb2⟩))

/-- **10.1, claim (3)**: *"If `X₁ ⊆ A` and `X₂ ⊆ B` then the theorem holds."*  Here `X₁` is the
attachment set of `F \ {f₁}` and `X₂` that of `F \ {fₙ}`.  This is the parity argument; it is
where `Berge G` is used.

**Orientation — why the conclusion is a disjunction.**  `Thm101Assembly.Concl G a b R K f f₁ fn`
pins the *head* `f₁` of the path as the endpoint carrying the two constrained triangle
neighbours, but 10.1 binds `f₁` and `fₙ` existentially and holds *"up to symmetry"*, so the path
may be traversed in either direction.  Here the disjunction is genuinely required rather than a
convenience: the printed same-parity branch (p. 58) ends *"either `fₙ` is adjacent to `a₃` or
`f₁` to `b₃`, and not both, as we saw before.  But then statement 4 of the theorem holds"* — and
the two sub-cases land on **opposite** orientations.  In the `f₁ adj b₃` sub-case `f₁` has two
`B`-neighbours and 10.1.4 goes through as stated (`Concl … f f₁ fn`); in the `fₙ adj a₃`
sub-case `fₙ` has the two `A`-neighbours and `f₁` has a single `K`-neighbour, so only the
reversed form `Concl … f.reverse fn f₁` can hold. -/
theorem claim_three (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ)
    (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f}) (hn : 2 ≤ f.length)
    (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({a 0, a 1, a 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ ({b 0, b 1, b 2} : Set V)) :
    Thm101Assembly.Concl G a b R K f f₁ fn ∨ Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  classical
  obtain ⟨-, -, hABne, hp, -⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hfne : f₁ ≠ fn :=
    PathBasics.isPathFrom_ends_ne hf (by change 1 ≤ f.length - 1; omega)
  have hf₁F : f₁ ∈ F := by rw [hfF]; exact PathBasics.head_mem hf.2.1
  have hfnF : fn ∈ F := by rw [hfF]; exact PathBasics.getLast_mem hf.2.2
  have hRK : ∀ i : Fin 3, ∀ x : V, x ∈ R i → x ∈ K := by
    intro i x hx
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hmemA : ∀ i : Fin 3, a i ∈ R i :=
    fun i => PathBasics.head_mem (hp i).2.1
  have hmemB : ∀ i : Fin 3, b i ∈ R i :=
    fun i => PathBasics.getLast_mem (hp i).2.2
  have hAindex : ∀ x : V, x ∈ ({a 0, a 1, a 2} : Set V) →
      ∃ i : Fin 3, x = a i := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hBindex : ∀ x : V, x ∈ ({b 0, b 1, b 2} : Set V) →
      ∃ i : Fin 3, x = b i := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hAmem : ∀ i : Fin 3, a i ∈ ({a 0, a 1, a 2} : Set V) := by
    intro i
    rcases fin3_cases i with rfl | rfl | rfl <;> simp
  have hBmem : ∀ i : Fin 3, b i ∈ ({b 0, b 1, b 2} : Set V) := by
    intro i
    rcases fin3_cases i with rfl | rfl | rfl <;> simp
  have hABdisj : ∀ x : V, x ∈ ({a 0, a 1, a 2} : Set V) →
      x ∈ ({b 0, b 1, b 2} : Set V) → False := by
    intro x hxA hxB
    obtain ⟨i, hi⟩ := hAindex x hxA
    obtain ⟨j, hj⟩ := hBindex x hxB
    exact hABne i j (hi.symm.trans hj)
  have hatt : ∀ x ∈ attachments G F K,
      (∃ i : Fin 3, x = a i ∧ G.Adj fn x) ∨
        (∃ i : Fin 3, x = b i ∧ G.Adj f₁ x) := by
    intro x hx
    obtain ⟨hxK, w, hwF, hadj⟩ := hx
    by_cases hw1 : w = f₁
    · subst w
      have hxB : x ∈ ({b 0, b 1, b 2} : Set V) :=
        hX2 ⟨hxK, f₁, ⟨hf₁F, by simp [hfne]⟩, hadj⟩
      obtain ⟨i, hi⟩ := hBindex x hxB
      exact Or.inr ⟨i, hi, hadj.symm⟩
    · have hxA : x ∈ ({a 0, a 1, a 2} : Set V) :=
        hX1 ⟨hxK, w, ⟨hwF, by simpa using hw1⟩, hadj⟩
      by_cases hwn : w = fn
      · subst w
        obtain ⟨i, hi⟩ := hAindex x hxA
        exact Or.inl ⟨i, hi, hadj.symm⟩
      · have hxB : x ∈ ({b 0, b 1, b 2} : Set V) :=
          hX2 ⟨hxK, w, ⟨hwF, by simpa using hwn⟩, hadj⟩
        exact False.elim (hABdisj x hxA hxB)
  have hfnA : ∃ i : Fin 3, G.Adj fn (a i) := by
    by_contra hnone
    push_neg at hnone
    apply hFloc
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    intro x hx
    rcases hatt x hx with ⟨i, hi, hadj⟩ | ⟨i, hi, -⟩
    · exact False.elim (hnone i (by simpa only [hi] using hadj))
    · simpa only [hi] using hBmem i
  have hf₁B : ∃ i : Fin 3, G.Adj f₁ (b i) := by
    by_contra hnone
    push_neg at hnone
    apply hFloc
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    intro x hx
    rcases hatt x hx with ⟨i, hi, -⟩ | ⟨i, hi, hadj⟩
    · simpa only [hi] using hAmem i
    · exact False.elim (hnone i (by simpa only [hi] using hadj))
  have hpair : ∃ i j : Fin 3,
      i ≠ j ∧ G.Adj fn (a i) ∧ G.Adj f₁ (b j) := by
    by_contra hnone
    obtain ⟨i, hi⟩ := hfnA
    obtain ⟨j, hj⟩ := hf₁B
    have hsame : ∀ r s : Fin 3, G.Adj fn (a r) → G.Adj f₁ (b s) → r = s := by
      intro r s hr hs
      by_contra hrs
      exact hnone ⟨r, s, hrs, hr, hs⟩
    have hij : i = j := hsame i j hi hj
    apply hFloc
    have hsub : attachments G F K ⊆ {x : V | x ∈ R i} := by
      intro x hx
      rcases hatt x hx with ⟨r, hr, hadj⟩ | ⟨s, hs, hadj⟩
      · have hri : r = i := by
          have hrj := hsame r j (by simpa only [hr] using hadj) hj
          exact hrj.trans hij.symm
        rw [hr, hri]
        exact hmemA i
      · have his : i = s := hsame i s hi (by simpa only [hs] using hadj)
        rw [hs, ← his]
        exact hmemB i
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl hsub, Or.inr (Or.inl hsub), Or.inr (Or.inr (Or.inl hsub))]
  obtain ⟨i, j, hij, hfni, hfbj⟩ := hpair
  obtain ⟨m, hmi, hmj⟩ := fin3_third i j hij
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ :=
    perm_of_three i j m hij (Ne.symm hmi) (Ne.symm hmj)
  have hc := claim_three_core G hG (fun t => a (σ t)) (fun t => b (σ t))
    (fun t => R (σ t)) K F f f₁ fn (PrismSymmetry.formPrism_perm hprism σ)
    (by rw [hK]; exact (PrismSymmetry.prismVertices_perm R σ).symm)
    hFK hf hfF hn
    (by
      show attachments G (F \ {f₁}) K ⊆
        ({a (σ 0), a (σ 1), a (σ 2)} : Set V)
      rw [PrismSymmetry.triple_perm a σ]
      exact hX1)
    (by
      show attachments G (F \ {fn}) K ⊆
        ({b (σ 0), b (σ 1), b (σ 2)} : Set V)
      rw [PrismSymmetry.triple_perm b σ]
      exact hX2)
    (by simpa only [hσ0] using hfni) (by simpa only [hσ1] using hfbj)
  rcases hc with hc | hc
  · exact Or.inl (Thm101Assembly.concl_perm σ hc)
  · exact Or.inr (Thm101Assembly.concl_perm σ hc)

end Workspace.ProofLemmas.Thm101ClaimThree
