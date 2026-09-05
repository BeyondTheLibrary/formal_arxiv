import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics

/-!
# A Roussel-Rubio leap turns a path into a long prism

Statement 2.1 (the Roussel-Rubio lemma) offers, as its second alternative, a *leap* `a, b` for
the path `P`: two nonadjacent vertices such that `a` is adjacent to exactly the first, second
and last vertices of `P`, and `b` to exactly the first, last-but-one and last.  Every section
that invokes that alternative -- 7, 10, 11, 12, 15 -- immediately says the same thing:

> *"and then the subgraph induced on `V(P) ∪ {x,y}` is a long prism"*

(printed p. 92, in the proof of 15.1; the same sentence, with different names, elsewhere).

This module supplies that step once.  The prism is

* triangles `{a, p₀, p₁}` and `{p_k, b, p_{k-1}}`, where `k = pathLength P`;
* joined by the three paths `[a, p_k]`, `[p₀, b]` and `p₁-⋯-p_{k-1}`,

so the three path lengths are `1`, `1` and `k - 2`, and the prism is *long* -- some path has
length `> 1` -- exactly when `k ≥ 4`.  That is why the callers first arrange `pathLength P ≥ 5`
(the leap alternative of 2.1 already carries `5 ≤ pathLength P`).

Nothing here is specific to any one section: the only inputs are `IsLeapForPath` and the
length bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.LeapPrism

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem longPrism_of_leap {G : SimpleGraph V} {p : List V} {a b : V}
    (hleap : IsLeapForPath G p a b) (hlen : 4 ≤ pathLength p) :
    ∃ (α β : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsLongPrism G α β Q₁ Q₂ Q₃ := by
  obtain ⟨hp, -, hab_ne, hab_nadj, hA, hB⟩ := hleap
  have hn : 5 ≤ p.length := by
    have : pathLength p = p.length - 1 := rfl
    omega
  -- non-dependent access to the vertices of `p`
  obtain ⟨f, hf⟩ : ∃ f : ℕ → V, ∀ i (h : i < p.length), f i = p[i]'h :=
    ⟨fun i => p.getD i (p[0]'(by omega)), fun i h => List.getD_eq_getElem _ _ h⟩
  have hfmem : ∀ i, i < p.length → f i ∈ p := by
    intro i h; rw [hf i h]; exact List.getElem_mem h
  have hfinj : ∀ i j, i < p.length → j < p.length → (f i = f j ↔ i = j) := by
    intro i j hi hj
    rw [hf i hi, hf j hj]
    exact List.Nodup.getElem_inj_iff hp.2.1
  have hfadj : ∀ i j (hi : i < p.length) (hj : j < p.length),
      (G.Adj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    rw [hf i hi, hf j hj]
    exact PathBasics.path_adj_iff hp hi hj
  have hfA : ∀ i (hi : i < p.length),
      (G.Adj a (f i) ↔ (i = 0 ∨ i = 1 ∨ i = p.length - 1)) := by
    intro i hi; rw [hf i hi]; exact hA i hi
  have hfB : ∀ i (hi : i < p.length),
      (G.Adj b (f i) ↔ (i = 0 ∨ i = p.length - 2 ∨ i = p.length - 1)) := by
    intro i hi; rw [hf i hi]; exact hB i hi
  -- `a` and `b` are not on `p`
  have hanot : ∀ i, i < p.length → a ≠ f i := by
    intro i hi he
    have h0 : G.Adj (f i) (f 0) := he ▸ (hfA 0 (by omega)).mpr (Or.inl rfl)
    have hi1 : i = 1 := by
      rcases (hfadj i 0 hi (by omega)).mp h0 with h | h <;> omega
    subst hi1
    exact G.irrefl (he ▸ (hfA 1 (by omega)).mpr (Or.inr (Or.inl rfl)))
  have hbnot : ∀ i, i < p.length → b ≠ f i := by
    intro i hi he
    have h0 : G.Adj (f i) (f 0) := he ▸ (hfB 0 (by omega)).mpr (Or.inl rfl)
    have hi1 : i = 1 := by
      rcases (hfadj i 0 hi (by omega)).mp h0 with h | h <;> omega
    subst hi1
    have hlast : G.Adj (f 1) (f (p.length - 1)) :=
      he ▸ (hfB (p.length - 1) (by omega)).mpr (Or.inr (Or.inr rfl))
    rcases (hfadj 1 (p.length - 1) (by omega) (by omega)).mp hlast with h | h <;> omega
  have hane : ∀ i, i < p.length → f i ≠ a := fun i hi h => hanot i hi h.symm
  have hbne : ∀ i, i < p.length → f i ≠ b := fun i hi h => hbnot i hi h.symm
  -- the six triangle vertices
  have haa0 : G.Adj a (f 0) := (hfA 0 (by omega)).mpr (Or.inl rfl)
  have haa1 : G.Adj a (f 1) := (hfA 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have haan : G.Adj a (f (p.length - 1)) := (hfA _ (by omega)).mpr (Or.inr (Or.inr rfl))
  have hbb0 : G.Adj b (f 0) := (hfB 0 (by omega)).mpr (Or.inl rfl)
  have hbbn2 : G.Adj b (f (p.length - 2)) := (hfB _ (by omega)).mpr (Or.inr (Or.inl rfl))
  have hbbn1 : G.Adj b (f (p.length - 1)) := (hfB _ (by omega)).mpr (Or.inr (Or.inr rfl))
  -- the middle path `p₁-⋯-p_{k-1}`
  have hslice : IsPathList G ((p.drop 1).take (p.length - 2 - 1 + 1)) :=
    PathBasics.isPathList_slice hp (by omega) (by omega)
  have hslicelen : ((p.drop 1).take (p.length - 2 - 1 + 1)).length = p.length - 2 :=
    (PathBasics.length_slice p (by omega) (by omega)).trans (by omega)
  have hslicefrom : IsPathFrom G ((p.drop 1).take (p.length - 2 - 1 + 1))
      (f 1) (f (p.length - 2)) := by
    refine ⟨hslice, ?_, ?_⟩
    · rw [PathBasics.head?_slice p (by omega) (by omega), hf 1 (by omega)]
    · rw [PathBasics.getLast?_slice p (by omega) (by omega), hf (p.length - 2) (by omega)]
  have hslicemem : ∀ x, x ∈ (p.drop 1).take (p.length - 2 - 1 + 1) ↔
      ∃ c, c < p.length ∧ 1 ≤ c ∧ c ≤ p.length - 2 ∧ f c = x := by
    intro x
    rw [PathBasics.mem_slice_iff p (show (1 : ℕ) ≤ p.length - 2 by omega) (by omega)]
    constructor
    · rintro ⟨c, hc, h1, h2, rfl⟩
      exact ⟨c, hc, h1, h2, hf c hc⟩
    · rintro ⟨c, hc, h1, h2, rfl⟩
      exact ⟨c, hc, h1, h2, (hf c hc).symm⟩
  -- the two length-one paths
  have hpair : ∀ u v : V, G.Adj u v → IsPathFrom G [u, v] u v := by
    intro u v huv
    refine ⟨⟨by simp, by simp [G.ne_of_adj huv], ?_⟩, rfl, rfl⟩
    intro i j hi hj
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      simp_all [huv.symm]
  refine PrismBasics.formPrism_mk (P₁ := [a, f (p.length - 1)]) (P₂ := [f 0, b])
    (P₃ := (p.drop 1).take (p.length - 2 - 1 + 1))
    haa0 haa1 ((hfadj 0 1 (by omega) (by omega)).mpr (Or.inl rfl))
    hbbn1.symm ((hfadj (p.length - 1) (p.length - 2) (by omega) (by omega)).mpr
      (Or.inr (by omega)))
    hbbn2
    (fun h => hanot _ (by omega) h) hab_ne (fun h => hanot _ (by omega) h)
    (fun h => absurd ((hfinj 0 (p.length - 1) (by omega) (by omega)).mp h) (by omega))
    (fun h => hbnot 0 (by omega) h.symm)
    (fun h => absurd ((hfinj 0 (p.length - 2) (by omega) (by omega)).mp h) (by omega))
    (fun h => absurd ((hfinj 1 (p.length - 1) (by omega) (by omega)).mp h) (by omega))
    (fun h => hbnot 1 (by omega) h.symm)
    (fun h => absurd ((hfinj 1 (p.length - 2) (by omega) (by omega)).mp h) (by omega))
    (hpair _ _ haan) (hpair _ _ hbb0.symm) hslicefrom ?_ ?_ ?_ ?_
  · -- edges between `[a, p_{k}]` and `[p₀, b]`
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact iff_of_true haa0 (Or.inl ⟨rfl, rfl⟩)
    · refine iff_of_false hab_nadj ?_
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hbnot 0 (by omega) h
      · exact hanot _ (by omega) h
    · refine iff_of_false ?_ ?_
      · intro h
        rcases (hfadj (p.length - 1) 0 (by omega) (by omega)).mp h with h' | h' <;> omega
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hane _ (by omega) h
        · exact hbne 0 (by omega) h
    · exact iff_of_true hbbn1.symm (Or.inr ⟨rfl, rfl⟩)
  · -- edges between `[a, p_{k}]` and the middle path
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    obtain ⟨c, hc, hc1, hc2, rfl⟩ := (hslicemem v).mp hv
    rcases hu with rfl | rfl
    · rw [hfA c hc]
      constructor
      · intro h
        exact Or.inl ⟨rfl, (hfinj c 1 hc (by omega)).mpr (by omega)⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact Or.inr (Or.inl ((hfinj c 1 hc (by omega)).mp h))
        · exact absurd h (hanot (p.length - 1) (by omega))
    · rw [hfadj (p.length - 1) c (by omega) hc]
      constructor
      · intro h
        exact Or.inr ⟨rfl, (hfinj c (p.length - 2) hc (by omega)).mpr (by omega)⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h (hane (p.length - 1) (by omega))
        · have := (hfinj c (p.length - 2) hc (by omega)).mp h
          omega
  · -- edges between `[p₀, b]` and the middle path
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    obtain ⟨c, hc, hc1, hc2, rfl⟩ := (hslicemem v).mp hv
    rcases hu with rfl | rfl
    · rw [hfadj 0 c (by omega) hc]
      constructor
      · intro h
        exact Or.inl ⟨rfl, (hfinj c 1 hc (by omega)).mpr (by omega)⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · have := (hfinj c 1 hc (by omega)).mp h
          omega
        · exact absurd h.symm (hbnot 0 (by omega))
    · rw [hfB c hc]
      constructor
      · intro h
        exact Or.inr ⟨rfl, (hfinj c (p.length - 2) hc (by omega)).mpr (by omega)⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h (hbnot 0 (by omega))
        · exact Or.inr (Or.inl ((hfinj c (p.length - 2) hc (by omega)).mp h))
  · -- the middle path is long
    right; right
    have : pathLength ((p.drop 1).take (p.length - 2 - 1 + 1)) = p.length - 3 := by
      simp only [pathLength, hslicelen]; omega
    have hpl : pathLength p = p.length - 1 := rfl
    omega

end Workspace.ProofLemmas.LeapPrism
