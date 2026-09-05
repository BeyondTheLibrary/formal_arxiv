import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# Attaching a vertex to the end of an induced path

`Workspace.ProofLemmas.PrismBasics` has the lemmas that close a path into a **hole** through
one or two extra vertices.  This module supplies the missing companion: extending a path to a
longer **path** by hanging a new vertex off one end (or off each end).  The paper writes this
as `s-u-P-v` and `s-u-P-v-t`, and does it constantly — most often in `Gᶜ`, where it reads
*"`x-f-x₁-Q-x₁'` is an antipath"*.

Everything is stated for an arbitrary `G`, so the antipath forms are the same lemmas applied
to `Gᶜ` (`IsAntipathFrom G p u v` is `IsPathFrom Gᶜ p u v` by definition).

None of these corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.PathAttach

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V} {p : List V} {u v s t : V}

/-- **Hanging a vertex off the front of a path.**  If `p` is a path from `u` to `v`, and `s`
is a vertex outside `p` adjacent to `u` and to no other vertex of `p`, then `s :: p` is a path
from `s` to `v` — the paper's `s-u-P-v`. -/
theorem isPathFrom_cons (hp : IsPathFrom G p u v) (hsu : G.Adj s u) (hs : s ∉ p)
    (hother : ∀ x ∈ p, x ≠ u → ¬ G.Adj s x) :
    IsPathFrom G (s :: p) s v := by
  obtain ⟨hpl, hhd, hlst⟩ := hp
  have hpos : 0 < p.length := PathBasics.path_length_pos hpl
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hhd hpos
  have hnd : p.Nodup := PathBasics.path_nodup hpl
  refine ⟨⟨List.cons_ne_nil _ _, List.nodup_cons.mpr ⟨hs, hnd⟩, ?_⟩, rfl, ?_⟩
  · intro i j hi hj
    have hi' : i < p.length + 1 := by simpa using hi
    have hj' : j < p.length + 1 := by simpa using hj
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hj0 : j = 0
      · subst hj0
        simp only [List.getElem_cons_zero]
        exact iff_of_false G.irrefl (by omega)
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hjp : j' < p.length := by omega
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        by_cases hj1 : j' = 0
        · subst hj1
          rw [h0]
          exact iff_of_true hsu (Or.inl rfl)
        · refine iff_of_false ?_ (by omega)
          refine hother _ (List.getElem_mem hjp) ?_
          intro he
          exact hj1 (hnd.getElem_inj_iff.mp (he.trans h0.symm))
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hip : i' < p.length := by omega
      by_cases hj0 : j = 0
      · subst hj0
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        by_cases hi1 : i' = 0
        · subst hi1
          rw [h0]
          exact iff_of_true hsu.symm (Or.inr rfl)
        · refine iff_of_false ?_ (by omega)
          intro hadj
          refine hother _ (List.getElem_mem hip) ?_ hadj.symm
          intro he
          exact hi1 (hnd.getElem_inj_iff.mp (he.trans h0.symm))
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hjp : j' < p.length := by omega
        simp only [List.getElem_cons_succ]
        rw [PathBasics.path_adj_iff hpl hip hjp]
        omega
  · rw [List.getLast?_cons_of_ne_nil (PathBasics.path_ne_nil hpl)]
    exact hlst

/-- **Hanging a vertex off the back of a path** — the mirror image of `isPathFrom_cons`,
obtained from it by reversing. -/
theorem isPathFrom_concat (hp : IsPathFrom G p u v) (htv : G.Adj t v) (ht : t ∉ p)
    (hother : ∀ x ∈ p, x ≠ v → ¬ G.Adj t x) :
    IsPathFrom G (p ++ [t]) u t := by
  have hr : IsPathFrom G p.reverse v u := PathBasics.isPathFrom_reverse hp
  have hc : IsPathFrom G (t :: p.reverse) t u := by
    refine isPathFrom_cons hr htv (by simpa using ht) ?_
    intro x hx hxv
    exact hother x (by simpa using hx) hxv
  have hrr := PathBasics.isPathFrom_reverse hc
  simpa using hrr

/-- **Hanging a vertex off each end of a path.**  The paper's `s-u-P-v-t`. -/
theorem isPathFrom_cons_concat (hp : IsPathFrom G p u v)
    (hsu : G.Adj s u) (htv : G.Adj t v) (hst : ¬ G.Adj s t) (hne : s ≠ t)
    (hs : s ∉ p) (ht : t ∉ p)
    (hsother : ∀ x ∈ p, x ≠ u → ¬ G.Adj s x)
    (htother : ∀ x ∈ p, x ≠ v → ¬ G.Adj t x) :
    IsPathFrom G (s :: (p ++ [t])) s t := by
  have h1 : IsPathFrom G (p ++ [t]) u t := isPathFrom_concat hp htv ht htother
  refine isPathFrom_cons h1 hsu ?_ ?_
  · intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hs h
    · exact hne (by simpa using h)
  · intro x hx hxu
    rcases List.mem_append.mp hx with h | h
    · exact hsother x h hxu
    · rw [List.mem_singleton] at h
      subst h
      exact hst

/-! ### Length and membership bookkeeping -/

theorem length_cons_append_singleton (s t : V) (p : List V) :
    (s :: (p ++ [t])).length = p.length + 2 := by
  simp

theorem pathLength_cons_append_singleton (s t : V) (p : List V) :
    pathLength (s :: (p ++ [t])) = p.length + 1 := by
  simp only [pathLength, length_cons_append_singleton]
  omega

theorem mem_cons_append_singleton {x : V} :
    x ∈ s :: (p ++ [t]) ↔ (x = s ∨ x ∈ p ∨ x = t) := by
  simp

end Workspace.ProofLemmas.PathAttach
