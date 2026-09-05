import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismSymmetry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm101NonlocalPair

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **10.1, paragraph 2.**  PAPER: *"We claim that some two-element subset of `X` is not local.
… So some two-element subset `{x₁, x₂}` of `X` is not local.  Consequently `x₁, x₂` are not
adjacent."* -/
theorem exists_nonlocal_pair (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K X : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hXK : X ⊆ K)
    (hX : ¬ LocalForPrism a b (R 0) (R 1) (R 2) X) :
    ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ ≠ x₂ ∧ ¬ G.Adj x₁ x₂ ∧
      ¬ LocalForPrism a b (R 0) (R 1) (R 2) ({x₁, x₂} : Set V) := by
  obtain ⟨hA, hB, hAB, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hfin : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have hthird : ∀ i k : Fin 3, i ≠ k → ∃ m : Fin 3, m ≠ i ∧ m ≠ k := by decide
  have hmemA : ∀ i : Fin 3, a i ∈ R i := fun i => PathBasics.head_mem (hp i).2.1
  have hmemB : ∀ i : Fin 3, b i ∈ R i := fun i => PathBasics.getLast_mem (hp i).2.2
  -- a triangle vertex lies only on its own path
  have haR : ∀ i k : Fin 3, a k ∈ R i → k = i := by
    intro i k hk
    by_contra hne
    obtain ⟨m, hmi, hmk⟩ := hthird i k (fun h => hne h.symm)
    have h1 := (hedge i m (Ne.symm hmi) (a k) hk (a m) (hmemA m)).mp (hA k m (Ne.symm hmk))
    rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · have h2 := hA k i hne
      rw [h1] at h2
      exact G.irrefl h2
    · exact hAB k i h1
  have hbR : ∀ i k : Fin 3, b k ∈ R i → k = i := by
    intro i k hk
    by_contra hne
    obtain ⟨m, hmi, hmk⟩ := hthird i k (fun h => hne h.symm)
    have h1 := (hedge i m (Ne.symm hmi) (b k) hk (b m) (hmemB m)).mp (hB k m (Ne.symm hmk))
    rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hAB i k h1.symm
    · have h2 := hB k i hne
      rw [h1] at h2
      exact G.irrefl h2
  -- every path of the prism has at least two vertices
  have hlen : ∀ k : Fin 3, 2 ≤ (R k).length := by
    intro k
    by_contra hcon
    have h1 : (R k) ≠ [] := (hp k).1.1
    have h2 : 0 < (R k).length := List.length_pos_of_ne_nil h1
    have h3 : (R k).length = 1 := by omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp h3
    have e1 : (R k).head? = some (a k) := (hp k).2.1
    have e2 : (R k).getLast? = some (b k) := (hp k).2.2
    rw [hc] at e1 e2
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at e1 e2
    exact hAB k k (e1.symm.trans e2)
  -- the three paths are pairwise disjoint
  have hdisj : ∀ i j : Fin 3, i ≠ j → ∀ x : V, x ∈ R i → x ∈ R j → False := by
    intro i j hij x hxi hxj
    obtain ⟨z, hzj, hxz⟩ : ∃ z : V, z ∈ R j ∧ G.Adj x z := by
      obtain ⟨t, ht, hxt⟩ := List.getElem_of_mem hxj
      have hL := hlen j
      by_cases hc : t + 1 < (R j).length
      · refine ⟨(R j)[t + 1], List.getElem_mem _, ?_⟩
        have h := (PathBasics.path_adj_iff (hp j).1 ht hc).mpr (Or.inl rfl)
        rw [hxt] at h
        exact h
      · have ht1 : 1 ≤ t := by omega
        have hlt : t - 1 < (R j).length := by omega
        refine ⟨(R j)[t - 1], List.getElem_mem _, ?_⟩
        have h := (PathBasics.path_adj_iff (hp j).1 ht hlt).mpr (Or.inr (by omega))
        rw [hxt] at h
        exact h
    rcases (hedge i j hij x hxi z hzj).mp hxz with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hij (haR j i (h1 ▸ hxj))
    · exact hij (hbR j i (h1 ▸ hxj))
  -- a vertex of a path that lies in a triangle is that path's own triangle vertex
  have keyA : ∀ (z : V) (k : Fin 3), z ∈ R k → (z = a 0 ∨ z = a 1 ∨ z = a 2) → z = a k := by
    intro z k hz hz3
    rcases hz3 with rfl | rfl | rfl
    · rw [haR k 0 hz]
    · rw [haR k 1 hz]
    · rw [haR k 2 hz]
  have keyB : ∀ (z : V) (k : Fin 3), z ∈ R k → (z = b 0 ∨ z = b 1 ∨ z = b 2) → z = b k := by
    intro z k hz hz3
    rcases hz3 with rfl | rfl | rfl
    · rw [hbR k 0 hz]
    · rw [hbR k 1 hz]
    · rw [hbR k 2 hz]
  -- the key criterion for a two-element subset to be non-local
  have hpair : ∀ (i j : Fin 3) (x y : V), i ≠ j → x ∈ R i → y ∈ R j →
      ¬ (x = a i ∧ y = a j) → ¬ (x = b i ∧ y = b j) →
      x ≠ y ∧ ¬ G.Adj x y ∧ ¬ LocalForPrism a b (R 0) (R 1) (R 2) ({x, y} : Set V) := by
    intro i j x y hij hxi hyj hna hnb
    have hxmem : x ∈ ({x, y} : Set V) := by simp
    have hymem : y ∈ ({x, y} : Set V) := by simp
    have hne : x ≠ y := by
      rintro rfl
      exact hdisj i j hij x hxi hyj
    have hnadj : ¬ G.Adj x y := by
      intro hadj
      rcases (hedge i j hij x hxi y hyj).mp hadj with h | h
      exacts [hna h, hnb h]
    refine ⟨hne, hnadj, ?_⟩
    intro hloc
    have hpathcase : ∀ k : Fin 3, ¬ (({x, y} : Set V) ⊆ {v : V | v ∈ R k}) := by
      intro k hk
      have hxk : x ∈ R k := hk hxmem
      have hyk : y ∈ R k := hk hymem
      rcases eq_or_ne i k with hik | hik
      · exact hdisj j k (fun h => hij (hik.trans h.symm)) y hyj hyk
      · exact hdisj i k hik x hxi hxk
    have hAcase : ¬ (({x, y} : Set V) ⊆ ({a 0, a 1, a 2} : Set V)) := by
      intro h
      have hx' : x = a 0 ∨ x = a 1 ∨ x = a 2 := by simpa using h hxmem
      have hy' : y = a 0 ∨ y = a 1 ∨ y = a 2 := by simpa using h hymem
      exact hna ⟨keyA x i hxi hx', keyA y j hyj hy'⟩
    have hBcase : ¬ (({x, y} : Set V) ⊆ ({b 0, b 1, b 2} : Set V)) := by
      intro h
      have hx' : x = b 0 ∨ x = b 1 ∨ x = b 2 := by simpa using h hxmem
      have hy' : y = b 0 ∨ y = b 1 ∨ y = b 2 := by simpa using h hymem
      exact hnb ⟨keyB x i hxi hx', keyB y j hyj hy'⟩
    rcases hloc with h | h | h | h | h
    · exact hpathcase 0 h
    · exact hpathcase 1 h
    · exact hpathcase 2 h
    · exact hAcase h
    · exact hBcase h
  -- membership in the prism
  have hmemK : ∀ z : V, z ∈ X → ∃ k : Fin 3, z ∈ R k := by
    intro z hz
    have hzK := hXK hz
    rw [hK] at hzK
    simp only [Set.mem_union, Set.mem_setOf_eq] at hzK
    rcases hzK with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  -- the five consequences of `X` not being local
  have hXR : ∀ k : Fin 3, ¬ (X ⊆ {v : V | v ∈ R k}) := by
    intro k hk
    apply hX
    rcases hfin k with rfl | rfl | rfl
    exacts [Or.inl hk, Or.inr (Or.inl hk), Or.inr (Or.inr (Or.inl hk))]
  have hXA : ¬ (X ⊆ ({a 0, a 1, a 2} : Set V)) := fun h =>
    hX (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hXB : ¬ (X ⊆ ({b 0, b 1, b 2} : Set V)) := fun h =>
    hX (Or.inr (Or.inr (Or.inr (Or.inr h))))
  -- PAPER: "since X ⊄ B we may assume that c₁ exists and c₁ ≠ b₁"
  obtain ⟨x, hxX, hxB⟩ := Set.not_subset.mp hXB
  obtain ⟨i, hxi⟩ := hmemK x hxX
  have hxbi : x ≠ b i := by
    rintro rfl
    exact hxB (by rcases hfin i with rfl | rfl | rfl <;> simp)
  by_cases hcase : ∃ k : Fin 3, k ≠ i ∧ ∃ z ∈ X, z ∈ R k ∧ z ≠ a k
  · -- PAPER: "If d₂ ≠ a₂ then {c₁, d₂} is the desired subset"
    obtain ⟨k, hki, z, hzX, hzk, hza⟩ := hcase
    obtain ⟨h1, h2, h3⟩ := hpair i k x z (Ne.symm hki) hxi hzk
      (by rintro ⟨-, h⟩; exact hza h) (by rintro ⟨h, -⟩; exact hxbi h)
    exact ⟨x, hxX, z, hzX, h1, h2, h3⟩
  · -- PAPER: "so we may assume d₂ = a₂, and similarly d₃ = a₃ if d₃ exists"
    have hall : ∀ k : Fin 3, k ≠ i → ∀ z ∈ X, z ∈ R k → z = a k := by
      intro k hki z hzX hzk
      by_contra hza
      exact hcase ⟨k, hki, z, hzX, hzk, hza⟩
    -- PAPER: "Since X ⊄ V(R₁), we may assume d₂ exists"
    obtain ⟨y, hyX, hyi⟩ := Set.not_subset.mp (hXR i)
    obtain ⟨j, hyj⟩ := hmemK y hyX
    have hji : j ≠ i := by
      rintro rfl
      exact hyi hyj
    have hya : y = a j := hall j hji y hyX hyj
    -- PAPER: "Since X ⊄ A, it follows that d₁ ≠ a₁, and then {a₂, d₁} is the desired subset"
    obtain ⟨w, hwX, hwA⟩ := Set.not_subset.mp hXA
    obtain ⟨k, hwk⟩ := hmemK w hwX
    have hki : k = i := by
      by_contra hne
      have hw := hall k hne w hwX hwk
      apply hwA
      rw [hw]
      rcases hfin k with rfl | rfl | rfl <;> simp
    have hwi : w ∈ R i := by rw [← hki]; exact hwk
    have hwa : w ≠ a i := by
      rintro rfl
      exact hwA (by rcases hfin i with rfl | rfl | rfl <;> simp)
    obtain ⟨h1, h2, h3⟩ := hpair i j w y (Ne.symm hji) hwi hyj
      (by rintro ⟨h, -⟩; exact hwa h)
      (by rintro ⟨-, h⟩; exact hAB j j (hya.symm.trans h))
    exact ⟨w, hwX, y, hyX, h1, h2, h3⟩

end Workspace.ProofLemmas.Thm101NonlocalPair
