import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A spanning globally minimum attachment path whose internal vertices have
no neighbours outside its side contains a vertex with exactly two neighbours. -/
theorem SpanningMinimumAttachmentPathHasDegreeTwoVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X A B : Set V) (a b : V) (Q : List V)
    (hAX : A ⊆ X) (hBX : B ⊆ X)
    (ha : a ∈ A) (hb : b ∈ B) (hAB : Disjoint A B)
    (hQ : SPGT.IsPathFrom G Q a b)
    (hmin : ∀ a' ∈ A, ∀ b' ∈ B, ∀ P : List V,
      SPGT.IsPathFrom G P a' b' → (∀ v ∈ P, v ∈ X) →
        SPGT.pathLength Q ≤ SPGT.pathLength P)
    (hspan : {z : V | z ∈ Q} = X)
    (hside : ∀ a' b' : V, A = {a'} → B = {b'} → ∀ P : List V,
      SPGT.IsPathFrom G P a' b' → {z : V | z ∈ P} = X →
        Odd (SPGT.pathLength P) ∧ 3 ≤ SPGT.pathLength P)
    (houtside : ∀ v ∈ X, v ∉ A → v ∉ B → ∀ u, u ∉ X → ¬ G.Adj v u) :
    ∃ v : V, (G.neighborSet v).ncard = 2 := by
  classical
  have hQl : SPGT.IsPathList G Q := hQ.1
  have hQpos : 0 < Q.length := Workspace.ProofLemmas.PathBasics.path_length_pos hQl
  have hQ0 : Q[0]'hQpos = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQlast : Q[Q.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  have hQX : ∀ z : V, z ∈ Q → z ∈ X := by
    intro z hz
    rw [← hspan]
    exact hz
  have hXQ : ∀ z : V, z ∈ X → z ∈ Q := by
    intro z hz
    have hz' : z ∈ {t : V | t ∈ Q} := by
      rw [hspan]
      exact hz
    exact hz'
  have hnotA : ∀ (i : ℕ) (hi : i < Q.length), 0 < i → i < Q.length - 1 →
      Q[i]'hi ∉ A := by
    intro i hi hi0 hil hiA
    have hlastlt : Q.length - 1 < Q.length := by omega
    have hs : SPGT.IsPathFrom G ((Q.drop i).take ((Q.length - 1) - i + 1))
        (Q[i]'hi) b := by
      have hs' := Workspace.ProofLemmas.PathBasics.isPathFrom_slice hQl
        (i := i) (j := Q.length - 1) hil hlastlt
      refine ⟨hs'.1, hs'.2.1, ?_⟩
      simpa only [hQlast] using hs'.2.2
    have hsX : ∀ z ∈ ((Q.drop i).take ((Q.length - 1) - i + 1)), z ∈ X := by
      intro z hz
      apply hQX z
      exact List.mem_of_mem_drop (List.mem_of_mem_take hz)
    have hm := hmin (Q[i]'hi) hiA b hb _ hs hsX
    change Q.length - 1 ≤ ((Q.drop i).take ((Q.length - 1) - i + 1)).length - 1 at hm
    rw [Workspace.ProofLemmas.PathBasics.length_slice Q (le_of_lt hil) hlastlt] at hm
    omega
  have hnotB : ∀ (i : ℕ) (hi : i < Q.length), 0 < i → i < Q.length - 1 →
      Q[i]'hi ∉ B := by
    intro i hi hi0 hil hiB
    have hp : SPGT.IsPathFrom G ((Q.drop 0).take (i - 0 + 1)) a (Q[i]'hi) := by
      have hp' := Workspace.ProofLemmas.PathBasics.isPathFrom_slice hQl
        (i := 0) (j := i) hi0 hi
      refine ⟨hp'.1, ?_, hp'.2.2⟩
      simpa only [hQ0] using hp'.2.1
    have hpX : ∀ z ∈ ((Q.drop 0).take (i - 0 + 1)), z ∈ X := by
      intro z hz
      apply hQX z
      exact List.mem_of_mem_drop (List.mem_of_mem_take hz)
    have hm := hmin a ha (Q[i]'hi) hiB _ hp hpX
    change Q.length - 1 ≤ ((Q.drop 0).take (i - 0 + 1)).length - 1 at hm
    rw [Workspace.ProofLemmas.PathBasics.length_slice Q (i := 0) (j := i) (by omega) hi] at hm
    omega
  have hAeq : A = ({a} : Set V) := by
    apply Set.Subset.antisymm
    · intro x hxA
      have hxQ : x ∈ Q := hXQ x (hAX hxA)
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxQ
      by_cases hi0 : i = 0
      · subst i
        simp only [Set.mem_singleton_iff]
        exact hix.symm.trans hQ0
      by_cases hilast : i = Q.length - 1
      · subst i
        exfalso
        have hxb : x = b := hix.symm.trans hQlast
        have hxB : x ∈ B := hxb.symm ▸ hb
        exact (Set.disjoint_left.mp hAB hxA) hxB
      · exfalso
        have hqiA : Q[i]'hi ∈ A := by simpa only [hix] using hxA
        exact hnotA i hi (by omega) (by omega) hqiA
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact ha
  have hBeq : B = ({b} : Set V) := by
    apply Set.Subset.antisymm
    · intro x hxB
      have hxQ : x ∈ Q := hXQ x (hBX hxB)
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxQ
      by_cases hi0 : i = 0
      · subst i
        exfalso
        have hxa : x = a := hix.symm.trans hQ0
        have hxA : x ∈ A := hxa.symm ▸ ha
        exact (Set.disjoint_right.mp hAB hxB) hxA
      by_cases hilast : i = Q.length - 1
      · subst i
        simp only [Set.mem_singleton_iff]
        exact hix.symm.trans hQlast
      · exfalso
        have hqiB : Q[i]'hi ∈ B := by simpa only [hix] using hxB
        exact hnotB i hi (by omega) (by omega) hqiB
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact hb
  obtain ⟨_, hlen⟩ := hside a b hAeq hBeq Q hQ hspan
  have hQlen : 4 ≤ Q.length := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hlen
    omega
  let x : V := Q[0]'(by omega)
  let v : V := Q[1]'(by omega)
  let y : V := Q[2]'(by omega)
  have hxy : x ≠ y := by
    dsimp only [x, y]
    exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hQl (by omega) (by omega) (by omega)
  have hvX : v ∈ X := by
    dsimp only [v]
    exact hQX _ (List.getElem_mem _)
  have hvA : v ∉ A := by
    dsimp only [v]
    exact hnotA 1 (by omega) (by omega) (by omega)
  have hvB : v ∉ B := by
    dsimp only [v]
    exact hnotB 1 (by omega) (by omega) (by omega)
  have hvx : G.Adj v x := by
    dsimp only [v, x]
    exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hQl (i := 1) (j := 0)
      (by omega) (by omega)).mpr (Or.inr (by omega))
  have hvy : G.Adj v y := by
    dsimp only [v, y]
    exact Workspace.ProofLemmas.PathBasics.path_adj_succ hQl (i := 1) (by omega)
  refine ⟨v, ?_⟩
  have hnbr : G.neighborSet v = ({x, y} : Set V) := by
    apply Set.Subset.antisymm
    · intro z hz
      rw [SimpleGraph.mem_neighborSet] at hz
      by_cases hzX : z ∈ X
      · have hzQ : z ∈ Q := hXQ z hzX
        obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hzQ
        have hadj : G.Adj (Q[1]'(by omega)) (Q[k]'hk) := by
          simpa only [v, ← hkz] using hz
        have hk' := (Workspace.ProofLemmas.PathBasics.path_adj_iff hQl
          (i := 1) (j := k) (by omega) hk).mp hadj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hk' with hk2 | hk0
        · right
          have hkeq : k = 2 := by omega
          calc
            z = Q[k]'hk := hkz.symm
            _ = Q[2]'(by omega) := by subst k; rfl
            _ = y := by rfl
        · left
          have hkeq : k = 0 := by omega
          calc
            z = Q[k]'hk := hkz.symm
            _ = Q[0]'(by omega) := by subst k; rfl
            _ = x := by rfl
      · exfalso
        exact (houtside v hvX hvA hvB z hzX) hz
    · intro z hz
      rw [SimpleGraph.mem_neighborSet]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hvx
      · exact hvy
  rw [hnbr, Set.ncard_pair hxy]

end Workspace.ProofLemmas
