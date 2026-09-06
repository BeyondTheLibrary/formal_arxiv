import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.AntiholeCompletion

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm131Prefix

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem interior_getElem {G : SimpleGraph V} {p : List V}
    (j : ℕ) (hj : j < (SPGT.interior p).length) :
    (SPGT.interior p)[j]'hj = p[j + 1]'(by
      have := Workspace.ProofLemmas.PathBasics.interior_length p
      omega) := by
  have h1 : (SPGT.interior p) = p.tail.dropLast := rfl
  simp only [h1] at hj ⊢
  rw [List.getElem_dropLast, List.getElem_tail]

theorem eq_cons_interior_append {G : SimpleGraph V} {p : List V} {u v : V}
    (h : IsPathFrom G p u v) (hlen : 2 ≤ p.length) :
    p = u :: (SPGT.interior p ++ [v]) := by
  have hint := Workspace.ProofLemmas.PathBasics.interior_length p
  have hu : p[0]'(by omega) = u :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? h.2.1 (by omega)
  have hv : p[p.length - 1]'(by omega) = v :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? h.2.2 (by omega)
  apply List.ext_getElem
  · have hh : (u :: (SPGT.interior p ++ [v])).length = (SPGT.interior p).length + 2 := by
      simp
    omega
  · intro i hi hi'
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simpa using hu
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [List.getElem_cons_succ]
      by_cases hk : k < (SPGT.interior p).length
      · rw [List.getElem_append_left hk]
        exact (interior_getElem (G := G) k hk).symm
      · have hklen : k = (SPGT.interior p).length := by
          simp only [List.length_cons, List.length_append, List.length_singleton,
            hint] at hi'
          omega
        rw [List.getElem_append_right (by omega)]
        have hgz : ∀ (h : k - (SPGT.interior p).length < [v].length),
            [v][k - (SPGT.interior p).length]'h = v := by
          intro h
          simp
        rw [hgz, ← hv]
        exact getElem_congr rfl (show k + 1 = p.length - 1 by omega) hi

/-- PAPER (13.1, claim (2)): *"there is an antipath `Q` joining `a`, `b` with
interior in `W`"* — such an antipath runs along an initial segment of the
trajectory `a-w₁-⋯-wₙ`, because the antipath is induced and `a` has a unique
`Ḡ`-neighbour in `W`. -/
theorem antipath_prefix {G : SimpleGraph V} {a b : V} {w Q : List V}
    (hw : IsAntipathList G (a :: w))
    (hQ : IsAntipathFrom G Q a b)
    (hQint : ∀ z ∈ SPGT.interior Q, z ∈ w)
    (hQ3 : 3 ≤ Q.length) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ w.length ∧ Q = a :: (w.take m ++ [b]) := by
  classical
  have hIlen := Workspace.ProofLemmas.PathBasics.interior_length Q
  have hInodup : (SPGT.interior Q).Nodup :=
    List.Nodup.sublist ((List.dropLast_sublist Q.tail).trans (List.tail_sublist Q))
      (Workspace.ProofLemmas.PathBasics.path_nodup hQ.1)
  have hQ0 : Q[0]'(by omega) = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hwnodup : (a :: w).Nodup :=
    Workspace.ProofLemmas.PathBasics.path_nodup hw
  have hwadj : ∀ (i j : ℕ) (hi : i < (a :: w).length) (hj : j < (a :: w).length),
      (Gᶜ.Adj ((a :: w)[i]'hi) ((a :: w)[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    exact Workspace.ProofLemmas.PathBasics.path_adj_iff hw hi hj
  have hIQ : ∀ (j : ℕ) (hj : j < (SPGT.interior Q).length),
      (SPGT.interior Q)[j]'hj = Q[j + 1]'(by omega) :=
    fun j hj => interior_getElem (G := G) j hj
  have key : ∀ (j : ℕ) (hj : j < (SPGT.interior Q).length),
      ∃ hjw : j < w.length, (SPGT.interior Q)[j]'hj = w[j]'hjw := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hmem : (SPGT.interior Q)[j]'hj ∈ w := hQint _ (List.getElem_mem hj)
      obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
      have hkc : ((a :: w)[k + 1]'(by simp; omega)) = (SPGT.interior Q)[j]'hj := by
        simpa using hkeq
      match j with
      | 0 =>
        -- the first interior vertex is `Ḡ`-adjacent to `a`
        have hadj : Gᶜ.Adj (Q[0]'(by omega)) (Q[0 + 1]'(by omega)) :=
          Workspace.ProofLemmas.PathBasics.path_adj_succ hQ.1 (i := 0) (by omega)
        rw [hQ0, ← hIQ 0 hj, hkeq.symm] at hadj
        have hac : ((a :: w)[0]'(by simp)) = a := by simp
        have hadj' : Gᶜ.Adj ((a :: w)[0]'(by simp)) ((a :: w)[k + 1]'(by simp; omega)) := by
          rw [hac]
          simpa using hadj
        have := (hwadj 0 (k + 1) (by simp) (by simp; omega)).1 hadj'
        have hk0 : k = 0 := by omega
        subst hk0
        exact ⟨by omega, by rw [← hkeq]⟩
      | (n + 1) =>
        obtain ⟨hnw, hn⟩ := ih n (by omega) (by omega)
        have hadj : Gᶜ.Adj (Q[n + 1]'(by omega)) (Q[n + 1 + 1]'(by omega)) :=
          Workspace.ProofLemmas.PathBasics.path_adj_succ hQ.1 (i := n + 1) (by omega)
        rw [← hIQ n (by omega), ← hIQ (n + 1) hj, hn, ← hkeq] at hadj
        have hadj' : Gᶜ.Adj ((a :: w)[n + 1]'(by simp; omega))
            ((a :: w)[k + 1]'(by simp; omega)) := by
          simpa using hadj
        have hcase := (hwadj (n + 1) (k + 1) (by simp; omega) (by simp; omega)).1 hadj'
        have hkn : k = n + 1 := by
          rcases hcase with h | h
          · omega
          · -- `k = n - 1` would repeat an earlier interior vertex
            exfalso
            have hkn1 : k + 1 = n := by omega
            have hn1 : 1 ≤ n := by omega
            obtain ⟨hmw, hm⟩ := ih (n - 1) (by omega) (by omega)
            have heq : (SPGT.interior Q)[n - 1]'(by omega)
                = (SPGT.interior Q)[n + 1]'hj := by
              rw [hm, ← hkeq]
              exact getElem_congr rfl (show n - 1 = k by omega) hmw
            have := (List.Nodup.getElem_inj_iff hInodup).mp heq
            omega
        subst hkn
        exact ⟨by omega, by rw [← hkeq]⟩
  set m : ℕ := (SPGT.interior Q).length with hmdef
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hlastw, -⟩ := key (m - 1) (by omega)
  have hmw : m ≤ w.length := by omega
  have htake : SPGT.interior Q = w.take m := by
    apply List.ext_getElem
    · simp only [List.length_take]
      omega
    · intro i hi hi'
      obtain ⟨hiw, hieq⟩ := key i hi
      rw [hieq]
      simp
  refine ⟨m, hm1, hmw, ?_⟩
  have hdec : Q = a :: (SPGT.interior Q ++ [b]) :=
    eq_cons_interior_append hQ (by omega)
  rw [hdec, htake]

end Workspace.ProofLemmas.Thm131Prefix
