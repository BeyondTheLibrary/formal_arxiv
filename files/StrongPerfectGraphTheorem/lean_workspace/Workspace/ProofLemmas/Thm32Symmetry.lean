import Workspace.ProofLemmas.Thm32OneSided

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! # Reversing the one-sided calculation in Theorem 3.2 -/

namespace Workspace.ProofLemmas.Thm32Symmetry

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem getElem_eq_of_eq {W : Type*} {l : List W} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i = j) : l[i]'hi = l[j]'hj := by
  subst j
  rfl

/-- The right antipath supplied by 2.9 is the reverse of the left situation. -/
theorem right_pattern
    (G : SimpleGraph V) (hG : Berge G) (m n s : ℕ) (p q : List V)
    (hp : IsPathList G p) (hpm : p.length = m)
    (hs1 : 2 ≤ s) (hs2 : s ≤ m - 2)
    (hqn : q.length = n) (hn2 : 2 ≤ n) (hnodd : Odd n)
    (hQ : IsAntipathFrom G (p[s - 1] :: (q ++ [p[s]])) p[s - 1] p[s])
    (hqleft : ∀ x ∈ q, ∃ y ∈ p.take (s - 1), G.Adj x y)
    (hqright : ∀ x ∈ q, ∃ y ∈ p.drop (s + 1), G.Adj x y)
    (w : V) (hw : w ∈ p.drop (s + 1)) (x : V) (hx : x ∈ p.drop (s + 1))
    (hwx : ¬ Gᶜ.Adj w x)
    (hW : IsPathList Gᶜ (w :: ((q ++ [p[s]]) ++ [x]))) :
    s ≤ m - 3 ∧ ∀ z ∈ (p.drop (s - 2)).take 5, ∀ y ∈ q,
      (¬ G.Adj z y ↔
        (z = p[s - 1] ∧ y = q[0]) ∨ (z = p[s] ∧ y = q[n - 1]) ∨
          (z = p[s + 1] ∧ y = q[0])) := by
  classical
  let t : ℕ := m - s
  let pr : List V := p.reverse
  let qr : List V := q.reverse
  have hplen : p.length = m := hpm
  have hprlen : pr.length = m := by simp [pr, hpm]
  have hqrlen : qr.length = n := by simp [qr, hqn]
  have ht2 : 2 ≤ t := by dsimp [t]; omega
  have htle : t ≤ m - 2 := by dsimp [t]; omega
  have htlt : t < pr.length := by omega
  have htm1lt : t - 1 < pr.length := by omega
  have hpslt : s < p.length := by omega
  have hsm1lt : s - 1 < p.length := by omega
  have hsp1lt : s + 1 < p.length := by omega
  have hpr_tm1 : pr[t - 1]'htm1lt = p[s] := by
    simp only [pr, List.getElem_reverse]
    exact getElem_eq_of_eq _ _ (by dsimp [t]; omega)
  have hpr_t : pr[t]'htlt = p[s - 1] := by
    simp only [pr, List.getElem_reverse]
    exact getElem_eq_of_eq _ _ (by dsimp [t]; omega)
  have htake : pr.take (t - 1) = (p.drop (s + 1)).reverse := by
    simp only [pr, List.take_reverse]
    congr 2
    dsimp [t]
    omega
  have hdrop : pr.drop (t + 1) = (p.take (s - 1)).reverse := by
    simp only [pr, List.drop_reverse]
    congr 2
    dsimp [t]
    omega
  have hqleft' : ∀ z ∈ qr, ∃ y ∈ pr.take (t - 1), G.Adj z y := by
    intro z hz
    have hzq : z ∈ q := by simpa [qr] using hz
    obtain ⟨y, hy, hzy⟩ := hqright z hzq
    refine ⟨y, ?_, hzy⟩
    rw [htake, List.mem_reverse]
    exact hy
  have hqright' : ∀ z ∈ qr, ∃ y ∈ pr.drop (t + 1), G.Adj z y := by
    intro z hz
    have hzq : z ∈ q := by simpa [qr] using hz
    obtain ⟨y, hy, hzy⟩ := hqleft z hzq
    refine ⟨y, ?_, hzy⟩
    rw [hdrop, List.mem_reverse]
    exact hy
  have hQrev0 := Workspace.ProofLemmas.PathBasics.isAntipathFrom_reverse hQ
  have hQrev : IsAntipathFrom G (p[s] :: (qr ++ [p[s - 1]])) p[s] p[s - 1] := by
    simpa [qr, List.reverse_append] using hQrev0
  have hQ' : IsAntipathFrom G (pr[t - 1] :: (qr ++ [pr[t]])) pr[t - 1] pr[t] := by
    simpa only [hpr_tm1, hpr_t] using hQrev
  have hx' : x ∈ pr.take (t - 1) := by
    rw [htake, List.mem_reverse]
    exact hx
  have hw' : w ∈ pr.take (t - 1) := by
    rw [htake, List.mem_reverse]
    exact hw
  have hWrev0 := Workspace.ProofLemmas.PathBasics.isPathList_reverse hW
  have hWrev : IsPathList Gᶜ (x :: ((p[s] :: qr) ++ [w])) := by
    simpa [qr, List.reverse_append] using hWrev0
  have hW' : IsPathList Gᶜ (x :: ((pr[t - 1] :: qr) ++ [w])) := by
    simpa only [hpr_tm1] using hWrev
  have hleft := Workspace.ProofLemmas.Thm32OneSided.left_pattern
    G hG m n t pr qr (Workspace.ProofLemmas.PathBasics.isPathList_reverse hp) hprlen
      ht2 htle hqrlen hn2 hnodd hQ' hqleft' hqright' x hx' w hw'
      (fun hadj => hwx hadj.symm) hW'
  obtain ⟨ht3, hpat⟩ := hleft
  have hsright : s ≤ m - 3 := by dsimp [t] at ht3; omega
  have hsp2lt : s + 2 < p.length := by omega
  have htpr : t + 1 < pr.length := by omega
  have ht3pr : t - 3 ≤ t + 1 := by omega
  have hpr_tm2 : pr[t - 2]'(by omega) = p[s + 1] := by
    simp only [pr, List.getElem_reverse]
    exact getElem_eq_of_eq _ _ (by dsimp [t]; omega)
  have hpr_tp1 : pr[t + 1]'htpr = p[s - 2] := by
    simp only [pr, List.getElem_reverse]
    exact getElem_eq_of_eq _ _ (by dsimp [t]; omega)
  have hqr_last : qr[n - 1]'(by omega) = q[0] := by
    simp only [qr, List.getElem_reverse]
    exact getElem_eq_of_eq _ _ (by omega)
  have hqr_zero : qr[0]'(by omega) = q[n - 1] := by
    simp only [qr, List.getElem_reverse]
    exact getElem_eq_of_eq _ _ (by omega)
  refine ⟨hsright, ?_⟩
  intro z hz y hy
  have hzslice : z ∈ (p.drop (s - 2)).take (s + 2 - (s - 2) + 1) := by
    simpa only [show s + 2 - (s - 2) + 1 = 5 by omega] using hz
  obtain ⟨k, hk, hsk, hks, hkz⟩ :=
    (Workspace.ProofLemmas.PathBasics.mem_slice_iff p (i := s - 2) (j := s + 2)
      (by omega) hsp2lt).mp hzslice
  let kr : ℕ := m - 1 - k
  have hkr : kr < pr.length := by dsimp [kr]; omega
  have hkrlo : t - 3 ≤ kr := by dsimp [kr, t]; omega
  have hkrhi : kr ≤ t + 1 := by dsimp [kr, t]; omega
  have hprkr : pr[kr]'hkr = z := by
    simp only [pr, List.getElem_reverse]
    exact (getElem_eq_of_eq _ _ (by dsimp [kr]; omega)).trans hkz
  have hzrevSlice : z ∈ (pr.drop (t - 3)).take (t + 1 - (t - 3) + 1) :=
    (Workspace.ProofLemmas.PathBasics.mem_slice_iff pr ht3pr htpr).2
      ⟨kr, hkr, hkrlo, hkrhi, hprkr⟩
  have hzrev : z ∈ (pr.drop (t - 3)).take 5 := by
    simpa only [show t + 1 - (t - 3) + 1 = 5 by omega] using hzrevSlice
  have hyrev : y ∈ qr := by simpa [qr] using hy
  have hiff := hpat z hzrev y hyrev
  constructor
  · intro hnon
    rcases hiff.mp hnon with ⟨hz0, hy0⟩ | ⟨hz0, hy0⟩ | ⟨hz0, hy0⟩
    · right; right
      exact ⟨hz0.trans hpr_tm2, hy0.trans hqr_last⟩
    · right; left
      exact ⟨hz0.trans hpr_tm1, hy0.trans hqr_zero⟩
    · left
      exact ⟨hz0.trans hpr_t, hy0.trans hqr_last⟩
  · intro hcases
    apply hiff.mpr
    rcases hcases with ⟨hz0, hy0⟩ | ⟨hz0, hy0⟩ | ⟨hz0, hy0⟩
    · right; right
      exact ⟨hz0.trans hpr_t.symm, hy0.trans hqr_last.symm⟩
    · right; left
      exact ⟨hz0.trans hpr_tm1.symm, hy0.trans hqr_zero.symm⟩
    · left
      exact ⟨hz0.trans hpr_tm2.symm, hy0.trans hqr_last.symm⟩

end Workspace.ProofLemmas.Thm32Symmetry
