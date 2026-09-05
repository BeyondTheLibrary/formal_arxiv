import Workspace.Statements.S02.Thm_2_1
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.InducedPathExtraction

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! # The one-sided leap calculation in Theorem 3.2 -/

namespace Workspace.ProofLemmas.Thm32OneSided

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem mem_take_index {p : List V} {k : ℕ} {z : V} (hz : z ∈ p.take k) :
    ∃ i : ℕ, ∃ hi : i < p.length, i < k ∧ p[i]'hi = z := by
  obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp hz
  have hip : i < p.length := lt_of_lt_of_le hi (by
    simp only [List.length_take]
    exact Nat.min_le_right _ _)
  have hik : i < k := by
    rw [List.length_take] at hi
    omega
  refine ⟨i, hip, hik, ?_⟩
  rw [← hieq]
  exact (List.getElem_take ..).symm

private theorem mem_drop_index {p : List V} {k : ℕ} {z : V} (hz : z ∈ p.drop k) :
    ∃ i : ℕ, ∃ hi : i < p.length, k ≤ i ∧ p[i]'hi = z := by
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hz
  have hjlen : j < p.length - k := by simpa using hj
  refine ⟨k + j, by omega, by omega, ?_⟩
  rw [← hjeq]
  simp

private theorem mem_drop_of_index {p : List V} {k i : ℕ} (hi : i < p.length) (hki : k ≤ i) :
    p[i]'hi ∈ p.drop k := by
  refine List.mem_iff_getElem.mpr ⟨i - k, by simp only [List.length_drop]; omega, ?_⟩
  rw [List.getElem_drop]
  have heq : k + (i - k) = i := by omega
  simp only [heq]

private theorem adj_of_not_compl_adj {G : SimpleGraph V} {x y : V} (hne : x ≠ y)
    (hc : ¬ Gᶜ.Adj x y) : G.Adj x y := by
  by_contra hcon
  exact hc ((G.compl_adj x y).2 ⟨hne, hcon⟩)

private theorem get_q_in_left_path (u a v : V) (q : List V) {j : ℕ} (hj : j < q.length) :
    (u :: ((a :: q) ++ [v]))[j + 2]'(by simp; omega) = q[j]'hj := by
  rw [List.getElem_cons_succ, List.getElem_append_left (by simp; omega),
    List.getElem_cons_succ]

private theorem get_last_in_left_path (u a v : V) (q : List V) :
    (u :: ((a :: q) ++ [v]))[q.length + 2]'(by simp) = v := by
  rw [List.getElem_cons_succ, List.getElem_append_right (by simp)]
  simp

/-- The left antipath supplied by 2.9 has the exact first attachment pattern of 3.2. -/
theorem left_pattern
    (G : SimpleGraph V) (hG : Berge G) (m n s : ℕ) (p q : List V)
    (hp : IsPathList G p) (hpm : p.length = m)
    (hs1 : 2 ≤ s) (hs2 : s ≤ m - 2)
    (hqn : q.length = n) (hn2 : 2 ≤ n) (hnodd : Odd n)
    (hQ : IsAntipathFrom G (p[s - 1] :: (q ++ [p[s]])) p[s - 1] p[s])
    (hqleft : ∀ x ∈ q, ∃ y ∈ p.take (s - 1), G.Adj x y)
    (hqright : ∀ x ∈ q, ∃ y ∈ p.drop (s + 1), G.Adj x y)
    (u : V) (hu : u ∈ p.take (s - 1)) (v : V) (hv : v ∈ p.take (s - 1))
    (huv : ¬ Gᶜ.Adj u v)
    (hW : IsPathList Gᶜ (u :: ((p[s - 1] :: q) ++ [v]))) :
    3 ≤ s ∧ ∀ x ∈ (p.drop (s - 3)).take 5, ∀ y ∈ q,
      (¬ G.Adj x y ↔
        (x = p[s - 2] ∧ y = q[n - 1]) ∨ (x = p[s - 1] ∧ y = q[0]) ∨
          (x = p[s] ∧ y = q[n - 1])) := by
  classical
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hnodd
    omega
  have hslt : s < p.length := by omega
  have hsm1lt : s - 1 < p.length := by omega
  have hsp1lt : s + 1 < p.length := by omega
  let W : List V := u :: ((p[s - 1] :: q) ++ [v])
  change IsPathList Gᶜ W at hW
  have hWlen : W.length = n + 3 := by simp [W, hqn]
  have hW0 : W[0]'(by omega) = u := by simp [W]
  have hW1 : W[1]'(by omega) = p[s - 1] := by simp [W]
  have hWlast : W[n + 2]'(by omega) = v := by
    simpa only [W, hqn] using get_last_in_left_path u p[s - 1] v q
  obtain ⟨iu, hiu, hius, hiueq⟩ := mem_take_index hu
  obtain ⟨iv, hiv, hivs, hiveq⟩ := mem_take_index hv
  have hpsv_ne : p[s - 1] ≠ v := by
    have hne := Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hW
      (i := 1) (j := n + 2) (by omega) (by omega) (by omega)
    intro he
    exact hne (hW1.trans (he.trans hWlast.symm))
  have hpsv_nc : ¬ Gᶜ.Adj p[s - 1] v := by
    have hnc := Workspace.ProofLemmas.PathBasics.path_not_adj_of_gap hW
      (i := 1) (j := n + 2) (by omega) (by omega) (by omega) (by omega)
    intro hadj
    exact hnc (by simpa only [hW1, hWlast] using hadj)
  have hpsv : G.Adj p[s - 1] v := adj_of_not_compl_adj hpsv_ne hpsv_nc
  have hiv_eq : iv = s - 2 := by
    rw [← hiveq] at hpsv
    rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hsm1lt hiv).mp hpsv with h | h <;>
      omega
  subst iv
  have huv_ne : u ≠ v := by
    have hne := Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hW
      (i := 0) (j := n + 2) (by omega) (by omega) (by omega)
    intro he
    exact hne (hW0.trans (he.trans hWlast.symm))
  have huvG : G.Adj u v := adj_of_not_compl_adj huv_ne huv
  have hiune : iu ≠ s - 2 := by
    intro he
    apply huv_ne
    rw [← hiueq, ← hiveq]
    subst he
    rfl
  have hs3 : 3 ≤ s := by omega
  have hiu_eq : iu = s - 3 := by
    rw [← hiueq, ← hiveq] at huvG
    rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hiu hiv).mp huvG with h | h <;>
      omega
  subst iu
  -- The tail beginning with `p[s]` is the anticonnected set to which 2.1 is applied.
  let T : Set V := {z : V | z ∈ p.drop s}
  have hTanti : AnticonnectedSet Gᶜ T := by
    unfold AnticonnectedSet
    simpa only [compl_compl] using
      Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (Workspace.ProofLemmas.PathBasics.isPathList_drop hp (by omega))
  have hWout : ∀ z ∈ W, z ∉ T := by
    intro z hz hzT
    simp [W] at hz
    rcases hz with hz | hz | hz | hz
    · subst z
      obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzT
      have := hp.2.1.getElem_inj_iff.mp (hiueq.trans hiz.symm)
      omega
    · subst z
      obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzT
      have := hp.2.1.getElem_inj_iff.mp (hiz.trans rfl)
      omega
    · obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzT
      obtain ⟨zL, hzL, hzzL⟩ := hqleft z hz
      obtain ⟨j, hj, hjs, hjz⟩ := mem_take_index hzL
      rw [← hiz, ← hjz] at hzzL
      rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hi hj).mp hzzL with h | h <;>
        omega
    · subst z
      obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzT
      have := hp.2.1.getElem_inj_iff.mp (hiz.trans hiveq.symm)
      omega
  have huT : VertexComplete Gᶜ u T := by
    intro z hzT
    obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzT
    have hne : u ≠ z := by
      intro he
      have := hp.2.1.getElem_inj_iff.mp (hiueq.trans (he.trans hiz.symm))
      omega
    refine (G.compl_adj _ _).2 ⟨hne, ?_⟩
    rw [← hiueq, ← hiz]
    exact Workspace.ProofLemmas.PathBasics.path_not_adj_of_gap hp hiu hi (by omega) (by omega)
  have hvT : VertexComplete Gᶜ v T := by
    intro z hzT
    obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzT
    have hne : v ≠ z := by
      intro he
      have := hp.2.1.getElem_inj_iff.mp (hiveq.trans (he.trans hiz.symm))
      omega
    refine (G.compl_adj _ _).2 ⟨hne, ?_⟩
    rw [← hiveq, ← hiz]
    exact Workspace.ProofLemmas.PathBasics.path_not_adj_of_gap hp hiv hi (by omega) (by omega)
  have hWhead : W.head? = some u := by simp [W]
  have hWlastopt : W.getLast? = some v := by
    simp only [W]
    rw [List.getLast?_cons_of_ne_nil (by simp),
      List.getLast?_append_of_ne_nil _ (by simp : [v] ≠ [])]
    rfl
  have hWodd : Odd (pathLength W) := by
    obtain ⟨k, hk⟩ := hnodd
    refine ⟨k + 1, ?_⟩
    simp [pathLength, hWlen]
    omega
  have h21 := Workspace.Statements.S02.SPGT.thm_2_1 Gᶜ
    (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) T hTanti W u v
      ⟨hW, hWhead, hWlastopt⟩ hWout hWodd huT hvT
  have hcomplete_unique : ∀ z ∈ W, VertexComplete Gᶜ z T → z = u ∨ z = v := by
    intro z hz hc
    simp [W] at hz
    rcases hz with hz | hz | hz | hz
    · exact Or.inl hz
    · subst z
      have hmem : p[s] ∈ T := mem_drop_of_index hslt le_rfl
      have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hp (i := s - 1) (by omega)
      have heq : s - 1 + 1 = s := by omega
      have hadj' : G.Adj p[s - 1] p[s] := by simpa only [heq] using hadj
      exact False.elim (((G.compl_adj _ _).1 (hc _ hmem)).2 hadj')
    · obtain ⟨zR, hzR, hzzR⟩ := hqright z hz
      have hzRT : zR ∈ T := by
        obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzR
        exact hiz ▸ mem_drop_of_index hi (by omega)
      exact False.elim (((G.compl_adj _ _).1 (hc zR hzRT)).2 hzzR)
    · exact Or.inr hz
  have hleap : 5 ≤ pathLength W ∧ ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath Gᶜ W a b := by
    rcases h21 with hedge | hleap | hshort
    · obtain ⟨a, haW, b, hbW, hab, haT, hbT⟩ := hedge
      rcases hcomplete_unique a haW haT with rfl | rfl <;>
        rcases hcomplete_unique b hbW hbT with rfl | rfl
      · exact False.elim ((Gᶜ).irrefl hab)
      · exact False.elim (huv hab)
      · exact False.elim (huv hab.symm)
      · exact False.elim ((Gᶜ).irrefl hab)
    · exact hleap
    · have hpathlen : pathLength W = n + 2 := by simp [pathLength, hWlen]
      omega
  obtain ⟨-, a, haT, b, hbT, hleap⟩ := hleap
  obtain ⟨-, -, habne, habnc, haadj, hbadj⟩ := hleap
  obtain ⟨ia, hia, hsia, hiaeq⟩ := mem_drop_index haT
  obtain ⟨ib, hib, hsib, hibeq⟩ := mem_drop_index hbT
  have hbps_ne : b ≠ p[s - 1] := by
    intro he
    apply hWout (p[s - 1])
    · simp [W]
    · exact he ▸ hbT
  have hbps_nc : ¬ Gᶜ.Adj b p[s - 1] := by
    intro hadj
    rw [← hW1] at hadj
    rcases (hbadj 1 (by omega)).mp hadj with h | h | h <;> omega
  have hbps : G.Adj b p[s - 1] := adj_of_not_compl_adj hbps_ne hbps_nc
  have hib_eq : ib = s := by
    rw [← hibeq] at hbps
    rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hib hsm1lt).mp hbps with h | h <;>
      omega
  subst ib
  have habG : G.Adj a b := adj_of_not_compl_adj habne habnc
  have hia_eq : ia = s + 1 := by
    rw [← hiaeq, ← hibeq] at habG
    rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hia hib).mp habG with h | h <;>
      omega
  subst ia
  -- We now have `u=p[s-3]`, `v=p[s-2]`, `b=p[s]`, and `a=p[s+1]`.
  have hqnd : q.Nodup := by
    have htail : (q ++ [p[s]]).Nodup := hQ.1.2.1.tail
    exact (List.nodup_append.mp htail).1
  have hWq : ∀ (j : ℕ) (hj : j < q.length), W[j + 2]'(by
      rw [hWlen]; omega) = q[j]'hj := by
    intro j hj
    simpa only [W] using get_q_in_left_path u p[s - 1] v q hj
  have hindex_pattern : ∀ (k : ℕ) (hk : k < p.length), s - 3 ≤ k → k ≤ s + 1 →
      ∀ (j : ℕ) (hj : j < q.length),
        (¬ G.Adj (p[k]'hk) (q[j]'hj) ↔
          (k = s - 2 ∧ j = n - 1) ∨ (k = s - 1 ∧ j = 0) ∨
            (k = s ∧ j = n - 1)) := by
    intro k hk hkl hku j hj
    have hjW : j + 2 < W.length := by rw [hWlen]; omega
    have hqyW : q[j]'hj ∈ W := by
      rw [← hWq j hj]
      exact List.getElem_mem hjW
    have hpxqy_ne : p[k]'hk ≠ q[j]'hj := by
      by_cases hkt : s ≤ k
      · intro he
        have hpkT : p[k]'hk ∈ T := mem_drop_of_index hk hkt
        exact hWout _ hqyW (he ▸ hpkT)
      · have hkcases : k = s - 3 ∨ k = s - 2 ∨ k = s - 1 := by omega
        rcases hkcases with hk0 | hk0 | hk0
        · subst k
          have hne := Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hW
            (i := 0) (j := j + 2) (by omega) hjW (by omega)
          intro he
          exact hne (by simpa only [hW0, hWq j hj, hiueq] using he)
        · subst k
          have hne := Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hW
            (i := n + 2) (j := j + 2) (by omega) hjW (by omega)
          intro he
          exact hne (by simpa only [hWlast, hWq j hj, hqn, hiveq] using he)
        · subst k
          have hne := Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hW
            (i := 1) (j := j + 2) (by omega) hjW (by omega)
          intro he
          exact hne (by simpa only [hW1, hWq j hj] using he)
    have hnonedge : ¬ G.Adj (p[k]'hk) (q[j]'hj) ↔ Gᶜ.Adj (p[k]'hk) (q[j]'hj) := by
      constructor
      · exact fun hn => (G.compl_adj _ _).2 ⟨hpxqy_ne, hn⟩
      · exact fun hc => ((G.compl_adj _ _).1 hc).2
    have hkcases : k = s - 3 ∨ k = s - 2 ∨ k = s - 1 ∨ k = s ∨ k = s + 1 := by
      omega
    rcases hkcases with hk0 | hk0 | hk0 | hk0 | hk0
    · subst k
      rw [hnonedge]
      have hpath := Workspace.ProofLemmas.PathBasics.path_adj_iff hW
        (i := 0) (j := j + 2) (by omega) hjW
      have hpath' : Gᶜ.Adj p[s - 3] q[j] ↔
          (0 + 1 = j + 2 ∨ j + 2 + 1 = 0) := by
        simpa only [hW0, hWq j hj, hiueq] using hpath
      rw [hpath']
      omega
    · subst k
      rw [hnonedge]
      have hpath := Workspace.ProofLemmas.PathBasics.path_adj_iff hW
        (i := n + 2) (j := j + 2) (by omega) hjW
      have hpath' : Gᶜ.Adj p[s - 2] q[j] ↔
          (n + 2 + 1 = j + 2 ∨ j + 2 + 1 = n + 2) := by
        simpa only [hWlast, hWq j hj, hiveq] using hpath
      rw [hpath']
      omega
    · subst k
      rw [hnonedge]
      have hpath := Workspace.ProofLemmas.PathBasics.path_adj_iff hW
        (i := 1) (j := j + 2) (by omega) hjW
      have hpath' : Gᶜ.Adj p[s - 1] q[j] ↔
          (1 + 1 = j + 2 ∨ j + 2 + 1 = 1) := by
        simpa only [hW1, hWq j hj] using hpath
      rw [hpath']
      omega
    · subst k
      rw [hnonedge]
      have hadj := hbadj (j + 2) hjW
      have hadj' : Gᶜ.Adj p[s] q[j] ↔
          (j + 2 = 0 ∨ j + 2 = W.length - 2 ∨ j + 2 = W.length - 1) := by
        simpa only [hibeq, hWq j hj] using hadj
      rw [hadj']
      rw [hWlen]
      omega
    · subst k
      rw [hnonedge]
      have hadj := haadj (j + 2) hjW
      have hadj' : Gᶜ.Adj p[s + 1] q[j] ↔
          (j + 2 = 0 ∨ j + 2 = 1 ∨ j + 2 = W.length - 1) := by
        simpa only [hiaeq, hWq j hj] using hadj
      rw [hadj']
      rw [hWlen]
      omega
  refine ⟨hs3, ?_⟩
  intro x hx y hy
  have hx' : x ∈ (p.drop (s - 3)).take (s + 1 - (s - 3) + 1) := by
    simpa only [show s + 1 - (s - 3) + 1 = 5 by omega] using hx
  obtain ⟨k, hk, hkl, hku, hkx⟩ :=
    (Workspace.ProofLemmas.PathBasics.mem_slice_iff p (i := s - 3) (j := s + 1)
      (by omega) hsp1lt).mp hx'
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy
  have hind := hindex_pattern k hk hkl hku j hj
  constructor
  · intro hnon
    have hcases := hind.mp (by simpa only [hkx, hjy] using hnon)
    rcases hcases with ⟨hk0, hj0⟩ | ⟨hk0, hj0⟩ | ⟨hk0, hj0⟩
    · left
      constructor
      · rw [← hkx]
        exact hp.2.1.getElem_inj_iff.mpr hk0
      · rw [← hjy]
        exact hqnd.getElem_inj_iff.mpr (by omega)
    · right; left
      constructor
      · rw [← hkx]
        exact hp.2.1.getElem_inj_iff.mpr hk0
      · rw [← hjy]
        exact hqnd.getElem_inj_iff.mpr (by omega)
    · right; right
      constructor
      · rw [← hkx]
        exact hp.2.1.getElem_inj_iff.mpr hk0
      · rw [← hjy]
        exact hqnd.getElem_inj_iff.mpr (by omega)
  · intro hcases
    have hi : (k = s - 2 ∧ j = n - 1) ∨ (k = s - 1 ∧ j = 0) ∨
        (k = s ∧ j = n - 1) := by
      rcases hcases with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩
      · left
        constructor
        · exact hp.2.1.getElem_inj_iff.mp (hkx.trans hx0)
        · exact hqnd.getElem_inj_iff.mp (hjy.trans hy0)
      · right; left
        constructor
        · exact hp.2.1.getElem_inj_iff.mp (hkx.trans hx0)
        · exact hqnd.getElem_inj_iff.mp (hjy.trans hy0)
      · right; right
        constructor
        · exact hp.2.1.getElem_inj_iff.mp (hkx.trans hx0)
        · exact hqnd.getElem_inj_iff.mp (hjy.trans hy0)
    simpa only [hkx, hjy] using hind.mpr hi

end Workspace.ProofLemmas.Thm32OneSided
