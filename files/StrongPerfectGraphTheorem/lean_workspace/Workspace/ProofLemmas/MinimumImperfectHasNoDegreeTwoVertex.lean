import Workspace.Types.Core
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect
import Workspace.ProofLemmas.MinimumImperfectNotCliqueNumColorable
import Workspace.ProofLemmas.IsoTransport
import Workspace.Statements.S01.Thm_E5_perfect_implies_berge

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT

/-- A Berge graph which is not bipartite contains a triangle. -/
private theorem berge_nonbipartite_has_triangle {V : Type*}
    (G : SimpleGraph V) (hB : Berge G) (hnb : ¬ G.IsBipartite) :
    ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by
  classical
  have hodd : ∃ (x : V) (q : G.Walk x x), Odd q.length := by
    by_contra hcon
    push Not at hcon
    exact hnb (SimpleGraph.two_colorable_iff_forall_loop_even.2
      (fun x q => Nat.not_odd_iff_even.mp (hcon x q)))
  have hexP : ∃ m : ℕ, ∃ (x : V) (q : G.Walk x x), q.length = m ∧ Odd m := by
    obtain ⟨x, q, hq⟩ := hodd
    exact ⟨q.length, x, q, rfl, hq⟩
  obtain ⟨n, ⟨u, w, hwlen, hnodd⟩, hmin⟩ :
      ∃ n : ℕ, (∃ (x : V) (q : G.Walk x x), q.length = n ∧ Odd n) ∧
        (∀ (x : V) (q : G.Walk x x), Odd q.length → n ≤ q.length) := by
    refine ⟨Nat.find hexP, Nat.find_spec hexP, ?_⟩
    intro x q hq
    exact Nat.find_min' hexP ⟨x, q, rfl, hq⟩
  have hpar : n % 2 = 1 := Nat.odd_iff.mp hnodd
  have hu0 : w.getVert 0 = u := w.getVert_zero
  have hun : w.getVert n = u := by rw [← hwlen]; exact w.getVert_length
  have hadjsucc : ∀ i, i < n → G.Adj (w.getVert i) (w.getVert (i + 1)) := by
    intro i hi
    exact w.adj_getVert_succ (by omega)
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    have h1 : G.Adj (w.getVert 0) (w.getVert 1) := hadjsucc 0 (by omega)
    rw [hu0, show (1 : ℕ) = n from hn1.symm, hun] at h1
    exact G.irrefl h1
  have hseg : ∀ i j : ℕ, i ≤ j → j ≤ n →
      ∃ q : G.Walk (w.getVert i) (w.getVert j), q.length = j - i := by
    intro i j hij hjn
    refine ⟨((w.drop i).take (j - i)).copy rfl ?_, ?_⟩
    · rw [SimpleGraph.Walk.drop_getVert]
      congr 1
      omega
    · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
        SimpleGraph.Walk.drop_length, hwlen]
      omega
  have hrest : ∀ i j : ℕ, i ≤ n → j ≤ n →
      ∃ q : G.Walk (w.getVert j) (w.getVert i), q.length = n - j + i := by
    intro i j hin hjn
    refine ⟨(w.drop j).append (w.take i), ?_⟩
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.drop_length,
      SimpleGraph.Walk.take_length, hwlen]
    omega
  have hinj : ∀ i j : ℕ, i < j → j < n → w.getVert i ≠ w.getVert j := by
    intro i j hij hjn heq
    obtain ⟨qa, hqa⟩ := hseg i j (le_of_lt hij) (by omega)
    obtain ⟨qb, hqb⟩ := hrest i j (by omega) (by omega)
    have hcase : (j - i) % 2 = 1 ∨ (n - j + i) % 2 = 1 := by omega
    rcases hcase with h | h
    · have hle := hmin _ (qa.copy rfl heq.symm)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_copy, hqa]; exact h))
      rw [SimpleGraph.Walk.length_copy, hqa] at hle
      omega
    · have hle := hmin _ (qb.copy heq.symm rfl)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_copy, hqb]; exact h))
      rw [SimpleGraph.Walk.length_copy, hqb] at hle
      omega
  have hchord : ∀ i j : ℕ, i < j → j < n → G.Adj (w.getVert i) (w.getVert j) →
      (j = i + 1 ∨ (i = 0 ∧ j = n - 1)) := by
    intro i j hij hjn hadj
    by_contra hcon
    have hne1 : j ≠ i + 1 := fun h => hcon (Or.inl h)
    have hne2 : ¬ (i = 0 ∧ j = n - 1) := fun h => hcon (Or.inr h)
    obtain ⟨qa, hqa⟩ := hseg i j (le_of_lt hij) (by omega)
    obtain ⟨qb, hqb⟩ := hrest i j (by omega) (by omega)
    have hcase : (j - i + 1) % 2 = 1 ∨ (n - j + i + 1) % 2 = 1 := by omega
    rcases hcase with h | h
    · have hle := hmin _ (qa.concat hadj.symm)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_concat, hqa]; exact h))
      rw [SimpleGraph.Walk.length_concat, hqa] at hle
      omega
    · have hle := hmin _ (qb.concat hadj)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_concat, hqb]; exact h))
      rw [SimpleGraph.Walk.length_concat, hqb] at hle
      omega
  have hu0n : w.getVert n = w.getVert 0 := hun.trans hu0.symm
  have hwrap : G.Adj (w.getVert (n - 1)) (w.getVert 0) := by
    have h := hadjsucc (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, hu0n] at h
    exact h
  have hmod : ∀ k : ℕ, k < n → (k + 1) % n = if k + 1 = n then 0 else k + 1 := by
    intro k hk
    by_cases hh : k + 1 = n
    · simp [hh]
    · rw [if_neg hh, Nat.mod_eq_of_lt (by omega)]
  have hLnd0 : ((List.range n).map w.getVert).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hinj x y h hy hxy
    · exact hinj y x h hx hxy.symm
  obtain ⟨L, hclen, hcnd, hcget⟩ : ∃ L : List V, L.length = n ∧ L.Nodup ∧
      ∀ (i : ℕ) (hi : i < L.length), (L[i]'hi) = w.getVert i :=
    ⟨(List.range n).map w.getVert, by simp, hLnd0, by intro i hi; simp⟩
  have hcadj : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length),
      (G.Adj (L[i]'hi) (L[j]'hj) ↔ (j = (i + 1) % L.length ∨ i = (j + 1) % L.length)) := by
    intro i j hi hj
    have hi' : i < n := by omega
    have hj' : j < n := by omega
    rw [hcget i hi, hcget j hj, hclen, hmod i hi', hmod j hj']
    constructor
    · intro hadj
      have hne : i ≠ j := by
        rintro rfl
        exact G.irrefl hadj
      rcases lt_or_gt_of_ne hne with h | h
      · rcases hchord i j h hj' hadj with h1 | ⟨h1, h2⟩
        · left; split_ifs <;> omega
        · right; split_ifs <;> omega
      · rcases hchord j i h hi' hadj.symm with h1 | ⟨h1, h2⟩
        · right; split_ifs <;> omega
        · left; split_ifs <;> omega
    · intro hcyc
      split_ifs at hcyc with h1 h2 h2
      · exfalso; omega
      · rcases hcyc with h | h
        · rw [h, show i = n - 1 by omega]; exact hwrap
        · rw [h]; exact (hadjsucc j hj').symm
      · rcases hcyc with h | h
        · rw [h]; exact hadjsucc i hi'
        · rw [h, show j = n - 1 by omega]; exact hwrap.symm
      · rcases hcyc with h | h
        · rw [h]; exact hadjsucc i hi'
        · rw [h]; exact (hadjsucc j hj').symm
  have hn3' : n = 3 := by
    by_contra hne
    have hhole : IsHoleList G L := ⟨by omega, hcnd, hcadj⟩
    have heven := hB.1 L hhole
    rw [holeLength, hclen] at heven
    rw [Nat.even_iff] at heven
    omega
  refine ⟨w.getVert 0, w.getVert 1, w.getVert 2, by simpa using hadjsucc 0 (by omega),
    by simpa using hadjsucc 1 (by omega), ?_⟩
  have h := hadjsucc 2 (by omega)
  rw [show (2 : ℕ) + 1 = n by omega, hu0n] at h
  exact h

/-- A minimum imperfect graph has no vertex with exactly two neighbors. -/
theorem MinimumImperfectHasNoDegreeTwoVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hG : SPGT.MinimumImperfect G) :
    ∀ v : V, (G.neighborSet v).ncard ≠ 2 := by
  classical
  intro v hv
  obtain ⟨a, b, hab, hN⟩ := Set.ncard_eq_two.mp hv
  have hva : G.Adj v a := by
    rw [← SimpleGraph.mem_neighborSet, hN]
    simp
  have hvb : G.Adj v b := by
    rw [← SimpleGraph.mem_neighborSet, hN]
    simp
  have htwo : 2 ≤ G.cliqueNum := by
    have hpairSet : G.IsClique ({v, a} : Set V) :=
      SimpleGraph.isClique_pair.mpr (fun _ => hva)
    have hpair : G.IsClique (↑({v, a} : Finset V) : Set V) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hpairSet
    simpa [hva.ne] using hpair.card_le_cliqueNum
  have hnotbip : ¬ G.IsBipartite := by
    intro hbip
    obtain ⟨K, hK⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := G)
    have hupper : G.cliqueNum ≤ 2 := by
      rw [← hK.card_eq]
      exact hK.isClique.card_le_of_colorable hbip
    have homega : G.cliqueNum = 2 := le_antisymm hupper htwo
    exact MinimumImperfectNotCliqueNumColorable.not_colorable_cliqueNum hG
      (by simpa [homega] using hbip)
  have hBerge : Berge G :=
    IsoTransport.minimumImperfect_berge hG
      (fun hp => Workspace.MainTheorem.SPGT.thm_E5_perfect_implies_berge G hp)
  obtain ⟨x, y, z, hxy, hyz, hzx⟩ := berge_nonbipartite_has_triangle G hBerge hnotbip
  have hthree : 3 ≤ G.cliqueNum := by
    have ht : G.IsNClique 3 ({x, y, z} : Finset V) :=
      SimpleGraph.is3Clique_iff.mpr ⟨x, y, z, hxy, hzx.symm, hyz, rfl⟩
    rw [← ht.card_eq]
    exact ht.isClique.card_le_cliqueNum
  let X : Set V := {w | w ≠ v}
  have hXproper : X ≠ Set.univ := by
    intro h
    have : v ∈ X := h ▸ Set.mem_univ v
    exact this rfl
  have hperfX : IsPerfect (G.induce X) :=
    SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hXproper
  have homegaX : (G.induce X).cliqueNum ≤ G.cliqueNum := by
    calc
      (G.induce X).cliqueNum ≤ (G.induce Set.univ).cliqueNum :=
        CliqueNumOfInducedSet.cliqueNum_induce_mono G (Set.subset_univ X)
      _ = G.cliqueNum := IsoTransport.cliqueNum_iso (SimpleGraph.induceUnivIso G)
  obtain ⟨cX⟩ : (G.induce X).Colorable G.cliqueNum :=
    SimpleGraph.Colorable.mono homegaX
      (CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect (G.induce X) hperfX)
  have hav : a ≠ v := fun h => G.irrefl (h ▸ hva.symm)
  have hbv : b ≠ v := fun h => G.irrefl (h ▸ hvb.symm)
  let aX : X := ⟨a, hav⟩
  let bX : X := ⟨b, hbv⟩
  obtain ⟨fresh, hfreshA, hfreshB⟩ :=
    Fin.exists_ne_and_ne_of_two_lt (cX aX) (cX bX) hthree
  let color : V → Fin G.cliqueNum := fun w =>
    if hw : w = v then fresh else cX ⟨w, hw⟩
  have hcolor : G.Colorable G.cliqueNum := by
    refine ⟨SimpleGraph.Coloring.mk color ?_⟩
    intro p q hpq
    by_cases hp : p = v
    · subst p
      have hqN : q ∈ G.neighborSet v := (SimpleGraph.mem_neighborSet G v q).mpr hpq
      rw [hN] at hqN
      rcases hqN with hqa | hqb
      · subst q
        dsimp only [color]
        rw [dif_pos rfl, dif_neg hav]
        change fresh ≠ cX aX
        exact hfreshA
      · have : q = b := by simpa using hqb
        subst q
        dsimp only [color]
        rw [dif_pos rfl, dif_neg hbv]
        change fresh ≠ cX bX
        exact hfreshB
    · by_cases hq : q = v
      · subst q
        have hpN : p ∈ G.neighborSet v := (SimpleGraph.mem_neighborSet G v p).mpr hpq.symm
        rw [hN] at hpN
        rcases hpN with hpa | hpb
        · subst p
          dsimp only [color]
          rw [dif_neg hav, dif_pos rfl]
          change cX aX ≠ fresh
          exact hfreshA.symm
        · have : p = b := by simpa using hpb
          subst p
          dsimp only [color]
          rw [dif_neg hbv, dif_pos rfl]
          change cX bX ≠ fresh
          exact hfreshB.symm
      · simp only [color, hp, hq, dite_false]
        exact cX.valid hpq
  exact MinimumImperfectNotCliqueNumColorable.not_colorable_cliqueNum hG hcolor

end Workspace.ProofLemmas
