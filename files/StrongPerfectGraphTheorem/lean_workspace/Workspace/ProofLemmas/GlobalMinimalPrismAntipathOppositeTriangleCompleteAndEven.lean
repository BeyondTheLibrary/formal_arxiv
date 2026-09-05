import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathAttach

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

theorem saturation_forbids_two_misses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Fin 3 → V) (y : V)
    (hsat : 2 ≤ (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y).ncard)
    (i j : Fin 3) (hij : i ≠ j)
    (hi : ¬ G.Adj (c i) y) (hj : ¬ G.Adj (c j) y) : False := by
  have hsmall :
      (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y).ncard ≤ 1 := by
    rcases HyperprismBasics.fin3_cases i with rfl | rfl | rfl <;>
      rcases HyperprismBasics.fin3_cases j with rfl | rfl | rfl
    · exact absurd rfl hij
    · have hsub : (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y) ⊆ {c 2} := by
        rintro x ⟨hx, hxy⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact (hi (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · exact (hj (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · rfl
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (c 2))
      simpa using this
    · have hsub : (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y) ⊆ {c 1} := by
        rintro x ⟨hx, hxy⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact (hi (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · rfl
        · exact (hj (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (c 1))
      simpa using this
    · have hsub : (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y) ⊆ {c 2} := by
        rintro x ⟨hx, hxy⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact (hj (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · exact (hi (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · rfl
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (c 2))
      simpa using this
    · exact absurd rfl hij
    · have hsub : (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y) ⊆ {c 0} := by
        rintro x ⟨hx, hxy⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · rfl
        · exact (hi (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · exact (hj (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (c 0))
      simpa using this
    · have hsub : (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y) ⊆ {c 1} := by
        rintro x ⟨hx, hxy⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact (hj (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · rfl
        · exact (hi (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (c 1))
      simpa using this
    · have hsub : (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet y) ⊆ {c 0} := by
        rintro x ⟨hx, hxy⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · rfl
        · exact (hj (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
        · exact (hi (by simpa [SimpleGraph.mem_neighborSet] using hxy.symm)).elim
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (c 0))
      simpa using this
    · exact absurd rfl hij
  omega

private theorem path_ends_nonadj_of_length_ge_two
    {V : Type*} {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (hlen : 2 ≤ pathLength p) : ¬ G.Adj u v := by
  intro hadj
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hlast : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hadj' : G.Adj (p[0]'hpos) (p[p.length - 1]'(by omega)) := by
    simpa [h0, hlast] using hadj
  have hidx := (PathBasics.path_adj_iff hp.1 hpos (by omega)).mp hadj'
  rw [pathLength] at hlen
  omega

theorem GlobalMinimalPrismAntipathOppositeTriangleCompleteAndEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (Y : Set V)
    (alpha beta : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V)
    (hprism : FormPrism G alpha beta (R 0) (R 1) (R 2))
    (hRoutside : ∀ i v, v ∈ R i → v ∉ Y)
    (hRlength : ∀ i, 1 < pathLength (R i))
    (hYmajor : ∀ y ∈ Y, MajorForPrism G alpha beta y)
    (hQ : Q = alpha 0 :: (q ++ [alpha 1]))
    (hQantipath : IsAntipathFrom G Q (alpha 0) (alpha 1))
    (hqY : ∀ x ∈ q, x ∈ Y)
    (halpha0 : ¬ VertexComplete G (alpha 0) Y)
    (halpha1 : ¬ VertexComplete G (alpha 1) Y)
    (hminimal : ∀ (u v : V) (S : List V),
      u ≠ v →
      ((u ∈ ({alpha 0, alpha 1, alpha 2} : Set V) ∧
          v ∈ ({alpha 0, alpha 1, alpha 2} : Set V)) ∨
        (u ∈ ({beta 0, beta 1, beta 2} : Set V) ∧
          v ∈ ({beta 0, beta 1, beta 2} : Set V))) →
      ¬ VertexComplete G u Y →
      ¬ VertexComplete G v Y →
      IsAntipathFrom G S u v →
      (∀ x ∈ interior S, x ∈ Y) →
      pathLength Q ≤ pathLength S) :
    (∃ i : Fin 3, VertexComplete G (beta i) {x : V | x ∈ q}) ∧
      4 ≤ pathLength Q ∧ Even (pathLength Q) := by
  classical
  have hmajor_alpha : ∀ y ∈ Y, ∀ i j : Fin 3, i ≠ j →
      ¬ G.Adj (alpha i) y → ¬ G.Adj (alpha j) y → False := by
    intro y hy i j hij hi hj
    exact saturation_forbids_two_misses G alpha y (hYmajor y hy).1 i j hij hi hj
  have hmajor_beta : ∀ y ∈ Y, ∀ i j : Fin 3, i ≠ j →
      ¬ G.Adj (beta i) y → ¬ G.Adj (beta j) y → False := by
    intro y hy i j hij hi hj
    exact saturation_forbids_two_misses G beta y (hYmajor y hy).2 i j hij hi hj
  have hq_len_two : 2 ≤ q.length := by
    by_contra hn
    have hle : q.length ≤ 1 := by omega
    rcases q with _ | ⟨x, t⟩
    · have hlenQ : pathLength Q = 1 := by simp [hQ, pathLength]
      have hc := PathBasics.isPathFrom_ends_adj_of_length_one hQantipath hlenQ
      have htri := hprism.1 (0 : Fin 3) 1 (by decide)
      exact ((G.compl_adj _ _).mp hc).2 htri
    · rcases t with _ | ⟨z, t⟩
      · have hxY : x ∈ Y := hqY x (by simp)
        have hlenQ : Q.length = 3 := by simp [hQ]
        have hqx0 : ¬ G.Adj (alpha 0) x := by
          have hc : Gᶜ.Adj (alpha 0) x := by
            have hp := hQantipath.1
            have h0 : Q[0]'(by omega) = alpha 0 :=
              PathBasics.getElem_zero_of_head? hQantipath.2.1 (by omega)
            have h1 : Q[1]'(by omega) = x := by simp [hQ]
            rw [← h0, ← h1]
            exact (PathBasics.path_adj_iff hp (by omega) (by omega)).mpr (by omega)
          exact ((G.compl_adj _ _).mp hc).2
        have hqx1 : ¬ G.Adj (alpha 1) x := by
          have hc : Gᶜ.Adj (alpha 1) x := by
            have hp := hQantipath.1
            have h1 : Q[1]'(by omega) = x := by simp [hQ]
            have h2 : Q[2]'(by omega) = alpha 1 := by simp [hQ]
            rw [← h2, ← h1]
            exact (PathBasics.path_adj_iff hp (by omega) (by omega)).mpr (by omega)
          exact ((G.compl_adj _ _).mp hc).2
        exact hmajor_alpha x hxY 0 1 (by decide) hqx0 hqx1
      · simp at hle
  have hQ_len_four : 4 ≤ Q.length := by
    simp [hQ]
    omega
  have hQ_len_three : 3 ≤ pathLength Q := by
    simp [hQ, pathLength]
    omega
  have hex : ∃ i : Fin 3, VertexComplete G (beta i) {x : V | x ∈ q} := by
    by_contra hnone
    push Not at hnone
    have hbeta_notY_all : ∀ k : Fin 3, beta k ∉ Y := by
      intro k
      exact hRoutside k (beta k)
        (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path hprism k)).2
    let Bad : Fin 3 → ℕ → Prop :=
      fun k t => ∃ ht : t < q.length, ¬ G.Adj (beta k) (q[t]'ht)
    have hbad_exists : ∀ k : Fin 3, ∃ t : ℕ, Bad k t := by
      intro k
      have hnot : ¬ ∀ x ∈ q, G.Adj (beta k) x := by
        intro hall
        apply hnone k
        intro x hx
        exact hall x hx
      push Not at hnot
      obtain ⟨x, hxq, hxadj⟩ := hnot
      obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hxq
      refine ⟨t, ?_⟩
      dsimp [Bad]
      refine ⟨ht, ?_⟩
      rw [htx]
      exact hxadj
    have hbad_unique : ∀ (i j : Fin 3) (t : ℕ), i ≠ j →
        Bad i t → Bad j t → False := by
      intro i j t hij hbi hbj
      obtain ⟨ht, hni⟩ := hbi
      obtain ⟨ht', hnj⟩ := hbj
      have hty : q[t]'ht ∈ Y := hqY _ (List.getElem_mem ht)
      have hnj' : ¬ G.Adj (beta j) (q[t]'ht) := by simpa using hnj
      exact hmajor_beta _ hty i j hij hni hnj'
    let Pair : ℕ → Prop := fun e =>
      ∃ (i j : Fin 3) (r s : ℕ), i ≠ j ∧ r < s ∧ s - r = e ∧ Bad i r ∧ Bad j s
    have hpair_exists : ∃ e : ℕ, Pair e := by
      obtain ⟨r0, hr0⟩ := hbad_exists 0
      obtain ⟨r1, hr1⟩ := hbad_exists 1
      have h01 : r0 ≠ r1 := by
        intro h
        subst r1
        exact hbad_unique 0 1 r0 (by decide) hr0 hr1
      rcases lt_or_gt_of_ne h01 with hlt | hgt
      · refine ⟨r1 - r0, ?_⟩
        exact ⟨0, 1, r0, r1, by decide, hlt, rfl, hr0, hr1⟩
      · refine ⟨r0 - r1, ?_⟩
        exact ⟨1, 0, r1, r0, by decide, hgt, rfl, hr1, hr0⟩
    let d : ℕ := Nat.find hpair_exists
    have hd_spec : Pair d := Nat.find_spec hpair_exists
    obtain ⟨i, j, r, s, hij, hrs, hdist, hbr0, hbs0⟩ := hd_spec
    obtain ⟨hrlt, hnibr⟩ := hbr0
    obtain ⟨hslt, hnibs⟩ := hbs0
    have hbr : Bad i r := ⟨hrlt, hnibr⟩
    have hbs : Bad j s := ⟨hslt, hnibs⟩
    have hdmin : ∀ e : ℕ, Pair e → d ≤ e := by
      intro e he
      exact Nat.find_min' hpair_exists he
    have hno_bad_between : ∀ (k : Fin 3) (t : ℕ), r < t → t < s → ¬ Bad k t := by
      intro k t hrt hts hbt
      by_cases hki : k = i
      · subst k
        have hp : Pair (s - t) := ⟨i, j, t, s, hij, hts, rfl, hbt, hbs⟩
        have hle := hdmin (s - t) hp
        have hlt : s - t < d := by omega
        omega
      · have hp : Pair (t - r) := ⟨i, k, r, t, (fun h => hki h.symm), hrt, rfl, hbr, hbt⟩
        have hle := hdmin (t - r) hp
        have hlt : t - r < d := by omega
        omega
    have hthird : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      rcases HyperprismBasics.fin3_cases i with rfl | rfl | rfl <;>
        rcases HyperprismBasics.fin3_cases j with rfl | rfl | rfl
      · exact (hij rfl).elim
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact (hij rfl).elim
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact (hij rfl).elim
    obtain ⟨k, hki, hkj⟩ := hthird
    obtain ⟨t, htq, hnotkt⟩ := hbad_exists k
    have hbt : Bad k t := ⟨htq, hnotkt⟩
    have hproper : ¬ (r = 0 ∧ s = q.length - 1) := by
      rintro ⟨hr0, hsend⟩
      have htr : t ≠ r := by
        intro h
        subst t
        exact hbad_unique k i r hki hbt hbr
      have hts : t ≠ s := by
        intro h
        subst t
        exact hbad_unique k j s hkj hbt hbs
      have hrt : r < t := by omega
      have hts' : t < s := by omega
      exact hno_bad_between k t hrt hts' hbt
    have hqpath : IsPathList Gᶜ q := by
      have hslice := PathBasics.isPathList_slice hQantipath.1 (i := 1) (j := q.length)
        (by omega) (by simp [hQ])
      have hlen : q.length - 1 + 1 = q.length := by omega
      rw [hlen] at hslice
      simpa [hQ] using hslice
    have hp : IsPathFrom Gᶜ ((q.drop r).take (s - r + 1)) (q[r]'hrlt) (q[s]'hslt) :=
      PathBasics.isPathFrom_slice hqpath hrs hslt
    have hS : IsAntipathFrom G
        (beta i :: ((q.drop r).take (s - r + 1) ++ [beta j])) (beta i) (beta j) := by
      change IsPathFrom Gᶜ _ _ _
      refine PathAttach.isPathFrom_cons_concat hp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine (G.compl_adj _ _).mpr ⟨?_, hnibr⟩
        intro h
        apply hbeta_notY_all i
        rw [h]
        exact hqY _ (List.getElem_mem hrlt)
      · refine (G.compl_adj _ _).mpr ⟨?_, hnibs⟩
        intro h
        apply hbeta_notY_all j
        rw [h]
        exact hqY _ (List.getElem_mem hslt)
      · intro hc
        exact ((G.compl_adj _ _).mp hc).2 (hprism.2.1 i j hij)
      · exact (hprism.2.1 i j hij).ne
      · intro hx
        obtain ⟨u, hu, hru, hus, hux⟩ :=
          (PathBasics.mem_slice_iff q (i := r) (j := s) (x := beta i)
            (le_of_lt hrs) hslt).mp hx
        apply hbeta_notY_all i
        rw [← hux]
        exact hqY _ (List.getElem_mem hu)
      · intro hx
        obtain ⟨u, hu, hru, hus, hux⟩ :=
          (PathBasics.mem_slice_iff q (i := r) (j := s) (x := beta j)
            (le_of_lt hrs) hslt).mp hx
        apply hbeta_notY_all j
        rw [← hux]
        exact hqY _ (List.getElem_mem hu)
      · intro x hx hxne hcx
        have hni : ¬ G.Adj (beta i) x := ((G.compl_adj _ _).mp hcx).2
        obtain ⟨u, hu, hru, hus, hux⟩ :=
          (PathBasics.mem_slice_iff q (i := r) (j := s) (x := x)
            (le_of_lt hrs) hslt).mp hx
        have hbu : Bad i u := by
          refine ⟨hu, ?_⟩
          rw [hux]
          exact hni
        by_cases hur : u = r
        · subst u
          exact hxne (by simpa using hux.symm)
        by_cases hus' : u = s
        · subst u
          exact hbad_unique i j s hij hbu hbs
        exact hno_bad_between i u (by omega) (by omega) hbu
      · intro x hx hxne hcx
        have hni : ¬ G.Adj (beta j) x := ((G.compl_adj _ _).mp hcx).2
        obtain ⟨u, hu, hru, hus, hux⟩ :=
          (PathBasics.mem_slice_iff q (i := r) (j := s) (x := x)
            (le_of_lt hrs) hslt).mp hx
        have hbu : Bad j u := by
          refine ⟨hu, ?_⟩
          rw [hux]
          exact hni
        by_cases hus' : u = s
        · subst u
          exact hxne (by simpa using hux.symm)
        by_cases hur : u = r
        · subst u
          exact hbad_unique i j r hij hbr hbu
        exact hno_bad_between j u (by omega) (by omega) hbu
    have hSint : ∀ x ∈ Workspace.Types.Core.SPGT.interior
        (beta i :: ((q.drop r).take (s - r + 1) ++ [beta j])), x ∈ Y := by
      intro x hx
      have hxp : x ∈ (q.drop r).take (s - r + 1) := by
        simpa [Workspace.Types.Core.SPGT.interior] using hx
      obtain ⟨u, hu, hru, hus, hux⟩ :=
        (PathBasics.mem_slice_iff q (i := r) (j := s) (x := x)
          (le_of_lt hrs) hslt).mp hxp
      rw [← hux]
      exact hqY _ (List.getElem_mem hu)
    have hbeta_tri : ∀ k : Fin 3, beta k ∈ ({beta 0, beta 1, beta 2} : Set V) := by
      intro k
      rcases HyperprismBasics.fin3_cases k with rfl | rfl | rfl <;> simp
    have hbeta_not_complete_Y : ∀ k : Fin 3, ¬ VertexComplete G (beta k) Y := by
      intro k hk
      apply hnone k
      intro x hx
      exact hk x (hqY x hx)
    have hmin := hminimal (beta i) (beta j)
      (beta i :: ((q.drop r).take (s - r + 1) ++ [beta j]))
      (hprism.2.1 i j hij).ne (Or.inr ⟨hbeta_tri i, hbeta_tri j⟩)
      (hbeta_not_complete_Y i) (hbeta_not_complete_Y j) hS hSint
    have hSlen : pathLength (beta i :: ((q.drop r).take (s - r + 1) ++ [beta j])) =
        s - r + 2 := by
      rw [PathAttach.pathLength_cons_append_singleton]
      rw [PathBasics.length_slice q (le_of_lt hrs) hslt]
    have hQlen : pathLength Q = q.length + 1 := by
      simp [hQ, pathLength]
    have hshortlen : s - r + 2 < q.length + 1 := by
      by_contra hn
      apply hproper
      constructor <;> omega
    have hshort : pathLength
        (beta i :: ((q.drop r).take (s - r + 1) ++ [beta j])) < pathLength Q := by
      rw [hSlen, hQlen]
      exact hshortlen
    exact (Nat.not_lt_of_ge hmin) hshort
  obtain ⟨i, hi⟩ := hex
  have hbeta_mem : beta i ∈ R i :=
    (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path hprism i)).2
  have hbeta_notY : beta i ∉ Y := hRoutside i (beta i) hbeta_mem
  have hbeta_notQ : beta i ∉ Q := by
    intro hmem
    have hmem' : beta i = alpha 0 ∨ beta i ∈ q ∨ beta i = alpha 1 := by
      simpa [hQ] using hmem
    rcases hmem' with hba | hq | hbb
    · exact hprism.2.2.1 0 i hba.symm
    · exact hbeta_notY (hqY _ hq)
    · exact hprism.2.2.1 1 i hbb.symm
  have hbeta_ne_a0 : beta i ≠ alpha 0 := fun h => hprism.2.2.1 0 i h.symm
  have hbeta_ne_a1 : beta i ≠ alpha 1 := fun h => hprism.2.2.1 1 i h.symm
  have hbeta_nonadj_a0 : ¬ G.Adj (beta i) (alpha 0) := by
    by_cases hi0 : i = 0
    · subst i
      intro hadj
      have hlen : 2 ≤ pathLength (R 0) := by
        have h := hRlength 0
        omega
      exact path_ends_nonadj_of_length_ge_two
        (HyperprismFromPrism.formPrism_path hprism 0) hlen hadj.symm
    · intro hadj
      have hcross := HyperprismFromPrism.formPrism_cross hprism
        (i := 0) (j := i) (fun h => hi0 h.symm)
        (alpha 0)
        (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path hprism 0)).1
        (beta i) hbeta_mem
      rcases (hcross.mp hadj.symm) with ⟨_, hv⟩ | ⟨hu, _⟩
      · exact hprism.2.2.1 i i hv.symm
      · exact hprism.2.2.1 0 0 hu
  have hbeta_nonadj_a1 : ¬ G.Adj (beta i) (alpha 1) := by
    by_cases hi1 : i = 1
    · subst i
      intro hadj
      have hlen : 2 ≤ pathLength (R 1) := by
        have h := hRlength 1
        omega
      exact path_ends_nonadj_of_length_ge_two
        (HyperprismFromPrism.formPrism_path hprism 1) hlen hadj.symm
    · intro hadj
      have hcross := HyperprismFromPrism.formPrism_cross hprism
        (i := 1) (j := i) (fun h => hi1 h.symm)
        (alpha 1)
        (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path hprism 1)).1
        (beta i) hbeta_mem
      rcases (hcross.mp hadj.symm) with ⟨_, hv⟩ | ⟨hu, _⟩
      · exact hprism.2.2.1 i i hv.symm
      · exact hprism.2.2.1 1 1 hu
  have hbeta_int : ∀ x ∈ Workspace.Types.Core.SPGT.interior Q, G.Adj (beta i) x := by
    intro x hx
    have hxq : x ∈ q := by
      rw [hQ] at hx
      simpa [Workspace.Types.Core.SPGT.interior] using hx
    exact hi x hxq
  have heven_succ := PrismBasics.even_of_antipath_closed_by_vertex' hG hQantipath
    hQ_len_four hbeta_notQ hbeta_ne_a0 hbeta_ne_a1 hbeta_nonadj_a0
    hbeta_nonadj_a1 hbeta_int
  obtain ⟨k, hk⟩ := heven_succ
  have heven : Even (pathLength Q) := by
    refine ⟨k - 1, ?_⟩
    rw [PathBasics.length_eq_pathLength_add_one hQantipath.1] at hk
    omega
  refine ⟨⟨i, hi⟩, ?_, heven⟩
  rcases heven with ⟨m, hm⟩
  omega

end Workspace.ProofLemmas
