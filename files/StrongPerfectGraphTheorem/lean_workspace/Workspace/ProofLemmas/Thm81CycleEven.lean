import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.CyclicPathConcatenationIsHole

/-!
# The rungs along a cycle of `J` induce a hole of `G`

This is the middle of the printed proof of 8.1 (printed p. 40):

PAPER: *"For each `xy ∈ E(C)` different from `uv`, choose an `xy`-rung `R_xy`.  For every
`uv`-rung `R`, the union of `V(R)` and all the `V(R_xy)`'s induces a cycle in `G`.  This has
length `≥ 4` since `C` has length `≥ 4`, so it is a hole and therefore even."*

The cycle in `G` obtained by walking around `C` and traversing the chosen rung of each edge of
`C` in turn has one vertex for each vertex of each rung, so its length (= its number of
vertices) is

`∑_{xy ∈ E(C)} |V(R_xy)| = ∑_{xy ∈ E(C)} (pathLength (R_xy) + 1)
   = (∑_{xy ∈ E(C)} pathLength (R_xy)) + |V(C)|`

(there being one edge of `C` per vertex of `C`).  Since `G` is Berge and this cycle is a hole,
that number is even, which is the statement below.

The consecutive pairs of `C` are `c.zip (c.rotate 1)`, exactly as in the seventh axiom of a
`J`-strip system, and give each edge of `C` once.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm81CycleEven

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- *"the union of `V(R)` and all the `V(R_xy)`'s induces a cycle in `G`.  This has length
`≥ 4` since `C` has length `≥ 4`, so it is a hole and therefore even."*

The hole's length is `∑_{xy ∈ E(C)} pathLength (R_xy) + |V(C)|`. -/
theorem even_cycle_sum {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (C : List U) (hlen : 4 ≤ C.length) (hnd : C.Nodup)
    (hadj : ∀ p ∈ C.zip (C.rotate 1), J.Adj p.1 p.2)
    (R : U → U → List V)
    (hR : ∀ p ∈ C.zip (C.rotate 1), IsUVRung G J S N p.1 p.2 (R p.1 p.2)) :
    Even (((C.zip (C.rotate 1)).map (fun p => pathLength (R p.1 p.2))).sum + C.length) := by
  classical
  let next : ℕ → ℕ := fun i => (i + 1) % C.length
  have hcpos : 0 < C.length := by omega
  have hnext_lt (i : ℕ) : next i < C.length := by
    exact Nat.mod_lt _ hcpos
  have hnext_formula (i : ℕ) (hi : i < C.length) :
      next i = if i + 1 = C.length then 0 else i + 1 := by
    by_cases hlast : i + 1 = C.length
    · simp [next, hlast]
    · simp only [next]
      rw [if_neg hlast, Nat.mod_eq_of_lt (by omega)]
  have hnext_ne (i : ℕ) (hi : i < C.length) : next i ≠ i := by
    rw [hnext_formula i hi]
    split_ifs <;> omega
  have hnext_inj (i j : ℕ) (hi : i < C.length) (hj : j < C.length)
      (heq : next i = next j) : i = j := by
    rw [hnext_formula i hi, hnext_formula j hj] at heq
    split_ifs at heq <;> omega
  have hnext_next_ne (i : ℕ) (hi : i < C.length) : next (next i) ≠ i := by
    intro heq
    have hni := hnext_lt i
    rw [hnext_formula (next i) hni, hnext_formula i hi] at heq
    split_ifs at heq <;> omega
  have cne (i j : ℕ) (hi : i < C.length) (hj : j < C.length) (hij : i ≠ j) :
      (C[i]'hi) ≠ (C[j]'hj) := by
    intro heq
    exact hij ((List.Nodup.getElem_inj_iff hnd).mp heq)

  let E : List (U × U) := C.zip (C.rotate 1)
  have hElen : E.length = C.length := by simp [E]
  have hEget (i : ℕ) (hi : i < C.length) :
      E[i]'(by omega) = (C[i]'hi, C[next i]'(hnext_lt i)) := by
    simp only [E, List.getElem_zip]
    rw [List.getElem_rotate]
  have hadjAt (i : ℕ) (hi : i < C.length) :
      J.Adj (C[i]'hi) (C[next i]'(hnext_lt i)) := by
    have hmE : E[i]'(by omega) ∈ E := List.getElem_mem (l := E) (n := i) (by omega)
    have h := hadj (E[i]'(by omega)) (by simpa only [E] using hmE)
    rwa [hEget i hi] at h
  let P : List (List V) := E.map (fun p => R p.1 p.2)
  have hPlen : P.length = C.length := by simp [P, hElen]
  have hPget (i : ℕ) (hi : i < C.length) :
      P[i]'(by omega) = R (C[i]'hi) (C[next i]'(hnext_lt i)) := by
    simp only [P, List.getElem_map]
    rw [hEget i hi]

  have hrungAt (i : ℕ) (hi : i < C.length) :
      IsUVRung G J S N (C[i]'hi) (C[next i]'(hnext_lt i)) (P[i]'(by omega)) := by
    have hmE : E[i]'(by omega) ∈ E := List.getElem_mem (l := E) (n := i) (by omega)
    have hr := hR (E[i]'(by omega)) (by simpa only [E] using hmE)
    rw [hEget i hi] at hr
    rw [hPget i hi]
    exact hr
  have hdata : ∀ (i : ℕ) (hi : i < C.length),
      ∃ s t : V, IsPathFrom G (P[i]'(by omega)) s t ∧
        (∀ x ∈ P[i]'(by omega), x ∈ N (C[i]'hi) ↔ x = s) ∧
        (∀ x ∈ P[i]'(by omega), x ∈ N (C[next i]'(hnext_lt i)) ↔ x = t) := by
    intro i hi
    exact StripSystemBasics.rung_isPath (hrungAt i hi)
  choose s₀ t₀ hdata using hdata
  let fallback : V := s₀ 0 hcpos
  let s : ℕ → V := fun i => if hi : i < C.length then s₀ i hi else fallback
  let t : ℕ → V := fun i => if hi : i < C.length then t₀ i hi else fallback

  have hhole : IsHoleList G (P.flatMap id) := by
    refine CyclicPathConcatenationIsHole.isHoleList_flatMap_of_cyclic G P s t
      (by rw [hPlen]; omega) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have hic : i < C.length := by rw [← hPlen]; exact hi
      simpa [s, t, hic] using (hdata i hic).1
    · intro i j hi hj hij x hx hy
      have hic : i < C.length := by rw [← hPlen]; exact hi
      have hjc : j < C.length := by rw [← hPlen]; exact hj
      have he : s(C[i]'hic, C[next i]'(hnext_lt i)) ≠
          s(C[j]'hjc, C[next j]'(hnext_lt j)) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with h | h
        · exact hij ((List.Nodup.getElem_inj_iff hnd).mp h.1)
        · have h1 : i = next j := (List.Nodup.getElem_inj_iff hnd).mp h.1
          have h2 : next i = j := (List.Nodup.getElem_inj_iff hnd).mp h.2
          exact hnext_next_ne i hic <| by
            calc
              next (next i) = next j := congrArg next h2
              _ = i := h1.symm
      have hxi := StripSystemBasics.rung_subset_strip (hrungAt i hic) x hx
      have hyj := StripSystemBasics.rung_subset_strip (hrungAt j hjc) x hy
      exact (Set.disjoint_left.mp
        (StripSystemBasics.strip_disjoint hSN
          (StripSystemBasics.rung_adj (hrungAt i hic))
          (StripSystemBasics.rung_adj (hrungAt j hjc)) he) hxi) hyj
    · intro i hi x hx y hy
      have hic : i < C.length := by rw [← hPlen]; exact hi
      have hind : (i + 1) % P.length = next i := by rw [hPlen]
      have hnP : next i < P.length := by rw [hPlen]; exact hnext_lt i
      have hy' : y ∈ P[next i]'hnP := by
        simpa only [hind] using hy
      rw [hind]
      have hni : next i < C.length := hnext_lt i
      have hri := hrungAt i hic
      have hrn := hrungAt (next i) hni
      have hab : J.Adj (C[i]'hic) (C[next i]'hni) := hadjAt i hic
      have hbd : J.Adj (C[next i]'hni) (C[next (next i)]'(hnext_lt (next i))) :=
        hadjAt (next i) hni
      have had : (C[i]'hic) ≠ (C[next (next i)]'(hnext_lt (next i))) :=
        cne i (next (next i)) hic (hnext_lt (next i))
          (fun heq => hnext_next_ne i hic heq.symm)
      have hxSab := StripSystemBasics.rung_subset_strip hri x hx
      have hxSba : x ∈ S (C[next i]'hni) (C[i]'hic) := by
        rw [← StripSystemBasics.strip_symm hSN hab]
        exact hxSab
      have hySbd := StripSystemBasics.rung_subset_strip hrn y hy'
      have hxN : x ∈ N (C[next i]'hni) ↔ x = t i := by
        simpa [t, hic] using (hdata i hic).2.2 x hx
      have hyN : y ∈ N (C[next i]'hni) ↔ y = s (next i) := by
        simpa [s, hni] using (hdata (next i) hni).2.1 y hy'
      constructor
      · intro hxy
        have hn := StripSystemBasics.mem_N_of_adj hSN hab.symm hbd had
          hxSba hySbd hxy
        exact ⟨hxN.mp hn.1, hyN.mp hn.2⟩
      · rintro ⟨hxt, hys⟩
        exact StripSystemBasics.Nuv_complete hSN hab.symm hbd had x
          ⟨hxN.mpr hxt, hxSba⟩ y ⟨hyN.mpr hys, hySbd⟩
    · intro i j hi hj hij hjnext hinext x hx y hy
      have hic : i < C.length := by rw [← hPlen]; exact hi
      have hjc : j < C.length := by rw [← hPlen]; exact hj
      have hjni : j ≠ next i := by simpa [next, hPlen] using hjnext
      have hinj : i ≠ next j := by simpa [next, hPlen] using hinext
      have hni := hnext_lt i
      have hnj := hnext_lt j
      have hfour :
          [C[i]'hic, C[next i]'hni, C[j]'hjc, C[next j]'hnj].Nodup := by
        refine List.nodup_cons.mpr ⟨?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
          exact ⟨cne i (next i) hic hni (hnext_ne i hic).symm,
            cne i j hic hjc hij, cne i (next j) hic hnj hinj⟩
        · refine List.nodup_cons.mpr ⟨?_, ?_⟩
          · simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
            exact ⟨cne (next i) j hni hjc hjni.symm,
              cne (next i) (next j) hni hnj
                (fun heq => hij (hnext_inj i j hic hjc heq))⟩
          · refine List.nodup_cons.mpr ⟨?_, ?_⟩
            · simpa using cne j (next j) hjc hnj (hnext_ne j hjc).symm
            · simp
      exact StripSystemBasics.strip_anticomplete hSN
        (StripSystemBasics.rung_adj (hrungAt i hic))
        (StripSystemBasics.rung_adj (hrungAt j hjc)) hfour x
        (StripSystemBasics.rung_subset_strip (hrungAt i hic) x hx) y
        (StripSystemBasics.rung_subset_strip (hrungAt j hjc) y hy)
    · rw [List.length_flatMap]
      calc
        4 ≤ P.length := by rw [hPlen]; exact hlen
        _ ≤ (P.map List.length).sum := by
          have hle : (P.map List.length).length ≤ (P.map List.length).sum := by
            apply List.length_le_sum_of_one_le (P.map List.length)
            intro n hn
            obtain ⟨Q, hQP, rfl⟩ := List.mem_map.mp hn
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hQP
            have hic : i < C.length := by rw [← hPlen]; exact hi
            have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos (hdata i hic).1.1
            omega
          simpa using hle

  have heven : Even (holeLength (P.flatMap id)) := hG.1 _ hhole
  rw [CyclicPathConcatenationIsHole.holeLength_flatMap] at heven
  have hlengths : (P.map List.length).sum =
      (E.map (fun p => pathLength (R p.1 p.2))).sum + C.length := by
    have hmap : P.map List.length =
        E.map (fun p => pathLength (R p.1 p.2) + 1) := by
      simp only [P, List.map_map]
      apply List.map_congr_left
      intro p hp
      have hr := hR p (by simpa [E] using hp)
      have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos
        (StripSystemBasics.rung_isPath hr).choose_spec.choose_spec.1.1
      simp only [Function.comp_apply, pathLength]
      omega
    rw [hmap, List.sum_map_add]
    simp [hElen]
  rw [hlengths] at heven
  simpa [E] using heven

end Workspace.ProofLemmas.Thm81CycleEven
