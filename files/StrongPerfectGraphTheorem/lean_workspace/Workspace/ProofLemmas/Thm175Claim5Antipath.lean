import Workspace.ProofLemmas.Thm175Claim4Setup
import Workspace.ProofLemmas.Thm203AntipathTools

/-! The two applications in the complement in the proof of 17.5 (5). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim5Antipath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_drop_iff {P : List V} {k : ℕ} {v : V} :
    v ∈ P.drop k ↔ ∃ i, ∃ hi : i < P.length, k ≤ i ∧ P[i]'hi = v := by
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    refine ⟨k + i, by have hh := hi; simp only [List.length_drop] at hh; omega,
      by omega, ?_⟩
    simp
  · rintro ⟨i, hi, hki, rfl⟩
    have hj : i - k < (P.drop k).length := by simp; omega
    have he : (P.drop k)[i - k]'hj = P[i]'hi := by simp [Nat.add_sub_of_le hki]
    exact he ▸ List.getElem_mem hj

/-- PAPER: "By 13.6 applied in [the complement], ... `S` has odd length. ...
so by 2.2 applied in [the complement], some internal vertex of `S` has no
neighbour in `P\{p₁,p₂}`. But they are all adjacent to `p_j` or to `p_n`,
so `j=2`."  Here `j` is zero-based. -/
theorem complete_index_eq_one
    (G : SimpleGraph V) (hG : InF5 G) (P : List V) (p₁ pₙ x z : V)
    (hP : IsPathFrom G P p₁ pₙ) (hlen : 4 ≤ P.length)
    (hxP : x ∉ P) (hzP : z ∉ P)
    (hxonly : ∀ v ∈ P, G.Adj x v → v = p₁)
    (hzanti : VertexAnticomplete G z {v | v ∈ P})
    (S : List V) (hS : IsAntipathFrom G S x p₁) (hSlong : 4 ≤ S.length)
    (hSP : ∀ v ∈ S, v ∈ P → v = p₁)
    (hzS : z ∉ S)
    (hzcomp : ∀ v ∈ S, v ≠ p₁ → G.Adj z v)
    (j : ℕ) (hj : j < P.length) (hjpos : 0 < j)
    (hint : ∀ v ∈ SPGT.interior S, G.Adj v (P[j]'hj) ∨ G.Adj v pₙ) :
    j = 1 := by
  have hp₁P := PathBasics.head_mem hP.2.1
  have hpₙP := PathBasics.getLast_mem hP.2.2
  have hp0 : P[0]'(by omega) = p₁ :=
    PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hpn : P[P.length - 1]'(by omega) = pₙ :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hp₁not (k : ℕ) (hk : 0 < k) : p₁ ∉ P.drop k := by
    intro hm
    obtain ⟨i, hi, hki, hi0⟩ := mem_drop_iff.mp hm
    have := hP.1.2.1.getElem_inj_iff.mp (hi0.trans hp0.symm)
    omega
  have hSout (k : ℕ) (hk : 0 < k) : ∀ v ∈ S, v ∉ P.drop k := by
    intro v hv hm
    exact hp₁not k hk (hSP v hv (List.drop_subset _ _ hm) ▸ hm)
  have hxanti (k : ℕ) (hk : 0 < k) :
      ∀ v ∈ P.drop k, ¬ G.Adj x v := by
    intro v hv hadj
    exact hp₁not k hk (hxonly v (List.drop_subset _ _ hv) hadj ▸ hv)
  have hzantiDrop (k : ℕ) : ∀ v ∈ P.drop k, ¬ G.Adj z v :=
    fun v hv => hzanti v (List.drop_subset _ _ hv)
  have hpnDrop (k : ℕ) (hk : k < P.length) : pₙ ∈ P.drop k :=
    mem_drop_iff.mpr ⟨P.length - 1, by omega, by omega, hpn⟩
  have hconn (k : ℕ) (hk : k < P.length) : ConnectedSet G {v | v ∈ P.drop k} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_drop hP.1 hk)
  have hxp₁ : G.Adj x p₁ := by
    have hn := PathBasics.path_ends_not_adj hS.1 (by omega)
    rw [PathBasics.getElem_zero_of_head? hS.2.1 (by omega),
      PathBasics.getElem_last_of_getLast? hS.2.2 (by omega)] at hn
    by_contra ha
    exact hn ((SimpleGraph.compl_adj G x p₁).mpr
      ⟨fun he => hxP (he ▸ hp₁P), ha⟩)
  have hQ : IsAntipathFrom G (S ++ [z]) x z := by
    apply PathAttach.isPathFrom_concat hS
    · exact (SimpleGraph.compl_adj G z p₁).mpr
        ⟨fun he => hzP (he ▸ hp₁P), hzanti p₁ hp₁P⟩
    · exact hzS
    · intro v hv hne hadj
      exact ((SimpleGraph.compl_adj G z v).mp hadj).2 (hzcomp v hv hne)
  have hxnep : x ≠ p₁ := fun he => hxP (he ▸ hp₁P)
  have hzx : G.Adj z x := hzcomp x (PathBasics.head_mem hS.2.1) hxnep
  have hQout : ∀ v ∈ S ++ [z], v ∉ P.drop 1 := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hSout 1 (by omega) v hv
    · have he : v = z := by simpa using hv
      exact fun hm => hzP (he ▸ List.drop_subset _ _ hm)
  have hQint : ∀ v ∈ SPGT.interior (S ++ [z]),
      ∃ a ∈ P.drop 1, G.Adj v a := by
    intro v hv
    have hparts := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hv
    have hvS : v ∈ S := by
      rcases List.mem_append.mp hparts.1 with hs | hz
      · exact hs
      · exact (hparts.2.2 (by simpa using hz)).elim
    by_cases hvp : v = p₁
    · subst v
      refine ⟨P[1]'(by omega), mem_drop_iff.mpr ⟨1, by omega, le_rfl, rfl⟩, ?_⟩
      have ha := PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
      simpa only [hp0] using ha
    · have hvI := (PathBasics.mem_interior_iff_of_pathFrom hS).mpr
        ⟨hvS, hparts.2.1, hvp⟩
      rcases hint v hvI with ha | ha
      · exact ⟨P[j]'hj, mem_drop_iff.mpr ⟨j, hj, by omega, rfl⟩, ha⟩
      · exact ⟨pₙ, hpnDrop 1 (by omega), ha⟩
  have hSeven : Even (pathLength (S ++ [z])) := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    have hthree := Thm203AntipathTools.antipath_length_three_of_odd hG
      (hconn 1 (by omega)) hQ ho hzx.symm hQout
      (hxanti 1 (by omega)) (hzantiDrop 1) hQint
    simp only [pathLength, List.length_append, List.length_singleton] at hthree
    omega
  have hSodd : Odd (pathLength S) := by
    rw [Nat.even_iff] at hSeven
    rw [Nat.odd_iff]
    simp only [pathLength, List.length_append, List.length_singleton] at *
    omega
  by_contra hjne
  have hjtwo : 2 ≤ j := by omega
  have hp₁anti : ∀ v ∈ P.drop 2, ¬ G.Adj p₁ v := by
    intro v hv ha
    obtain ⟨i, hi, h2i, rfl⟩ := mem_drop_iff.mp hv
    rw [← hp0] at ha
    have := (PathBasics.path_adj_iff hP.1 (by omega) hi).mp ha
    omega
  have hint2 : ∀ v ∈ SPGT.interior S, ∃ a ∈ P.drop 2, G.Adj v a := by
    intro v hv
    rcases hint v hv with ha | ha
    · exact ⟨P[j]'hj, mem_drop_iff.mpr ⟨j, hj, hjtwo, rfl⟩, ha⟩
    · exact ⟨pₙ, hpnDrop 2 (by omega), ha⟩
  have hzI : ∀ v ∈ SPGT.interior S, G.Adj z v := by
    intro v hv
    have hparts := (PathBasics.mem_interior_iff_of_pathFrom hS).mp hv
    exact hzcomp v hparts.1 hparts.2.2
  obtain ⟨v, hv, ha⟩ | ⟨v, hv, ha⟩ :=
    Thm203AntipathTools.exists_end_nbr_of_odd_antipath hG.1.1
      (hconn 2 (by omega)) (fun hm => hzP (List.drop_subset _ _ hm))
      (hzantiDrop 2) hS hSodd hxp₁ (hSout 2 (by omega)) hint2 hzI
  · exact hxanti 2 (by omega) v hv ha
  · exact hp₁anti v hv ha

end Workspace.ProofLemmas.Thm175Claim5Antipath
