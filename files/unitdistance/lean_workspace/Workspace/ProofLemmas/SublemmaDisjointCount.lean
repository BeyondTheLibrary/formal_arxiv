import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.SplittingRamification

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.SplittingRamification

theorem SublemmaDisjointCount (d : AdmissibleDatum)
    (hcount : ∀ b, (Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard
      = 2 * deg d) :
    (⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard
      = 2 * d.t * deg d := by
  set S : Fin d.t → Set (Ideal (𝓞 d.K)) :=
    fun b => Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) with hS
  -- degree of L is positive
  have hdeg : 0 < deg d := by
    have h := Module.finrank_pos (R := ℚ) (M := d.L)
    simpa [deg] using h
  -- each block is finite (its ncard is nonzero)
  have hne : ∀ b, (S b).ncard ≠ 0 := by
    intro b
    rw [hcount b]
    omega
  have hfin : ∀ b, (S b).Finite := fun b => Set.finite_of_ncard_ne_zero (hne b)
  -- the blocks are pairwise disjoint
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro b b' hbb'
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro P hP hP'
    rw [hS] at hP hP'
    simp only [Ideal.primesOver, Set.mem_setOf_eq] at hP hP'
    have hlies : P.LiesOver (Ideal.span {(d.q b : ℤ)}) := hP.2
    have hlies' : P.LiesOver (Ideal.span {(d.q b' : ℤ)}) := hP'.2
    have heq : Ideal.span {(d.q b : ℤ)} = Ideal.span {(d.q b' : ℤ)} :=
      hlies.over.trans hlies'.over.symm
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at heq
    simp only [Int.natAbs_natCast] at heq
    exact hbb' (d.hq_distinct heq)
  rw [Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype]
  have hcount' : ∀ i, (S i).ncard = 2 * deg d := hcount
  simp only [hcount', Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring
