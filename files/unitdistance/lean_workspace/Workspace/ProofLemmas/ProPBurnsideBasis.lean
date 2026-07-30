-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8; H. Koch, Galois Theory of p-Extensions, Springer, 2002, Theorem 4.10; J. D. Dixon, M. P. F. du Sautoy, A. Mann, D. Segal, Analytic Pro-p Groups, 2nd ed., CUP, 1999, Proposition 1.9(ii).
-- Paper label: Proposition 3.3 (first assertion) / Proposition A.8
-- NL statement: For a finitely generated pro-p group G, the Frattini subgroup satisfies Phi(G) = G^p [G,G]; hence every commutator x y x^{-1} y^{-1} and every p-th power x^p lies in Phi(G), the quotient G/Phi(G) is an elementary abelian p-group (an F_p-vector space), and Burnside's basis theorem gives d(G) = dim_{F_p} G/Phi(G): there is a natural number d with d(G) = d and |G/Phi(G)| = p^d.
--
-- This theorem is factored into two cited inputs:
--   * ProPMaximalOpenNormalIndexP: every maximal proper open subgroup is normal of index p;
--   * ProPGeneratorRankFrattini:   d(G) equals the F_p-dimension of the Frattini quotient.
-- Conjuncts (a) [commutators lie in Φ(G)] and (b) [p-th powers lie in Φ(G)] are proved here from
-- ProPMaximalOpenNormalIndexP (each maximal open subgroup H has index p, hence G/H is cyclic of
-- order p, hence abelian of exponent p, so every commutator and every p-th power maps to 1 in G/H;
-- Φ(G) is the intersection of all such H). Conjunct (c) [the rank/cardinality equality] is cited
-- from ProPGeneratorRankFrattini.
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.ProPMaximalOpenNormalIndexP
import Workspace.ProofLemmas.ProPGeneratorRankFrattini

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Proposition 3.3, Burnside basis.** For a finitely generated pro-`p` group `G`, the
quotient `G/Φ(G)` is an elementary abelian `p`-group (all commutators and `p`-th powers lie
in `Φ(G)`), i.e. an `𝔽_p`-vector space, and the generator rank `d(G)` equals its
`𝔽_p`-dimension: there is `d` with `d(G) = d` and `|G/Φ(G)| = p^d`.

Conjuncts (a) and (b) are proved from `ProPMaximalOpenNormalIndexP`; conjunct (c) is
cited from `ProPGeneratorRankFrattini`. -/
theorem ProPBurnsideBasis (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) :
    (∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ frattiniOpen G) ∧
    (∀ x : G, x ^ p ∈ frattiniOpen G) ∧
    ∃ d : ℕ, dRank G = (d : ℕ∞) ∧ Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  refine ⟨?_, ?_, ProPGeneratorRankFrattini p G hpro hfg⟩
  · -- (a) commutators lie in Φ(G)
    intro x y
    rw [frattiniOpen, Subgroup.mem_sInf]
    intro H hH
    obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
    haveI := hnorm
    have hcard : Nat.card (G ⧸ H) = p := hidx
    haveI : Finite (G ⧸ H) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
    haveI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
    haveI : IsMulCommutative (G ⧸ H) := IsCyclic.isMulCommutative
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm' (x : G ⧸ H) (y : G ⧸ H)]
    group
  · -- (b) p-th powers lie in Φ(G)
    intro x
    rw [frattiniOpen, Subgroup.mem_sInf]
    intro H hH
    obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
    haveI := hnorm
    have hcard : Nat.card (G ⧸ H) = p := hidx
    haveI : Finite (G ⧸ H) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_pow]
    rw [← hcard]
    exact pow_card_eq_one'
