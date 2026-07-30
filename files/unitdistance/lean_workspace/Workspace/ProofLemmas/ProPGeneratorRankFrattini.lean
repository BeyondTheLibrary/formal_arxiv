-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8
-- (Burnside basis / topological Nakayama); J. D. Dixon et al., Analytic Pro-p Groups, 2nd ed.,
-- CUP, 1999, Proposition 1.9(ii).
--
-- The only admitted input is the topological Nakayama upper bound `ProPTopologicalNakayama`
-- (∃ a topological generating set of size ≤ dim_{F_p} G/Φ(G)).
-- Everything else is proved from Mathlib and `ProPMaximalOpenNormalIndexP`:
--   * `frattiniOpen_isOpen` / `frattiniOpen_normal`: Φ(G) is open and normal, via the finiteness
--     of the set of maximal open subgroups (each is the kernel of a continuous hom G → 𝔽_p, and a
--     continuous hom into a finite discrete group is determined by its values on a topological
--     generating set, so there are only finitely many);
--   * `frattiniQuotient_card`: G/Φ(G) is a finite elementary abelian p-group of order p^d, d its
--     𝔽_p-dimension (commutators and p-th powers lie in Φ(G) by `ProPMaximalOpenNormalIndexP`, then
--     the ZMod p-module cardinality formula);
--   * LOWER bound d ≤ d(G) (`card_quot_le` + the assembly): the image of any topological
--     generating finset spans the 𝔽_p-vector space G/Φ(G), so any such finset has ≥ d elements.
-- The reverse inequality d(G) ≤ d (lifting an 𝔽_p-basis of G/Φ(G) to topological generators) is
-- the admitted input `ProPTopologicalNakayama`.
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.ProPMaximalOpenNormalIndexP
import Workspace.ProofLemmas.ProPTopologicalNakayama

set_option maxHeartbeats 800000

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

namespace ProPGeneratorRankFrattiniAux

/-- Continuous homs to a finite discrete group are determined by their values
on a topologically generating set. -/
theorem eq_of_eqOn_topgen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [Group F] [TopologicalSpace F] [DiscreteTopology F] [T2Space F]
    (S : Set G) (hS : TopologicallyGenerates S)
    (φ ψ : G →* F) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hagree : Set.EqOn φ ψ S) : φ = ψ := by
  have hgen : Set.EqOn φ ψ (Subgroup.closure S : Set G) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem z hz => exact hagree hz
    | one => simp
    | mul a b _ _ ha hb => simp [map_mul, ha, hb]
    | inv a _ ha => simp [map_inv, ha]
  have hdense : Dense ((Subgroup.closure S : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq]; exact hS
  exact DFunLike.coe_injective (Continuous.ext_on hdense hφ hψ hgen)

/-- Cardinality bound from a spanning finset of a finite `ZMod p`-module. -/
theorem card_le_of_gen_span {M : Type*} [AddCommGroup M] [Finite M] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) M] (F : Finset M)
    (hgen : ∀ a : M, a ∈ Submodule.span (ZMod p) (↑F : Set M)) :
    Nat.card M ≤ p ^ F.card := by
  haveI : Fintype M := Fintype.ofFinite _
  have hspan : Submodule.span (ZMod p) (↑F : Set M) = ⊤ := Submodule.eq_top_iff'.mpr hgen
  have hcard := @Module.card_eq_pow_finrank (ZMod p) M _ _ _ _ _
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard
  rw [hcard]
  apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
  have h := finrank_span_finset_le_card (R := ZMod p) F
  have heq : Set.finrank (ZMod p) (↑F : Set M) = Module.finrank (ZMod p) M := by
    unfold Set.finrank; rw [hspan, finrank_top]
  rwa [heq] at h

/-- The image of a multiplicative closure lands in the `ZMod p`-span of the image. -/
theorem mem_span_of_mem_closure {Q : Type*} [CommGroup Q] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) (Additive Q)] (F : Set Q) (q : Q)
    (hq : q ∈ Subgroup.closure F) :
    Additive.ofMul q ∈ Submodule.span (ZMod p) ((Additive.ofMul '' F) : Set (Additive Q)) := by
  induction hq using Subgroup.closure_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | one => simpa using Submodule.zero_mem _
  | mul x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | inv x _ hx => exact Submodule.neg_mem _ hx

/-- If a continuous surjection maps `G` onto a finite discrete elementary abelian `p`-group `Q`,
then any topologically generating finset `S` of `G` bounds `|Q| ≤ p ^ |S|`. -/
theorem card_quot_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Q : Type*} [CommGroup Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {p : ℕ} [Fact p.Prime] [Finite Q]
    (hexp : ∀ q : Q, q ^ p = 1)
    (π : G →* Q) (hcont : Continuous π) (hsurj : Function.Surjective π)
    (S : Finset G) (hS : TopologicallyGenerates (↑S : Set G)) :
    Nat.card Q ≤ p ^ S.card := by
  classical
  have key : (Set.univ : Set Q) ⊆ (↑(Subgroup.closure (π '' (↑S : Set G))) : Set Q) := by
    have e1 : (Set.univ : Set Q)
        = π '' (_root_.closure ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G)) := by
      rw [hS, Set.image_univ, hsurj.range_eq]
    rw [e1]
    calc π '' (_root_.closure ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G))
        ⊆ _root_.closure (π '' ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G)) :=
          image_closure_subset_closure_image hcont
      _ = _root_.closure ((Subgroup.closure (π '' (↑S : Set G)) : Subgroup Q) : Set Q) := by
          rw [← Subgroup.coe_map, MonoidHom.map_closure]
      _ = ((Subgroup.closure (π '' (↑S : Set G)) : Subgroup Q) : Set Q) :=
          (isClosed_discrete _).closure_eq
  have hgen : Subgroup.closure (π '' (↑S : Set G)) = ⊤ := by
    rw [eq_top_iff]; intro x _; exact key (Set.mem_univ x)
  haveI : Fintype Q := Fintype.ofFinite _
  have hexpA : ∀ a : Additive Q, (p : ℕ) • a = 0 := by
    intro a
    have h1 : (Additive.toMul a) ^ p = 1 := hexp (Additive.toMul a)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h1
  letI : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hexpA
  haveI : Finite (Additive Q) := ‹Finite Q›
  set FA : Finset (Additive Q) := S.image (fun g => (Additive.ofMul (π g))) with hFA
  have hFAcoe : (↑FA : Set (Additive Q)) = Additive.ofMul '' (π '' (↑S : Set G)) := by
    rw [hFA, Finset.coe_image, Set.image_image]
  rw [show Nat.card Q = Nat.card (Additive Q) from rfl]
  refine (card_le_of_gen_span (M := Additive Q) (p := p) FA (fun a => ?_)).trans
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by rw [hFA]; exact Finset.card_image_le))
  have ha : Additive.toMul a ∈ Subgroup.closure (π '' (↑S : Set G)) := by
    rw [hgen]; exact Subgroup.mem_top _
  have hh := mem_span_of_mem_closure (p := p) (π '' (↑S : Set G)) (Additive.toMul a) ha
  rw [← hFAcoe] at hh
  simpa using hh

section
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)

include hpro hfg

/-- Every maximal open subgroup is the kernel of a continuous hom onto `Multiplicative (ZMod p)`. -/
theorem exists_hom_ker (K : Subgroup G) (hK : IsMaximalOpenSubgroup K) :
    ∃ φ : G →* Multiplicative (ZMod p), Continuous φ ∧ φ.ker = K := by
  obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg K hK
  haveI := hnorm
  have hKopen : IsOpen (K : Set G) := hK.1
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKopen
  have hcardK : Nat.card (G ⧸ K) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  have hMult : Nat.card (Multiplicative (ZMod p)) = p := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  let e : (G ⧸ K) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardK hMult
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_, ?_⟩
  · exact (continuous_of_discreteTopology (f := e)).comp QuotientGroup.continuous_mk
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, QuotientGroup.coe_mk']
    rw [show (1 : Multiplicative (ZMod p)) = e 1 from (map_one e).symm, e.apply_eq_iff_eq,
      QuotientGroup.eq_one_iff]

/-- The set of maximal open subgroups is finite. -/
theorem finite_maximalOpen : {K : Subgroup G | IsMaximalOpenSubgroup K}.Finite := by
  obtain ⟨S, hS⟩ := id hfg
  haveI : Finite (↑(S : Set G)) := (S : Set G).toFinite.to_subtype
  rw [Set.finite_coe_iff.symm]
  have hchoose : ∀ K : {K : Subgroup G // IsMaximalOpenSubgroup K},
      ∃ φ : G →* Multiplicative (ZMod p), Continuous φ ∧ φ.ker = K.1 :=
    fun K => exists_hom_ker p G hpro hfg K.1 K.2
  choose φ hcont hker using hchoose
  have hinj : Function.Injective
      (fun K : {K : Subgroup G // IsMaximalOpenSubgroup K} =>
        (fun s : (↑(S : Set G)) => φ K s.1)) := by
    intro K₁ K₂ heq
    have hagree : Set.EqOn (φ K₁) (φ K₂) (S : Set G) := by
      intro s hs
      exact congrFun heq ⟨s, hs⟩
    have := eq_of_eqOn_topgen (S : Set G) hS (φ K₁) (φ K₂) (hcont K₁) (hcont K₂) hagree
    apply Subtype.ext
    rw [← hker K₁, ← hker K₂, this]
  exact Finite.of_injective _ hinj

/-- The topological Frattini subgroup is open. -/
theorem frattiniOpen_isOpen : IsOpen ((frattiniOpen G : Subgroup G) : Set G) := by
  have hfin := finite_maximalOpen p G hpro hfg
  rw [frattiniOpen, Subgroup.coe_sInf]
  exact hfin.isOpen_biInter (fun H hH => hH.1)

/-- The topological Frattini subgroup is normal. -/
theorem frattiniOpen_normal : (frattiniOpen G).Normal := by
  rw [frattiniOpen]
  constructor
  intro n hn g
  rw [Subgroup.mem_sInf] at hn ⊢
  intro H hH
  obtain ⟨hnorm, _⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  exact hnorm.conj_mem n (hn H hH) g

/-- Every commutator lies in `Φ(G)` (from R1: each maximal open `H` has index `p`, so `G/H`
is abelian). -/
theorem commutator_mem_frattini (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ frattiniOpen G := by
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

/-- Every `p`-th power lies in `Φ(G)`. -/
theorem pow_mem_frattini (x : G) : x ^ p ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
  exact pow_card_eq_one'

/-- `G/Φ(G)` is abelian. -/
theorem frattiniQuotient_comm [(frattiniOpen G).Normal] :
    ∀ a b : G ⧸ frattiniOpen G, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using commutator_mem_frattini p G hpro hfg y⁻¹ x⁻¹

/-- `G/Φ(G)` has exponent dividing `p`. -/
theorem frattiniQuotient_expp [(frattiniOpen G).Normal] :
    ∀ q : G ⧸ frattiniOpen G, q ^ p = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_mem_frattini p G hpro hfg x

/-- `G/Φ(G)` is a finite elementary abelian `p`-group: its cardinality is `p^d`. -/
theorem frattiniQuotient_card :
    ∃ d : ℕ, Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  haveI : (frattiniOpen G).Normal := frattiniOpen_normal p G hpro hfg
  have hcomm := frattiniQuotient_comm p G hpro hfg
  have hpow_all := frattiniQuotient_expp p G hpro hfg
  obtain ⟨_, hcompact, _, _, _⟩ := id hpro
  haveI := hcompact
  haveI : Finite (G ⧸ frattiniOpen G) :=
    Subgroup.quotient_finite_of_isOpen _ (frattiniOpen_isOpen p G hpro hfg)
  letI : CommGroup (G ⧸ frattiniOpen G) := { mul_comm := hcomm }
  have hexp : ∀ a : Additive (G ⧸ frattiniOpen G), (p : ℕ) • a = 0 := by
    intro a
    have h1 : (Additive.toMul a) ^ p = 1 := hpow_all (Additive.toMul a)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h1
  letI : Module (ZMod p) (Additive (G ⧸ frattiniOpen G)) := AddCommGroup.zmodModule hexp
  haveI : Fintype (G ⧸ frattiniOpen G) := Fintype.ofFinite _
  haveI : Fintype (Additive (G ⧸ frattiniOpen G)) := Fintype.ofFinite _
  refine ⟨Module.finrank (ZMod p) (Additive (G ⧸ frattiniOpen G)), ?_⟩
  have hcard := @Module.card_eq_pow_finrank (ZMod p) (Additive (G ⧸ frattiniOpen G)) _ _ _ _ _
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard
  exact hcard

/-- Assembled Burnside rank formula (Nakayama upper bound cited). -/
theorem main :
    ∃ d : ℕ, dRank G = (d : ℕ∞) ∧ Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  haveI hN : (frattiniOpen G).Normal := frattiniOpen_normal p G hpro hfg
  obtain ⟨_, hcompact, _, _, _⟩ := id hpro
  haveI := hcompact
  haveI hQfin : Finite (G ⧸ frattiniOpen G) :=
    Subgroup.quotient_finite_of_isOpen _ (frattiniOpen_isOpen p G hpro hfg)
  haveI hQdisc : DiscreteTopology (G ⧸ frattiniOpen G) :=
    QuotientGroup.discreteTopology (frattiniOpen_isOpen p G hpro hfg)
  have hexp := frattiniQuotient_expp p G hpro hfg
  letI : CommGroup (G ⧸ frattiniOpen G) := { mul_comm := frattiniQuotient_comm p G hpro hfg }
  obtain ⟨d, hd⟩ := frattiniQuotient_card p G hpro hfg
  refine ⟨d, ?_, hd⟩
  apply le_antisymm
  · -- dRank G ≤ d  (topological Nakayama, residual)
    obtain ⟨S, hStop, hScard⟩ := ProPTopologicalNakayama p G hpro hfg d hd
    refine le_trans (sInf_le ⟨S, hStop, rfl⟩) ?_
    exact_mod_cast hScard
  · -- d ≤ dRank G  (lower bound, proved)
    apply le_sInf
    rintro n ⟨S, hStop, rfl⟩
    have hb := card_quot_le (Q := G ⧸ frattiniOpen G) hexp
      (QuotientGroup.mk' (frattiniOpen G)) QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective _) S hStop
    rw [hd] at hb
    have hle : d ≤ S.card := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hb
    exact_mod_cast hle

end
end ProPGeneratorRankFrattiniAux

/-- **Proposition 3.3 / A.8, Burnside basis (rank formula).** For a finitely generated pro-`p`
group `G`, the generator rank `d(G)` equals the `𝔽_p`-dimension of the Frattini quotient:
there is `d` with `dRank G = d` and `|G/Φ(G)| = p^d`.  Proved from Mathlib and
`ProPMaximalOpenNormalIndexP` except for the topological Nakayama upper bound, cited from
`ProPTopologicalNakayama`. -/
theorem ProPGeneratorRankFrattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) :
    ∃ d : ℕ, dRank G = (d : ℕ∞) ∧ Nat.card (G ⧸ frattiniOpen G) = p ^ d :=
  ProPGeneratorRankFrattiniAux.main p G hpro hfg

