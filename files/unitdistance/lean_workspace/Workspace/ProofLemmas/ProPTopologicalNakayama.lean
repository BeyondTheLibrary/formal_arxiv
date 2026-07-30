-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8
-- (Burnside basis theorem / topological Nakayama lemma, Cor. 2.8.4); J. D. Dixon, M. P. F. du
-- Sautoy, A. Mann, D. Segal, Analytic Pro-p Groups, 2nd ed., CUP, 1999, Proposition 1.9(ii).
--
-- Paper label: Proposition 3.3 / Proposition A.8 (Burnside basis, upper bound).
--
-- The **topological Nakayama upper bound** of the topological Burnside basis theorem, proved from
-- Mathlib together with the sibling theorem `ProPMaximalOpenNormalIndexP`.
--
-- Proof structure:
--   * `gen_finset_of_module` / `exists_gen_finset`: a finite elementary abelian p-group Q = G/Φ(G)
--     of order p^d, viewed as a d-dimensional 𝔽_p-vector space (Additive Q), has an 𝔽_p-basis of
--     size d whose multiplicative image generates Q; hence a generating finset of card ≤ d.
--   * `exists_maximalOpen_ge` (the compactness step): a proper closed subgroup H of a profinite
--     group is contained in a maximal proper open subgroup. Proof: `closedSubgroup_eq_sInf_open`
--     yields a proper open N₀ ⊇ H; its normal core N is open normal, G/N is finite, and a coatom
--     M̄ of the finite subgroup lattice above the (proper) image of N₀ pulls back to a maximal open
--     M ⊇ H (via `IsCoatomic` on the finite group's subgroup lattice).
--   * The Frattini facts (`frattiniOpen_normal`, commutator/p-th-power in Φ(G), G/Φ(G) abelian of
--     exponent p) are re-derived locally from `ProPMaximalOpenNormalIndexP` (to avoid an import
--     cycle with `ProPGeneratorRankFrattini`, which imports this file).
--   * Nakayama assembly: lift an 𝔽_p-basis of G/Φ(G) to a finset S of size ≤ d. The closed subgroup
--     H := closure⟨S⟩ maps ONTO G/Φ(G); if H ≠ G it would sit inside a maximal open M ⊇ Φ(G), whose
--     image in G/Φ(G) is a proper subgroup containing the generators — contradiction. Hence S
--     topologically generates G.
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.ProPMaximalOpenNormalIndexP
set_option maxHeartbeats 800000
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

namespace ProPTopologicalNakayamaAux

/-- If `Additive Q` is a finite `ZMod p`-module of dimension `d`, then `Q` has a generating
finset of cardinality `≤ d` (an `𝔽ₚ`-basis, mapped back multiplicatively). -/
theorem gen_finset_of_module (p : ℕ) [Fact p.Prime] (Q : Type*) [CommGroup Q] [Finite Q]
    [Module (ZMod p) (Additive Q)] (d : ℕ)
    (hd : Module.finrank (ZMod p) (Additive Q) = d) :
    ∃ T : Finset Q, T.card ≤ d ∧ Subgroup.closure (T : Set Q) = ⊤ := by
  classical
  haveI : Fintype (Additive Q) := Fintype.ofFinite _
  have hsmul : ∀ (c : ZMod p) (a : Additive Q), c • a = (c.val) • a := by
    intro c a; rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  haveI : Fintype ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)) :=
    (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinite.fintype
  have hcardι : Fintype.card ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)) = d := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace (ZMod p) (Additive Q))]
    exact hd
  have hspan : Submodule.span (ZMod p)
      (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q) : Set (Additive Q)) = ⊤ := by
    have h := (Module.Basis.ofVectorSpace (ZMod p) (Additive Q)).span_eq
    rwa [Module.Basis.range_ofVectorSpace] at h
  refine ⟨(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.image Additive.toMul,
    ?_, ?_⟩
  · calc ((Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.image
              Additive.toMul).card
        ≤ (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.card :=
          Finset.card_image_le
      _ = Fintype.card ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)) :=
          Set.toFinset_card _
      _ = d := hcardι
  · rw [eq_top_iff]
    intro q _
    have key : ∀ a : Additive Q,
        a ∈ Submodule.span (ZMod p)
          (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q) : Set (Additive Q)) →
        Additive.toMul a ∈ Subgroup.closure
          (↑((Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.image
            Additive.toMul) : Set Q) := by
      intro a ha'
      induction ha' using Submodule.span_induction with
      | mem x hx =>
          apply Subgroup.subset_closure
          rw [Finset.coe_image, Set.coe_toFinset]
          exact ⟨x, hx, rfl⟩
      | zero => simpa using Subgroup.one_mem _
      | add x y _ _ hx hy => rw [toMul_add]; exact Subgroup.mul_mem _ hx hy
      | smul c x _ hx => rw [hsmul c x, toMul_nsmul]; exact Subgroup.pow_mem _ hx _
    have hmem : (Additive.ofMul q) ∈ Submodule.span (ZMod p)
        (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q) : Set (Additive Q)) := by
      rw [hspan]; exact Submodule.mem_top
    have := key (Additive.ofMul q) hmem
    simpa using this

/-- A finite elementary abelian `p`-group `Q` of order `p^d` has a generating finset of
cardinality `≤ d`. -/
theorem exists_gen_finset (p : ℕ) [Fact p.Prime] (Q : Type*) [CommGroup Q] [Finite Q]
    (hexp : ∀ q : Q, q ^ p = 1) (d : ℕ) (hcard : Nat.card Q = p ^ d) :
    ∃ T : Finset Q, T.card ≤ d ∧ Subgroup.closure (T : Set Q) = ⊤ := by
  have hexpA : ∀ a : Additive Q, (p : ℕ) • a = 0 := by
    intro a
    have h1 : (Additive.toMul a) ^ p = 1 := hexp (Additive.toMul a)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h1
  letI : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hexpA
  haveI : Fintype (Additive Q) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod p) (Additive Q) :=
    Module.Finite.of_finite (R := ZMod p) (M := Additive Q)
  have hfr : Module.finrank (ZMod p) (Additive Q) = d := by
    have hc := @Module.card_eq_pow_finrank (ZMod p) (Additive Q) _ _ _ _ _
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hc
    have hcA : Nat.card (Additive Q) = p ^ d := by
      rw [show Nat.card (Additive Q) = Nat.card Q from rfl]; exact hcard
    rw [hcA] at hc
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hc.symm)
  exact gen_finset_of_module p Q d hfr

/-- **Compactness step.** A proper closed subgroup `H` of a profinite group is contained in a
maximal proper open subgroup. -/
theorem exists_maximalOpen_ge (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (H : Subgroup G) (hHcl : IsClosed (H : Set G)) (hHne : H ≠ ⊤) :
    ∃ M : Subgroup G, IsMaximalOpenSubgroup M ∧ H ≤ M := by
  obtain ⟨_, hcompact, hT2, hTD, _⟩ := hpro
  haveI := hcompact; haveI := hT2; haveI := hTD
  have hHeq : (H : Subgroup G) = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} :=
    ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨H, hHcl⟩
  obtain ⟨N0, hN0open, hHN0, hN0ne⟩ :
      ∃ N0 : Subgroup G, IsOpen (N0 : Set G) ∧ H ≤ N0 ∧ N0 ≠ ⊤ := by
    by_contra hcon
    push_neg at hcon
    apply hHne
    rw [hHeq, eq_top_iff]
    refine le_sInf ?_
    rintro N ⟨hNopen, hHN⟩
    exact le_of_eq (hcon N hNopen hHN).symm
  haveI : Finite (G ⧸ N0) := Subgroup.quotient_finite_of_isOpen N0 hN0open
  haveI : N0.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN0closed : IsClosed (N0 : Set G) := Subgroup.isClosed_of_isOpen N0 hN0open
  have hNcl : IsClosed (N0.normalCore : Set G) := Subgroup.normalCore_isClosed N0 hN0closed
  have hNopen : IsOpen (N0.normalCore : Set G) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex N0.normalCore hNcl
  set N := N0.normalCore with hNdef
  have hNle : N ≤ N0 := Subgroup.normalCore_le N0
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  set π := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  set N0bar := Subgroup.map π N0 with hN0bar
  have hcomapN0 : Subgroup.comap π N0bar = N0 := by
    rw [hN0bar, Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNle
  have hN0barne : N0bar ≠ ⊤ := by
    intro htop
    apply hN0ne
    have hc : Subgroup.comap π N0bar = Subgroup.comap π ⊤ := by rw [htop]
    rwa [hcomapN0, Subgroup.comap_top] at hc
  obtain ⟨Mbar, hMcoatom, hN0Mbar⟩ :=
    (eq_top_or_exists_le_coatom N0bar).resolve_left hN0barne
  set M := Subgroup.comap π Mbar with hMdef
  have hNM : N ≤ M := by
    have h1 : π.ker ≤ Subgroup.comap π Mbar := by
      rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
    rw [hker] at h1; exact h1
  refine ⟨M, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Subgroup.isOpen_mono hNM hNopen
  · intro htop
    apply hMcoatom.1
    have hmap : Subgroup.map π M = Mbar := Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar
    rw [← hmap, htop]
    exact Subgroup.map_top_of_surjective π hπsurj
  · intro K hKopen hMK
    have hNK : N ≤ K := le_trans hNM hMK
    have hMbarle : Mbar ≤ Subgroup.map π K := by
      have h : Subgroup.map π M ≤ Subgroup.map π K := Subgroup.map_mono (f := π) hMK
      rwa [Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar] at h
    have hcomapK : Subgroup.comap π (Subgroup.map π K) = K := by
      rw [Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNK
    rcases eq_or_lt_of_le hMbarle with heq | hlt
    · left
      rw [← hcomapK, ← heq]
    · right
      rw [← hcomapK, hMcoatom.2 _ hlt, Subgroup.comap_top]
  · calc H ≤ N0 := hHN0
      _ = Subgroup.comap π N0bar := hcomapN0.symm
      _ ≤ Subgroup.comap π Mbar := Subgroup.comap_mono hN0Mbar
      _ = M := hMdef.symm

/-- `Φ(G)` is normal (re-derived locally from R1, to avoid an import cycle with
`ProPGeneratorRankFrattini`). -/
theorem frattiniOpen_normal (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) : (frattiniOpen G).Normal := by
  rw [frattiniOpen]
  constructor
  intro n hn g
  rw [Subgroup.mem_sInf] at hn ⊢
  intro H hH
  obtain ⟨hnorm, _⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  exact hnorm.conj_mem n (hn H hH) g

/-- Every commutator lies in `Φ(G)`. -/
theorem commutator_mem_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) (x y : G) :
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
theorem pow_mem_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) (x : G) : x ^ p ∈ frattiniOpen G := by
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
theorem frattiniQuotient_comm (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) [(frattiniOpen G).Normal] :
    ∀ a b : G ⧸ frattiniOpen G, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using commutator_mem_frattini p G hpro hfg y⁻¹ x⁻¹

/-- `G/Φ(G)` has exponent dividing `p`. -/
theorem frattiniQuotient_expp (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) [(frattiniOpen G).Normal] :
    ∀ q : G ⧸ frattiniOpen G, q ^ p = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_mem_frattini p G hpro hfg x

end ProPTopologicalNakayamaAux

open ProPTopologicalNakayamaAux in
/-- **Topological Nakayama / Burnside basis, upper bound.** For a finitely generated pro-`p`
group `G` whose Frattini quotient has cardinality `p^d`, there is a topological generating
finset of `G` with at most `d` elements (obtained by lifting an `𝔽_p`-basis of `G/Φ(G)`). -/
theorem ProPTopologicalNakayama (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (d : ℕ) (hd : Nat.card (G ⧸ frattiniOpen G) = p ^ d) :
    ∃ S : Finset G, TopologicallyGenerates (↑S : Set G) ∧ S.card ≤ d := by
  classical
  haveI hN : (frattiniOpen G).Normal := frattiniOpen_normal p G hpro hfg
  haveI hQfin : Finite (G ⧸ frattiniOpen G) :=
    Nat.finite_of_card_ne_zero (by rw [hd]; exact pow_ne_zero d (Fact.out : p.Prime).pos.ne')
  letI : CommGroup (G ⧸ frattiniOpen G) :=
    { mul_comm := frattiniQuotient_comm p G hpro hfg }
  have hexp := frattiniQuotient_expp p G hpro hfg
  obtain ⟨T, hTcard, hTgen⟩ := exists_gen_finset p (G ⧸ frattiniOpen G) hexp d hd
  set π : G →* (G ⧸ frattiniOpen G) := QuotientGroup.mk' (frattiniOpen G) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set sec : (G ⧸ frattiniOpen G) → G := Function.surjInv hπsurj with hsec
  have hsecspec : ∀ t, π (sec t) = t := fun t => Function.surjInv_eq hπsurj t
  set S : Finset G := T.image sec with hS
  refine ⟨S, ?_, by rw [hS]; exact (Finset.card_image_le).trans hTcard⟩
  have hHtop : (Subgroup.closure (↑S : Set G)).topologicalClosure = ⊤ := by
    by_contra hne
    obtain ⟨M, hMmax, hHM⟩ := exists_maximalOpen_ge p G hpro
      ((Subgroup.closure (↑S : Set G)).topologicalClosure)
      (Subgroup.isClosed_topologicalClosure _) hne
    have hΦM : frattiniOpen G ≤ M := by rw [frattiniOpen]; exact sInf_le hMmax
    have hcomap : Subgroup.comap π (Subgroup.map π M) = M := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hΦM
    have hMbarne : Subgroup.map π M ≠ ⊤ := by
      intro htop
      apply hMmax.2.1
      have hc : Subgroup.comap π (Subgroup.map π M) = Subgroup.comap π ⊤ := by rw [htop]
      rwa [hcomap, Subgroup.comap_top] at hc
    have hTM : ∀ t ∈ T, t ∈ Subgroup.map π M := by
      intro t ht
      have hsecmem : sec t ∈ (Subgroup.closure (↑S : Set G)).topologicalClosure := by
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_closure
        rw [hS, Finset.coe_image]
        exact ⟨t, ht, rfl⟩
      have hmemM : sec t ∈ M := hHM hsecmem
      rw [← hsecspec t]
      exact Subgroup.mem_map_of_mem π hmemM
    have hle : (⊤ : Subgroup (G ⧸ frattiniOpen G)) ≤ Subgroup.map π M := by
      rw [← hTgen, Subgroup.closure_le]
      intro t ht
      exact hTM t (Finset.mem_coe.mp ht)
    exact hMbarne (top_le_iff.mp hle)
  show _root_.closure ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G) = Set.univ
  rw [← Subgroup.topologicalClosure_coe, hHtop, Subgroup.coe_top]
