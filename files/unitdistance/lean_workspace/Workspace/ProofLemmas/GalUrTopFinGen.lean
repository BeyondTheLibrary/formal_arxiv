-- Cited from: Neukirch, J., Schmidt, A., Wingberg, K. (2008). Cohomology of Number Fields, 2nd ed., Grundlehren der math. Wissenschaften 323, Springer. Chapter X, Section 10 (Galois groups of maximal unramified pro-p extensions of number fields are topologically finitely generated). See also Koch, H. (2002), Galois Theory of p-Extensions.
-- Paper label: [NSW08, Ch X, Section 10] (background to Prop A.10)
--
-- The only content admitted here is `GalUrFrattiniQuotientFinite`
--   GalUrFrattiniQuotientFinite : Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F))
-- (the unramified class-field-theory bridge: by the Artin map the Frattini quotient of Gal(F^{ur,3}/F)
-- is a quotient of Cl_F ⊗ Z/3Z, hence finite because the class group is finite; the Artin-map
-- correspondence itself is not currently in Mathlib).
--
-- Proof structure (reverse Burnside/Nakayama):
--   * `maxOpen_normal_index_p`: in a pro-p group every maximal proper open subgroup is normal of
--     index p.
--   * `frattini_normal` / `commutator_in_frattini` / `pow_in_frattini` / `frattini_quot_comm` /
--     `frattini_quot_expp`: the Frattini quotient G/Φ(G) is elementary abelian of exponent p, from the
--     above.
--   * `frattini_quot_card`: given `Finite (G/Φ(G))`, G/Φ(G) has order p^d.
--   * `nakayama_topfingen`: lift an F_p-basis of G/Φ(G) to a finset S ⊆ G (via
--     `ProPTopologicalNakayamaAux.exists_gen_finset`); the closed subgroup ⟨S⟩‾ maps onto G/Φ(G), and
--     if proper it would sit in a maximal open M ⊇ Φ(G) (the compactness step
--     `ProPTopologicalNakayamaAux.exists_maximalOpen_ge`) whose image in G/Φ(G) is a proper subgroup
--     containing all generators — contradiction. Hence S topologically generates G.
--   * Pro-3-ness of G = galUr 3 F is the lemma `Workspace.ProofLemmas.GalUrIsProP`.
--
-- NL statement: For every totally real cubic number field F, the Galois group galUr 3 F of the maximal everywhere-unramified pro-3 extension F^{ur,3}/F is topologically finitely generated: TopFinitelyGenerated (galUr 3 F), i.e. some finite subset of galUr 3 F topologically generates it.
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.ProPTopologicalNakayama
import Workspace.ProofLemmas.GalUrFrattiniQuotientFinite
import Workspace.ProofLemmas.GalUrIsProP

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000

namespace GalUrTopFinGenAux

/-- In a pro-`p` group `G`, every maximal proper open subgroup `H` is normal of index `p`. -/
theorem maxOpen_normal_index_p (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (H : Subgroup G) (hH : IsMaximalOpenSubgroup H) :
    H.Normal ∧ H.index = p := by
  obtain ⟨_, hcompact, _hT2, _hTD, hPindex⟩ := hpro
  haveI := hcompact
  obtain ⟨hHopen, hHne, hHmax⟩ := hH
  haveI hHfq : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI hHfi : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hNH : H.normalCore ≤ H := Subgroup.normalCore_le H
  have hHclosed : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hHopen
  have hNclosed : IsClosed (H.normalCore : Set G) := Subgroup.normalCore_isClosed H hHclosed
  have hNopen : IsOpen (H.normalCore : Set G) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex H.normalCore hNclosed
  obtain ⟨k, hk⟩ := hPindex H.normalCore inferInstance hNopen
  haveI hPfin : Finite (G ⧸ H.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  have hcardP : Nat.card (G ⧸ H.normalCore) = p ^ k := by
    rw [← Subgroup.index_eq_card]; exact hk
  haveI hPgroup : IsPGroup p (G ⧸ H.normalCore) := IsPGroup.of_card hcardP
  haveI hPnil : Group.IsNilpotent (G ⧸ H.normalCore) := hPgroup.isNilpotent
  have hNC : NormalizerCondition (G ⧸ H.normalCore) := normalizerCondition_of_isNilpotent
  set f := QuotientGroup.mk' H.normalCore with hfdef
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective H.normalCore
  have hker : f.ker = H.normalCore := QuotientGroup.ker_mk' H.normalCore
  set Hbar := Subgroup.map f H with hHbardef
  have hcomapHbar : Subgroup.comap f Hbar = H := by
    rw [hHbardef, Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNH
  have hcoatom : IsCoatom Hbar := by
    constructor
    · intro htop
      apply hHne
      have hc : Subgroup.comap f Hbar = Subgroup.comap f ⊤ := by rw [htop]
      rw [hcomapHbar, Subgroup.comap_top] at hc
      exact hc
    · intro Kbar hKbar
      have hNK : H.normalCore ≤ Subgroup.comap f Kbar := by
        have h1 : f.ker ≤ Subgroup.comap f Kbar := by
          rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
        rwa [hker] at h1
      have hKopen : IsOpen ((Subgroup.comap f Kbar) : Set G) := Subgroup.isOpen_mono hNK hNopen
      have hHK : H ≤ Subgroup.comap f Kbar :=
        Subgroup.map_le_iff_le_comap.mp (by rw [← hHbardef]; exact hKbar.le)
      have hmapK : Subgroup.map f (Subgroup.comap f Kbar) = Kbar :=
        Subgroup.map_comap_eq_self_of_surjective hfsurj Kbar
      rcases hHmax (Subgroup.comap f Kbar) hKopen hHK with hKH | hKtop
      · have hcontra : Kbar = Hbar := by rw [← hmapK, hKH, ← hHbardef]
        exact absurd hcontra.symm (ne_of_lt hKbar)
      · rw [← hmapK, hKtop]; exact Subgroup.map_top_of_surjective f hfsurj
  have hHbarNormal : Hbar.Normal := Subgroup.NormalizerCondition.normal_of_coatom Hbar hNC hcoatom
  haveI := hHbarNormal
  have hHnormal : H.Normal := by rw [← hcomapHbar]; exact hHbarNormal.comap f
  refine ⟨hHnormal, ?_⟩
  have hkerle : f.ker ≤ H := by rw [hker]; exact hNH
  have hmapidx : (Subgroup.map f H).index = H.index := H.index_map_eq hfsurj hkerle
  have hindexeq : H.index = Hbar.index := by rw [hHbardef]; exact hmapidx.symm
  rw [hindexeq]
  haveI hQnt : Nontrivial ((G ⧸ H.normalCore) ⧸ Hbar) :=
    QuotientGroup.nontrivial_iff.mpr hcoatom.1
  haveI hQpgroup : IsPGroup p ((G ⧸ H.normalCore) ⧸ Hbar) := hPgroup.to_quotient Hbar
  set g := QuotientGroup.mk' Hbar with hgdef
  have hgsurj : Function.Surjective g := QuotientGroup.mk'_surjective Hbar
  have hgker : g.ker = Hbar := QuotientGroup.ker_mk' Hbar
  have hsimple : ∀ K : Subgroup ((G ⧸ H.normalCore) ⧸ Hbar), K = ⊥ ∨ K = ⊤ := by
    intro K
    have hHbarK' : Hbar ≤ Subgroup.comap g K := by
      have h1 : g.ker ≤ Subgroup.comap g K := by
        rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
      rwa [hgker] at h1
    have hmapK' : Subgroup.map g (Subgroup.comap g K) = K :=
      Subgroup.map_comap_eq_self_of_surjective hgsurj K
    rcases eq_or_lt_of_le hHbarK' with heq | hlt
    · left
      rw [← hmapK', ← heq, Subgroup.map_eq_bot_iff]
      exact le_of_eq hgker.symm
    · right
      rw [← hmapK', hcoatom.2 (Subgroup.comap g K) hlt]
      exact Subgroup.map_top_of_surjective g hgsurj
  haveI hcenterNt : Nontrivial (Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar)) :=
    hQpgroup.center_nontrivial
  have hcenterTop : Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar) = ⊤ := by
    rcases hsimple (Subgroup.center _) with h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hcenterNt)
    · exact h
  have hcomm : ∀ a b : ((G ⧸ H.normalCore) ⧸ Hbar), a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.center _ := by rw [hcenterTop]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  letI : CommGroup ((G ⧸ H.normalCore) ⧸ Hbar) := { mul_comm := hcomm }
  haveI hQsimple : IsSimpleGroup ((G ⧸ H.normalCore) ⧸ Hbar) :=
    ⟨fun K _ => hsimple K⟩
  have hprime : (Nat.card ((G ⧸ H.normalCore) ⧸ Hbar)).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn0, hn⟩ := hQpgroup.nontrivial_iff_card.mp hQnt
  have hpdvd : p ∣ Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) := by
    rw [hn]; exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn0)
  have hpeq : p = Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) :=
    (Nat.prime_dvd_prime_iff_eq Fact.out hprime).mp hpdvd
  rw [Subgroup.index_eq_card]
  exact hpeq.symm

/-- `Φ(G)` is normal (from the hfg-free `maxOpen_normal_index_p`). -/
theorem frattini_normal (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G) :
    (frattiniOpen G).Normal := by
  rw [frattiniOpen]
  constructor
  intro n hn g
  rw [Subgroup.mem_sInf] at hn ⊢
  intro H hH
  obtain ⟨hnorm, _⟩ := maxOpen_normal_index_p p G hpro H hH
  haveI := hnorm
  exact hnorm.conj_mem n (hn H hH) g

/-- Every commutator lies in `Φ(G)`. -/
theorem commutator_in_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G) (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := maxOpen_normal_index_p p G hpro H hH
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
theorem pow_in_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G) (x : G) :
    x ^ p ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := maxOpen_normal_index_p p G hpro H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
  exact pow_card_eq_one'

/-- `G/Φ(G)` is abelian. -/
theorem frattini_quot_comm (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    [(frattiniOpen G).Normal] :
    ∀ a b : G ⧸ frattiniOpen G, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using commutator_in_frattini p G hpro y⁻¹ x⁻¹

/-- `G/Φ(G)` has exponent dividing `p`. -/
theorem frattini_quot_expp (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    [(frattiniOpen G).Normal] :
    ∀ q : G ⧸ frattiniOpen G, q ^ p = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_in_frattini p G hpro x

/-- `G/Φ(G)` is a finite elementary abelian `p`-group: its cardinality is `p^d`, using finiteness of
the Frattini quotient. -/
theorem frattini_quot_card (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfin : Finite (G ⧸ frattiniOpen G)) :
    ∃ d : ℕ, Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  haveI : (frattiniOpen G).Normal := frattini_normal p G hpro
  have hcomm := frattini_quot_comm p G hpro
  have hpow_all := frattini_quot_expp p G hpro
  haveI := hfin
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

/-- **Reverse Nakayama / Burnside.** A pro-`p` group `G` whose topological Frattini
quotient `G/Φ(G)` is finite is topologically finitely generated. Proof: `G/Φ(G)` is a finite
elementary abelian `p`-group of order `p^d`; lift an `𝔽_p`-basis to a finset `S ⊆ G` of size `≤ d`;
the closed subgroup `⟨S⟩‾` surjects onto `G/Φ(G)`, and if it were proper it would sit inside a
maximal open `M ⊇ Φ(G)` whose image in `G/Φ(G)` is a proper subgroup containing all generators —
contradiction. -/
theorem nakayama_topfingen (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfin : Finite (G ⧸ frattiniOpen G)) :
    TopFinitelyGenerated G := by
  classical
  haveI hN : (frattiniOpen G).Normal := frattini_normal p G hpro
  haveI hQfin : Finite (G ⧸ frattiniOpen G) := hfin
  letI : CommGroup (G ⧸ frattiniOpen G) := { mul_comm := frattini_quot_comm p G hpro }
  have hexp := frattini_quot_expp p G hpro
  obtain ⟨d, hd⟩ := frattini_quot_card p G hpro hfin
  obtain ⟨T, hTcard, hTgen⟩ :=
    ProPTopologicalNakayamaAux.exists_gen_finset p (G ⧸ frattiniOpen G) hexp d hd
  set π : G →* (G ⧸ frattiniOpen G) := QuotientGroup.mk' (frattiniOpen G) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set sec : (G ⧸ frattiniOpen G) → G := Function.surjInv hπsurj with hsec
  have hsecspec : ∀ t, π (sec t) = t := fun t => Function.surjInv_eq hπsurj t
  set S : Finset G := T.image sec with hS
  refine ⟨S, ?_⟩
  have hHtop : (Subgroup.closure (↑S : Set G)).topologicalClosure = ⊤ := by
    by_contra hne
    obtain ⟨M, hMmax, hHM⟩ := ProPTopologicalNakayamaAux.exists_maximalOpen_ge p G hpro
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

end GalUrTopFinGenAux

open GalUrTopFinGenAux in
/-- For a totally real cubic number field `F`, the Galois group `galUr 3 F` of the maximal
everywhere-unramified pro-`3` extension is topologically finitely generated. -/
theorem GalUrTopFinGen :
    ∀ (F : Type) [Field F] [NumberField F],
      NumberField.IsTotallyReal F → Module.finrank ℚ F = 3 →
        TopFinitelyGenerated (galUr 3 F) := by
  intro F _ _ _ _
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact nakayama_topfingen 3 (galUr 3 F) (GalUrIsProP F) (GalUrFrattiniQuotientFinite F)


