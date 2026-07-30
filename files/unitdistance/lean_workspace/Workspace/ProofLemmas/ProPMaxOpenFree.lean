import Mathlib
import Workspace.Types.ProPGroup

/-!
# `hfg`-free maximality lemma for pro-`p` groups (shared auxiliary)

`maxOpen_normal_index_p` : in a pro-`p` group every maximal proper *open* subgroup is normal of
index `p`.  This is the `TopFinitelyGenerated`-free form of `ProPMaximalOpenNormalIndexP`; it is
extracted into its own file so that both `GalUrFrattiniQuotientFinite` and `GalUrTopFinGen` can use
it without circularity (the frozen sibling `ProPMaximalOpenNormalIndexP` carries a spurious
`TopFinitelyGenerated G` hypothesis, which is exactly what those two results are proving).
-/

set_option maxHeartbeats 800000

open Workspace.Types.ProPGroup

namespace Workspace.ProofLemmas.ProPMaxOpenFree

/-- (hfg-free re-derivation of R1 `ProPMaximalOpenNormalIndexP`.) In a pro-`p` group `G`, every
maximal proper open subgroup `H` is normal of index `p`. The original sibling carries a spurious
`TopFinitelyGenerated G` hypothesis (unused in its proof); we re-derive it here without that
hypothesis so it can be used to *prove* topological finite generation without circularity. -/
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


end Workspace.ProofLemmas.ProPMaxOpenFree
