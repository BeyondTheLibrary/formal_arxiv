-- Cited from: Ribes, L., Zalesskii, P. (2010). Profinite Groups, 2nd ed., Ergebnisse der Math. 40,
-- Springer. The existence of a descending chain of open normal subgroups of index tending to
-- infinity inside an infinite, topologically finitely generated pro-p group.
--
-- The chain does NOT require the pro-p Frattini/lower-central series:
-- for an INFINITE PROFINITE group `Gbar = G ⧸ N` (compact, Hausdorff, totally disconnected topological
-- group — all supplied by `IsProP 3`) the open normal subgroups form a neighbourhood basis of `1`
-- and hence separate points. Build the chain by iterated intersection: starting from `⊤`, given an
-- open normal subgroup `K` of finite index, `K` is INFINITE (finite index in the infinite `Gbar`), so it
-- contains some `g ≠ 1`; profiniteness gives an open normal `U` with `g ∉ U`, and `K ⊓ U` is again
-- open, normal, of finite index, and strictly smaller than `K` (it omits `g`). Strict descent forces
-- the indices to strictly increase (`Subgroup.index_strictAnti`), so they tend to `∞` for free
-- (`StrictMono.tendsto_atTop`). Pulling everything back along the (continuous, surjective) quotient
-- map `G ↠ Gbar` produces open normal subgroups of `G` above `N` with the same indices. Neither the
-- pro-p hypothesis nor topological finite generation is needed for the construction — only
-- infiniteness and the profinite structure carried by `IsProP 3`.
-- Paper label: [RZ10] Profinite Groups (descending open-normal chains in infinite f.g. pro-p groups)
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup

set_option maxHeartbeats 800000

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

/-- A layer of the descending chain: an open, normal subgroup of finite index. -/
private structure DescChainLayer (Gbar : Type*) [Group Gbar] [TopologicalSpace Gbar] : Type _ where
  carrier : Subgroup Gbar
  hopen : IsOpen (carrier : Set Gbar)
  hnorm : carrier.Normal
  hfi : carrier.FiniteIndex

/-- In an infinite profinite group, any open-normal finite-index subgroup strictly contains a
smaller open-normal finite-index subgroup. -/
private lemma descChain_exists_smaller
    {Gbar : Type*} [Group Gbar] [TopologicalSpace Gbar] [IsTopologicalGroup Gbar]
    [CompactSpace Gbar] [T2Space Gbar] [TotallyDisconnectedSpace Gbar] [Infinite Gbar]
    (l : DescChainLayer Gbar) : ∃ l' : DescChainLayer Gbar, l'.carrier < l.carrier := by
  haveI := l.hnorm
  haveI := l.hfi
  -- `l.carrier` is infinite (finite index in the infinite `Gbar`)
  have hGbar0 : Nat.card Gbar = 0 := Nat.card_eq_zero_of_infinite
  have hcard0 : Nat.card l.carrier = 0 := by
    have h := Subgroup.card_mul_index l.carrier
    rw [hGbar0] at h
    exact (Nat.mul_eq_zero.mp h).resolve_right l.hfi.index_ne_zero
  haveI hInfK : Infinite l.carrier := by
    rcases Nat.card_eq_zero.mp hcard0 with h | h
    · exact absurd (⟨(1 : l.carrier)⟩ : Nonempty l.carrier) (not_nonempty_iff.mpr h)
    · exact h
  have hne : ∃ g : Gbar, g ∈ l.carrier ∧ g ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : l.carrier)
    refine ⟨x, x.2, ?_⟩
    intro hc
    apply hx
    exact Subtype.ext hc
  obtain ⟨g, hgK, hg_ne⟩ := hne
  -- an open normal subgroup `U` avoiding `g`
  have hgc_open : IsOpen ({g}ᶜ : Set Gbar) := isOpen_compl_singleton
  have h1mem : (1 : Gbar) ∈ ({g}ᶜ : Set Gbar) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun hc => hg_ne hc.symm
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hgc_open h1mem
  haveI hUnorm : (U : Subgroup Gbar).Normal := U.isNormal'
  have hUopen : IsOpen ((U : Subgroup Gbar) : Set Gbar) := U.toOpenSubgroup.isOpen
  have hgU : g ∉ (U : Subgroup Gbar) := by
    intro hmem
    have hmem' : g ∈ (U : Set Gbar) := hmem
    exact (hU hmem') rfl
  -- the smaller layer `K ⊓ U`
  have hK'open : IsOpen ((l.carrier ⊓ (U : Subgroup Gbar) : Subgroup Gbar) : Set Gbar) := by
    rw [Subgroup.coe_inf]; exact l.hopen.inter hUopen
  refine ⟨⟨l.carrier ⊓ (U : Subgroup Gbar), hK'open, inferInstance, ?_⟩, ?_⟩
  · haveI : Finite (Gbar ⧸ (l.carrier ⊓ (U : Subgroup Gbar))) :=
      Subgroup.quotient_finite_of_isOpen _ hK'open
    exact Subgroup.finiteIndex_of_finite_quotient
  · apply lt_of_le_of_ne inf_le_left
    intro heq
    have hgK' : g ∈ l.carrier ⊓ (U : Subgroup Gbar) := by rw [heq]; exact hgK
    exact hgU (Subgroup.mem_inf.mp hgK').2

/-- **Descending open-normal chain in an infinite profinite group.** -/
private lemma descChain_main
    (Gbar : Type*) [Group Gbar] [TopologicalSpace Gbar] [IsTopologicalGroup Gbar]
    [CompactSpace Gbar] [T2Space Gbar] [TotallyDisconnectedSpace Gbar] [Infinite Gbar] :
    ∃ K : ℕ → Subgroup Gbar, (∀ j, (K j).Normal) ∧ (∀ j, IsOpen (K j : Set Gbar)) ∧
      K 0 = ⊤ ∧ StrictAnti K ∧ (∀ j, 0 < (K j).index) := by
  have Hstep : ∀ l : DescChainLayer Gbar, ∃ l' : DescChainLayer Gbar, l'.carrier < l.carrier :=
    fun l => descChain_exists_smaller l
  choose next hnext using Hstep
  let base : DescChainLayer Gbar :=
    { carrier := ⊤
      hopen := by rw [Subgroup.coe_top]; exact isOpen_univ
      hnorm := inferInstance
      hfi := ⟨by rw [Subgroup.index_top]; exact one_ne_zero⟩ }
  let chain : ℕ → DescChainLayer Gbar := fun n => Nat.rec base (fun _ l => next l) n
  refine ⟨fun n => (chain n).carrier, fun n => (chain n).hnorm, fun n => (chain n).hopen, rfl, ?_,
    fun n => Nat.pos_of_ne_zero (chain n).hfi.index_ne_zero⟩
  apply strictAnti_nat_of_succ_lt
  intro n
  exact hnext (chain n)

/-- **Descending open-normal chain in an infinite finitely generated pro-`3` quotient.**

For every number field `F`, writing `G := galUr 3 F`, whenever a quotient `Gbar = G ⧸ N` (for a closed
normal subgroup `N ≤ G`) is infinite, topologically finitely generated and pro-`3`, there is a chain
`H : ℕ → Subgroup G` of open normal subgroups above `N` with `H 0 = ⊤`, strictly decreasing, each of
finite index, whose indices tend to infinity.

Discharged from Mathlib alone: the profinite structure carried by `IsProP 3` makes the open normal
subgroups of `Gbar` separate points, so an iterated-intersection construction produces a strictly
descending chain of open normal finite-index subgroups; strict descent forces the indices to `→ ∞`,
and pulling back along `G ↠ Gbar` yields the chain in `G` above `N`. -/
theorem UnramifiedProPDescendingChain :
    ∀ (F : Type*) [Field F] [NumberField F],
      ∀ (N : Subgroup (galUr 3 F)) (hNnorm : N.Normal),
          IsClosed (N : Set (galUr 3 F)) →
            letI := hNnorm
            Infinite (galUr 3 F ⧸ N) →
              TopFinitelyGenerated (galUr 3 F ⧸ N) →
                IsProP 3 (galUr 3 F ⧸ N) →
                  ∃ H : ℕ → Subgroup (galUr 3 F),
                    (∀ j, (H j).Normal) ∧
                      (∀ j, IsOpen ((H j : Set (galUr 3 F)))) ∧
                        (∀ j, N ≤ H j) ∧
                          H 0 = ⊤ ∧
                            StrictAnti H ∧
                              (∀ j, 0 < (H j).index) ∧
                                Filter.Tendsto (fun j => (H j).index)
                                  Filter.atTop Filter.atTop := by
  intro F instF instNF N hNnorm hNclosed
  letI := hNnorm
  intro hInf hFG hProP
  obtain ⟨hTG, hCompact, hT2, hTD, _hpow⟩ := hProP
  haveI := hTG
  haveI := hCompact
  haveI := hT2
  haveI := hTD
  haveI := hInf
  obtain ⟨K, hKnorm, hKopen, hK0, hKanti, hKidx⟩ := descChain_main (galUr 3 F ⧸ N)
  set q := QuotientGroup.mk' N with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hqcont : Continuous q := by rw [hq, QuotientGroup.coe_mk']; exact QuotientGroup.continuous_mk
  -- comap strict-mono on subgroups (via surjectivity)
  have hcs : ∀ {A B : Subgroup (galUr 3 F ⧸ N)}, A < B → A.comap q < B.comap q := by
    intro A B h
    apply lt_of_le_of_ne (Subgroup.comap_mono h.le)
    intro heq
    have hAB : A = B := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hqsurj A,
          ← Subgroup.map_comap_eq_self_of_surjective hqsurj B, heq]
    exact absurd hAB (ne_of_lt h)
  refine ⟨fun j => (K j).comap q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => (hKnorm j).comap q
  · intro j
    have hpre : (((K j).comap q) : Set (galUr 3 F)) = q ⁻¹' (K j : Set _) := rfl
    rw [hpre]; exact (hKopen j).preimage hqcont
  · intro j n hn
    rw [Subgroup.mem_comap]
    have : q n = 1 := by rw [hq, QuotientGroup.coe_mk', QuotientGroup.eq_one_iff]; exact hn
    rw [this]; exact one_mem _
  · show Subgroup.comap q (K 0) = ⊤
    rw [hK0]; exact Subgroup.comap_top q
  · intro a b hab
    exact hcs (hKanti hab)
  · intro j
    rw [Subgroup.index_comap_of_surjective _ hqsurj]
    exact hKidx j
  · have hmono : StrictMono (fun j => (K j).index) := by
      apply strictMono_nat_of_lt_succ
      intro n
      haveI : (K (n + 1)).FiniteIndex := ⟨(hKidx (n + 1)).ne'⟩
      exact Subgroup.index_strictAnti (hKanti (Nat.lt_succ_self n))
    have hfun : (fun j => ((K j).comap q).index) = (fun j => (K j).index) := by
      funext j; exact Subgroup.index_comap_of_surjective _ hqsurj
    rw [hfun]
    exact hmono.tendsto_atTop
