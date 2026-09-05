import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.AddPendantVertexTransport
import Workspace.ProofLemmas.AnticomponentOfSkewSideBasics
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect
import Workspace.ProofLemmas.PerfectCliqueBlowup
import Workspace.ProofLemmas.AddPendantVertexBerge
import Workspace.ProofLemmas.SkewComponentComplementHasTwoVertices
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.IsoTransport
import Workspace.Statements.S01.Thm_E5_perfect_implies_berge

/-!
# Claim (2) of the proof of 1.5

> *"(2) For `1 ≤ i ≤ m` there is a subset `Cᵢ ⊆ Aᵢ` such that `ω(Cᵢ ∪ B₁) = s` and
> `ω((Aᵢ \ Cᵢ) ∪ (B \ B₁)) ≤ t − s."*

with `s = ω(B₁)` and `t = ω(A ∪ B)`.

The statement mentions neither `G'` nor `H` nor the blow-up — it is purely about `G`,
`A`, `B`, `B₁` — so nothing of §5's machinery leaks into the interface.  Its proof is
§5.1–§5.5:

* `H := (G +ᵥ B₁)|(Sum.inl '' (B ∪ P) ∪ {z})` is Berge by
  `AddPendantVertexBerge.berge_addPendantVertex` and `HoleBasics.berge_induce`;
* `|V(H)| < |V(G)|`, because the vertices of `G` missing from `H` are exactly those
  of `A \ P`, of which there are at least two by
  `SkewComponentComplementHasTwoVertices.exists_two_mem_sdiff`, while `H` has only
  one new vertex;
* so `H` is perfect by `SmallerBergeGraphIsPerfect.isPerfect_of_berge_of_card_lt`;
* blow `ẑ` up to a clique `Z` of size exactly `t − s ≥ 1` by
  `PerfectCliqueBlowup.exists_blowup` (using `s < t` from
  `AnticomponentOfSkewSideBasics.cliqueNum_lt` plus monotonicity);
* everything after that is phrased through the single injection
  `κ : B ∪ P → V(H⁺)` and its four properties, so the vertex type of `H⁺` never
  reappears and no `induce` of an `induce` is ever formed;
* `ω(H⁺) ≤ t`, hence a proper `t`-colouring `c` exists
  (`CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect`); after normalising, the
  colour set splits as `S ⊎ c(Z)` with `|S| = s`; set `C := {v ∈ P | c(κ v) ∈ S}`.

The colour relabelling of §5.4 (*"we may assume colours `1, …, s` do not occur in
`Z`"*) is presentational: only the splitting `S ⊎ c(Z)` with `|S| = s`,
`|c(Z)| = t − s` is used, so performing or skipping the explicit `Equiv.Perm (Fin t)`
are both faithful.

If this node needs deepening later, the natural cut is at the end of §5.2: *"`H` is
perfect and `|V(H)| < |V(G)|`"* on one side, the `κ`-level colouring argument
§5.3–§5.5 on the other.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.ComponentCliqueNumSplit

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.AddPendantVertexTransport

/-- §5.3–§5.5 of the proof of 1.5, phrased entirely through the injection `κ` and the
clique `Z`, as the natural-language proof prescribes. -/
private theorem split_of_kappa {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B B₁ P : Set V}
    (hPA : P ⊆ A) (hB₁B : B₁ ⊆ B)
    (hcompl : Complete G B₁ (B \ B₁))
    {W' : Type*} [Fintype W'] [DecidableEq W'] {K' : SimpleGraph W'}
    {Z : Set W'} {κ : V → W'}
    (hκinj : ∀ u ∈ B ∪ P, ∀ v ∈ B ∪ P, κ u = κ v → u = v)
    (hκnotZ : ∀ u ∈ B ∪ P, κ u ∉ Z)
    (hcover : ∀ x : W', x ∈ Z ∨ ∃ u ∈ B ∪ P, κ u = x)
    (hZcard : Z.ncard = (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum)
    (hst : (G.induce B₁).cliqueNum ≤ (G.induce (A ∪ B)).cliqueNum)
    (hZclique : K'.IsClique Z)
    (hκadj : ∀ u ∈ B ∪ P, ∀ v ∈ B ∪ P, (K'.Adj (κ u) (κ v) ↔ G.Adj u v))
    (hZκ : ∀ w ∈ Z, ∀ u ∈ B ∪ P, (K'.Adj w (κ u) ↔ u ∈ B₁))
    (hperf : IsPerfect K') :
    ∃ C : Set V, C ⊆ P ∧
      (G.induce (C ∪ B₁)).cliqueNum = (G.induce B₁).cliqueNum ∧
      (G.induce ((P \ C) ∪ (B \ B₁))).cliqueNum ≤
        (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum := by
  classical
  have hBPsub : B ∪ P ⊆ A ∪ B := by
    intro u hu
    rcases hu with h | h
    · exact Or.inr h
    · exact Or.inl (hPA h)
  -- §5.3  every clique of `K'` has at most `t` vertices
  have hclique_bound : ∀ Kf : Finset W', K'.IsClique (↑Kf : Set W') →
      Kf.card ≤ (G.induce (A ∪ B)).cliqueNum := by
    intro Kf hKf
    have hLmem : ∀ u : V, u ∈ Finset.univ.filter (fun u => u ∈ B ∪ P ∧ κ u ∈ Kf) ↔
        (u ∈ B ∪ P ∧ κ u ∈ Kf) := by
      intro u; simp
    set L : Finset V := Finset.univ.filter (fun u => u ∈ B ∪ P ∧ κ u ∈ Kf) with hLdef
    have hLinj : Set.InjOn κ (↑L : Set V) := by
      intro u hu v hv huv
      exact hκinj u ((hLmem u).mp hu).1 v ((hLmem v).mp hv).1 huv
    have hLclique : G.IsClique (↑L : Set V) := by
      intro u hu v hv huv
      have hu' := (hLmem u).mp hu
      have hv' := (hLmem v).mp hv
      exact (hκadj u hu'.1 v hv'.1).mp
        (hKf (Finset.mem_coe.mpr hu'.2) (Finset.mem_coe.mpr hv'.2)
          (fun h => huv (hκinj u hu'.1 v hv'.1 h)))
    have hsplit : Kf.filter (fun x => x ∉ Z) = L.image κ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hxK, hxZ⟩
        rcases hcover x with h | ⟨u, hu, rfl⟩
        · exact absurd h hxZ
        · exact ⟨u, (hLmem u).mpr ⟨hu, hxK⟩, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨((hLmem u).mp hu).2, hκnotZ u ((hLmem u).mp hu).1⟩
    have hcard1 : (Kf.filter (fun x => x ∉ Z)).card = L.card := by
      rw [hsplit, Finset.card_image_of_injOn hLinj]
    have hcard2 : (Kf.filter (fun x => x ∈ Z)).card + (Kf.filter (fun x => x ∉ Z)).card
        = Kf.card := Finset.card_filter_add_card_filter_not _
    have hZbound : (Kf.filter (fun x => x ∈ Z)).card ≤ Z.ncard := by
      rw [Set.ncard_eq_toFinset_card' Z]
      refine Finset.card_le_card ?_
      intro x hx
      simp only [Finset.mem_filter] at hx
      simpa using hx.2
    by_cases hZmeet : ∃ w ∈ Kf, w ∈ Z
    · obtain ⟨w, hwK, hwZ⟩ := hZmeet
      have hLB₁ : (↑L : Set V) ⊆ B₁ := by
        intro u hu
        have hu' := (hLmem u).mp hu
        refine (hZκ w hwZ u hu'.1).mp (hKf (Finset.mem_coe.mpr hwK)
          (Finset.mem_coe.mpr hu'.2) ?_)
        intro h
        exact (hκnotZ u hu'.1) (h ▸ hwZ)
      have hLs : L.card ≤ (G.induce B₁).cliqueNum :=
        CliqueNumOfInducedSet.card_le_cliqueNum_induce G hLB₁ hLclique
      omega
    · push Not at hZmeet
      have hempty : Kf.filter (fun x => x ∈ Z) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        exact hZmeet x
      have hLt : L.card ≤ (G.induce (A ∪ B)).cliqueNum :=
        CliqueNumOfInducedSet.card_le_cliqueNum_induce G
          (fun u hu => hBPsub ((hLmem u).mp hu).1) hLclique
      rw [hempty, Finset.card_empty] at hcard2
      omega
  have hωK' : K'.cliqueNum ≤ (G.induce (A ∪ B)).cliqueNum := by
    obtain ⟨Kf, hKf⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := K')
    rw [← hKf.2]
    exact hclique_bound Kf hKf.1
  obtain ⟨c⟩ : K'.Colorable (G.induce (A ∪ B)).cliqueNum :=
    SimpleGraph.Colorable.mono hωK'
      (CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect K' hperf)
  -- §5.4  the colour set splits as `S ⊎ c(Z)` with `|S| = s`
  have hZFcard : Z.toFinset.card = Z.ncard := (Set.ncard_eq_toFinset_card' Z).symm
  have hcinjZ : Set.InjOn c (↑Z.toFinset : Set W') := by
    intro a ha b hb hab
    by_contra hne
    exact c.valid (hZclique (by simpa using ha) (by simpa using hb) hne) hab
  set cZ : Finset (Fin (G.induce (A ∪ B)).cliqueNum) := Z.toFinset.image c with hcZdef
  have hcZcard : cZ.card = Z.ncard := by
    rw [hcZdef, Finset.card_image_of_injOn hcinjZ, hZFcard]
  set S : Finset (Fin (G.induce (A ∪ B)).cliqueNum) := Finset.univ \ cZ with hSdef
  have hSiff : ∀ γ, γ ∈ S ↔ γ ∉ cZ := by intro γ; simp [hSdef]
  have hScard : S.card = (G.induce B₁).cliqueNum := by
    rw [hSdef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, hcZcard, hZcard]
    omega
  have hB₁S : ∀ u ∈ B₁, c (κ u) ∈ S := by
    intro u hu
    rw [hSiff]
    rw [hcZdef]
    simp only [Finset.mem_image]
    rintro ⟨w, hw, hcw⟩
    have hwZ : w ∈ Z := by simpa using hw
    exact c.valid ((hZκ w hwZ u (Or.inl (hB₁B hu))).mpr hu) hcw
  have hSonB₁ : ∀ γ ∈ S, ∃ u ∈ B₁, c (κ u) = γ := by
    obtain ⟨K₀, hK₀B₁, hK₀cl, hK₀card⟩ :=
      CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G B₁
    have hinj : Set.InjOn (fun u => c (κ u)) (↑K₀ : Set V) := by
      intro u hu v hv huv
      by_contra hne
      exact c.valid ((hκadj u (Or.inl (hB₁B (hK₀B₁ hu))) v
        (Or.inl (hB₁B (hK₀B₁ hv)))).mpr (hK₀cl hu hv hne)) huv
    have himg : K₀.image (fun u => c (κ u)) ⊆ S := by
      intro γ hγ
      simp only [Finset.mem_image] at hγ
      obtain ⟨u, hu, rfl⟩ := hγ
      exact hB₁S u (hK₀B₁ (by simpa using hu))
    have hcard : (K₀.image (fun u => c (κ u))).card = S.card := by
      rw [Finset.card_image_of_injOn hinj, hK₀card, hScard]
    have heq : K₀.image (fun u => c (κ u)) = S :=
      Finset.eq_of_subset_of_card_le himg (le_of_eq hcard.symm)
    intro γ hγ
    rw [← heq] at hγ
    simp only [Finset.mem_image] at hγ
    obtain ⟨u, hu, huγ⟩ := hγ
    exact ⟨u, hK₀B₁ (by simpa using hu), huγ⟩
  have hBnotB₁ : ∀ v ∈ B \ B₁, c (κ v) ∉ S := by
    intro v hv hcv
    obtain ⟨u, huB₁, hu⟩ := hSonB₁ _ hcv
    exact c.valid ((hκadj u (Or.inl (hB₁B huB₁)) v (Or.inl hv.1)).mpr
      (hcompl u huB₁ v hv)) hu
  -- §5.5  `C := { v ∈ P : c (κ v) ∈ S }`
  refine ⟨{v | v ∈ P ∧ c (κ v) ∈ S}, fun v hv => hv.1, ?_, ?_⟩
  · refine le_antisymm ?_ (CliqueNumOfInducedSet.cliqueNum_induce_mono G Set.subset_union_right)
    obtain ⟨K, hKsub, hKcl, hKcard⟩ :=
      CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G
        ({v | v ∈ P ∧ c (κ v) ∈ S} ∪ B₁)
    rw [← hKcard]
    have hKBP : ∀ v ∈ (↑K : Set V), v ∈ B ∪ P := by
      intro v hv
      rcases hKsub hv with h | h
      · exact Or.inr h.1
      · exact Or.inl (hB₁B h)
    have hKS : ∀ v ∈ (↑K : Set V), c (κ v) ∈ S := by
      intro v hv
      rcases hKsub hv with h | h
      · exact h.2
      · exact hB₁S v h
    have hinj : Set.InjOn (fun u => c (κ u)) (↑K : Set V) := by
      intro u hu v hv huv
      by_contra hne
      exact c.valid ((hκadj u (hKBP u hu) v (hKBP v hv)).mpr (hKcl hu hv hne)) huv
    calc K.card = (K.image (fun u => c (κ u))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ S.card := by
          refine Finset.card_le_card ?_
          intro γ hγ
          simp only [Finset.mem_image] at hγ
          obtain ⟨u, hu, rfl⟩ := hγ
          exact hKS u (by simpa using hu)
      _ = (G.induce B₁).cliqueNum := hScard
  · obtain ⟨K, hKsub, hKcl, hKcard⟩ :=
      CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G
        ((P \ {v | v ∈ P ∧ c (κ v) ∈ S}) ∪ (B \ B₁))
    rw [← hKcard]
    have hKBP : ∀ v ∈ (↑K : Set V), v ∈ B ∪ P := by
      intro v hv
      rcases hKsub hv with h | h
      · exact Or.inr h.1
      · exact Or.inl h.1
    have hKcZ : ∀ v ∈ (↑K : Set V), c (κ v) ∈ cZ := by
      intro v hv
      rcases hKsub hv with h | h
      · by_contra hc
        exact h.2 ⟨h.1, (hSiff _).mpr hc⟩
      · by_contra hc
        exact hBnotB₁ v h ((hSiff _).mpr hc)
    have hinj : Set.InjOn (fun u => c (κ u)) (↑K : Set V) := by
      intro u hu v hv huv
      by_contra hne
      exact c.valid ((hκadj u (hKBP u hu) v (hKBP v hv)).mpr (hKcl hu hv hne)) huv
    calc K.card = (K.image (fun u => c (κ u))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ cZ.card := by
          refine Finset.card_le_card ?_
          intro γ hγ
          simp only [Finset.mem_image] at hγ
          obtain ⟨u, hu, rfl⟩ := hγ
          exact hKcZ u (by simpa using hu)
      _ = (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum := by
          rw [hcZcard, hZcard]

/-- **Claim (2)**.  With `s = (G.induce B₁).cliqueNum` and
`t = (G.induce (A ∪ B)).cliqueNum`, every component `P` of `A` splits as `C ∪ (P \ C)`
so that `ω(C ∪ B₁) = s` and `ω((P \ C) ∪ (B \ B₁)) ≤ t − s`. -/
theorem exists_subset_cliqueNum_split {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : MinimumImperfect G) {A B : Set V}
    (hAB : IsBalancedSkewPartition G A B) {B₁ : Set V}
    (hB₁ : IsAnticomponent G B B₁) {P : Set V} (hP : IsComponent G A P) :
    ∃ C : Set V, C ⊆ P ∧
      (G.induce (C ∪ B₁)).cliqueNum = (G.induce B₁).cliqueNum ∧
      (G.induce ((P \ C) ∪ (B \ B₁))).cliqueNum ≤
        (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum := by
  classical
  obtain ⟨hskew, hbal⟩ := hAB
  obtain ⟨hABuniv, hABdisj, hAnotconn, hBnotanti⟩ := hskew
  have hPA : P ⊆ A := hP.1
  have hB₁B : B₁ ⊆ B := hB₁.1
  have hcompl : Complete G B₁ (B \ B₁) :=
    AnticomponentOfSkewSideBasics.complete_sdiff G hB₁
  -- `s < t` (P8 plus monotonicity), so `t - s ≥ 1`
  have hst : (G.induce B₁).cliqueNum < (G.induce (A ∪ B)).cliqueNum :=
    lt_of_lt_of_le (AnticomponentOfSkewSideBasics.cliqueNum_lt G hB₁ hBnotanti)
      (CliqueNumOfInducedSet.cliqueNum_induce_mono G Set.subset_union_right)
  -- §5.1  `H` is Berge
  have hBergeG : Berge G :=
    IsoTransport.minimumImperfect_berge hG
      (fun hp => Workspace.MainTheorem.SPGT.thm_E5_perfect_implies_berge G hp)
  have hBergeG' : Berge (addPendantVertex G B₁) :=
    AddPendantVertexBerge.berge_addPendantVertex hBergeG hABuniv hbal hB₁
  set W : Set (V ⊕ Unit) := Sum.inl '' (B ∪ P) ∪ {Sum.inr ()} with hWdef
  have hBergeH : Berge ((addPendantVertex G B₁).induce W) :=
    HoleBasics.berge_induce hBergeG' W
  -- §5.1  `|V(H)| < |V(G)|`
  have hWmem : ∀ u : V, u ∈ B ∪ P → (Sum.inl u : V ⊕ Unit) ∈ W :=
    fun u h => Or.inl ⟨u, h, rfl⟩
  have hWncard : W.ncard = (B ∪ P).ncard + 1 := by
    rw [hWdef, Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_singleton]
    rw [Set.disjoint_left]
    rintro x ⟨u, -, rfl⟩ hx
    exact Sum.inl_ne_inr hx
  have hUniv : (Set.univ : Set V) = (B ∪ P) ∪ (A \ P) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_diff, true_iff]
    rcases (hABuniv ▸ Set.mem_univ x : x ∈ A ∪ B) with h | h
    · by_cases hxP : x ∈ P
      · exact Or.inl (Or.inr hxP)
      · exact Or.inr ⟨h, hxP⟩
    · exact Or.inl (Or.inl h)
  have hcardV : Fintype.card V = (B ∪ P).ncard + (A \ P).ncard := by
    have h1 : (Set.univ : Set V).ncard = Fintype.card V := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    rw [← h1, hUniv, Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _)]
    rw [Set.disjoint_left]
    rintro x (hx | hx) ⟨hxA, hxP⟩
    · exact (Set.disjoint_left.mp hABdisj hxA) hx
    · exact hxP hx
  have htwo : 2 ≤ (A \ P).ncard := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      SkewComponentComplementHasTwoVertices.exists_two_mem_sdiff hG
        ⟨hABuniv, hABdisj, hAnotconn, hBnotanti⟩ hP
    have hsub : ({a, b} : Set V) ⊆ A \ P := by
      rintro x (rfl | rfl)
      · exact ha
      · exact hb
    calc 2 = ({a, b} : Set V).ncard := (Set.ncard_pair hab).symm
      _ ≤ (A \ P).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcardW : Fintype.card ↥W < Fintype.card V := by
    have h2 : Fintype.card ↥W = W.ncard := by
      rw [Set.ncard_eq_toFinset_card' W, Set.toFinset_card]
    omega
  -- §5.2  `H` is perfect, and `z` blows up to a clique `Z` of size `t - s`
  have hHperf : IsPerfect ((addPendantVertex G B₁).induce W) :=
    SmallerBergeGraphIsPerfect.isPerfect_of_berge_of_card_lt hG _ hBergeH hcardW
  obtain ⟨W', hFin, hDec, K', Z, ζ, hζinj, hζdisj, hζcover, hZcard, hZclique,
    hζadj, hZadj, hζperf⟩ :=
    PerfectCliqueBlowup.exists_blowup ((addPendantVertex G B₁).induce W)
      (⟨Sum.inr (), Or.inr rfl⟩ : ↥W)
      (show 1 ≤ (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum by omega)
  letI : Fintype W' := hFin
  letI : DecidableEq W' := hDec
  obtain ⟨z₀, hz₀⟩ : Z.Nonempty := (Set.ncard_pos (Set.toFinite Z)).mp (by omega)
  -- the injection `κ : B ∪ P → V(H⁺)`
  have hne : ∀ (u : V) (h : u ∈ B ∪ P),
      (⟨Sum.inl u, hWmem u h⟩ : ↥W) ≠ (⟨Sum.inr (), Or.inr rfl⟩ : ↥W) :=
    fun u h hh => Sum.inl_ne_inr (congrArg Subtype.val hh)
  set κ : V → W' := fun u =>
    if h : u ∈ B ∪ P then ζ ⟨⟨Sum.inl u, hWmem u h⟩, hne u h⟩ else z₀ with hκdef
  have hκval : ∀ (u : V) (h : u ∈ B ∪ P),
      κ u = ζ ⟨⟨Sum.inl u, hWmem u h⟩, hne u h⟩ := by
    intro u h
    rw [hκdef]
    exact dif_pos h
  refine split_of_kappa (G := G) (A := A) (B := B) (B₁ := B₁) (P := P)
    hPA hB₁B hcompl (K' := K') (Z := Z) (κ := κ) ?_ ?_ ?_ hZcard (le_of_lt hst)
    hZclique ?_ ?_ (hζperf hHperf)
  · -- κ is injective on `B ∪ P`
    intro u hu v hv huv
    rw [hκval u hu, hκval v hv] at huv
    have := congrArg Subtype.val (congrArg Subtype.val (hζinj huv))
    exact Sum.inl_injective this
  · -- κ misses `Z`
    intro u hu
    rw [hκval u hu]
    exact Set.disjoint_left.mp hζdisj ⟨_, rfl⟩
  · -- `V(H⁺)` is covered by `Z` and the image of `κ`
    intro x
    rcases (hζcover ▸ Set.mem_univ x : x ∈ Set.range ζ ∪ Z) with ⟨a, rfl⟩ | hxZ
    · refine Or.inr ?_
      obtain ⟨u, hu, hval⟩ : ∃ u : V, u ∈ B ∪ P ∧ (a : ↥W).1 = Sum.inl u := by
        obtain ⟨⟨y, hyW⟩, hyne⟩ := a
        rcases y with y | uu
        · rcases hyW with ⟨u, hu, heq⟩ | hs
          · exact ⟨y, (Sum.inl_injective heq) ▸ hu, rfl⟩
          · exact absurd hs (by simp)
        · exact absurd (Subtype.ext (by cases uu; rfl)) hyne
      refine ⟨u, hu, ?_⟩
      rw [hκval u hu]
      congr 1
      exact Subtype.ext (Subtype.ext hval.symm)
    · exact Or.inl hxZ
  · -- κ reflects adjacency
    intro u hu v hv
    rw [hκval u hu, hκval v hv]
    exact hζadj _ _
  · -- every member of `Z` is adjacent to exactly the `κ`-image of `B₁`
    intro w hw u hu
    rw [hκval u hu]
    exact hZadj w hw _

end Workspace.ProofLemmas.ComponentCliqueNumSplit
