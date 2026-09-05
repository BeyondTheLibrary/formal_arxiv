import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim2Transfer
import Workspace.ProofLemmas.Thm192Claim2Heredity
import Workspace.ProofLemmas.Thm192Claim2RimPath
import Workspace.ProofLemmas.Thm192Infra

/-!
# The localized induction of 19.2 (2), for an arbitrary smaller hub

`Thm192Claim2Localization.inductive_wheel_with_rim_in_A` runs the induction of claim (2)
of 19.2 inside the graph induced on `A ∪ {x₀,x₁,x₂,z} ∪ Y₀` with the frame `(z,A)`, for
the one hub `Y₀ = Y \ {y}` that claim (2) needs.  Nothing in that argument uses the shape
of `Y₀`: it only uses that `Y₀ ⊆ Y` is anticonnected, that `x₂` is not `Y₀`-complete, and
that `Y₀` is smaller than `Y`, so that the induction on `|Y|` applies.  This file is the
same argument for an arbitrary such `Y₀`, together with the consequence that claim (9)
needs: **two distinct vertices of `A` are `Y₀`-complete**.

That consequence is the printed sentence of claim (1) — *"by the minimality of `|Y|` there
is a `Y \ {y₂}`-complete vertex in `A`"* — read for a general smaller hub, and it is what
supplies the second neighbour in `A` of a vertex of `Y₀`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim9YAdjX2TwoComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT Workspace.ProofLemmas.Thm192Setup
open Workspace.ProofLemmas.Thm192Claim2Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex of a connected set with no neighbour in that set is its only vertex. -/
theorem eq_of_connected_isolated {H : SimpleGraph V} {B : Set V} (hB : ConnectedSet H B)
    {w : V} (hw : w ∈ B) (hiso : ∀ u ∈ B, ¬ H.Adj w u) : ∀ u ∈ B, u = w := by
  intro u hu
  obtain ⟨p⟩ := hB ⟨w, hw⟩ ⟨u, hu⟩
  cases p with
  | nil => rfl
  | @cons _ v _ hadj q => exact absurd hadj (hiso v.1 v.2)

/-- `z` belongs to no `Aᵢ`: a connected set containing `A₀` and no neighbour of `z`
cannot contain `z`, since `A₀` is nonempty and misses `z`. -/
theorem z_notMem_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i : ℕ}
    (hframe : IsFrame G z A₀) : z ∉ wheelSystemA G z A₀ x i := by
  intro hz
  obtain ⟨B, ⟨hA0, hBc, hBz, -⟩, hzB⟩ := mem_wheelSystemA hz
  obtain ⟨a, ha⟩ := hframe.1
  have hae : a = z := eq_of_connected_isolated hBc hzB (fun u hu => hBz u hu) a (hA0 ha)
  exact hframe.2.2.1 (hae ▸ ha)

/-- **PAPER** (printed p. 118, claim (2)): *"From the minimality of `|Y|`, `z` is
`Y₀`-complete and therefore `Y`-complete, and there is a path as in the claim."*

The wheel supplied by the smaller-hub induction, applied inside the graph induced on
`A ∪ {x₀,x₁,x₂,z} ∪ Y₀` with the frame `(z,A)`. -/
theorem inductive_wheel_with_rim_in_A (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (Y₀ : Set V) (hY₀Y : Y₀ ⊆ Y) (hY0 : AnticonnectedSet G Y₀)
    (hx2 : ¬ VertexComplete G (x 2) Y₀)
    (hcard0 : Y₀.ncard < Y.ncard) :
    ∃ C : List V, IsWheel G C Y₀ ∧
      x 0 ∈ C ∧ x 1 ∈ C ∧ z ∈ C ∧
      {v : V | v ∈ C} ⊆ ({x 0, x 1, z} : Set V) ∪ A := by
  classical
  obtain ⟨ih1, ihu⟩ := ih
  -- ### Bookkeeping in `G`
  have hAA1 : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hzA1 : z ∉ wheelSystemA G z A₀ x 1 := z_notMem_wheelSystemA hframe
  have hzA : z ∉ A := fun h => hzA1 (hAA1 h)
  have hadjz : ∀ j ≤ 2, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hxA : ∀ j, j ≤ 2 → x j ∉ A :=
    fun j hj hm => wheelSystemA_no_z _ (hAA1 hm) (hadjz j hj)
  have hnbzA : ∀ v ∈ A, ¬ G.Adj z v := fun v hv => wheelSystemA_no_z v (hAA1 hv)
  have hAnc : ∀ v ∈ A, ¬ VertexComplete G v ({x 0, x 1} : Set V) := by
    intro v hv hc
    exact wheelSystemA_no_complete v (hAA1 hv) (by rw [wheelSystemX_one]; exact hc)
  have hYx0 : ∀ w ∈ Y, G.Adj (x 0) w := hHyp.2.2.1
  have hYx1 : ∀ w ∈ Y, G.Adj (x 1) w := hHyp.2.2.2.1
  -- ### The induced subgraph
  set S : Set V := A ∪ ({x 0, x 1, x 2, z} ∪ Y₀) with hSdef
  have hAS : A ⊆ S := Set.subset_union_left
  have hzS : z ∈ S := Or.inr (Or.inl (by simp))
  have hxS : ∀ j, j ≤ 2 → x j ∈ S := by
    intro j hj
    interval_cases j
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inl (by simp))
  have hY₀S : Y₀ ⊆ S := fun w hw => Or.inr (Or.inr hw)
  have hadjS : ∀ a b : ↥S, (G.induce S).Adj a b ↔ G.Adj a.1 b.1 := fun _ _ => Iff.rfl
  have hvinj : Function.Injective (Subtype.val : ↥S → V) := Subtype.val_injective
  have hrange : Set.range (Subtype.val : ↥S → V) = S := Subtype.range_coe
  have himgA : (Subtype.val : ↥S → V) '' (Subtype.val ⁻¹' A) = A :=
    Set.image_preimage_eq_of_subset (by rw [hrange]; exact hAS)
  have himgY : (Subtype.val : ↥S → V) '' (Subtype.val ⁻¹' Y₀) = Y₀ :=
    Set.image_preimage_eq_of_subset (by rw [hrange]; exact hY₀S)
  obtain ⟨x', hx'⟩ : ∃ x' : ℕ → ↥S, ∀ j, j ≤ 2 → (x' j).val = x j :=
    ⟨fun i => if h : x i ∈ S then ⟨x i, h⟩ else ⟨z, hzS⟩, by
      intro j hj
      show (if h : x j ∈ S then (⟨x j, h⟩ : ↥S) else ⟨z, hzS⟩).val = x j
      rw [dif_pos (hxS j hj)]⟩
  set z' : ↥S := ⟨z, hzS⟩ with hz'def
  set A' : Set ↥S := Subtype.val ⁻¹' A with hA'def
  set Y' : Set ↥S := Subtype.val ⁻¹' Y₀ with hY'def
  obtain ⟨a₀, ha₀⟩ := goodA_nonempty hA
  -- ### `(z, A)` is a frame of the induced graph
  have hframe' : IsFrame (G.induce S) z' A' := by
    refine ⟨⟨⟨a₀, hAS ha₀⟩, ha₀⟩, ?_, ?_, ?_⟩
    · rw [connectedSet_map hvinj hadjS, himgA]
      exact hA.2.1
    · exact fun h => hzA h
    · exact fun v hv => hnbzA v.1 hv
  -- ### `x₀,x₁,x₂` is a wheel system there
  have hX1 : wheelSystemX x' 1 = ({x' 0, x' 1} : Set ↥S) := wheelSystemX_one x'
  have hncA' : ∀ v : ↥S, v ∈ A' → ¬ VertexComplete (G.induce S) v ({x' 0, x' 1} : Set ↥S) := by
    intro v hv hc
    refine hAnc v.1 hv ?_
    rintro u (rfl | rfl)
    · have := hc (x' 0) (by simp)
      rw [hadjS, hx' 0 (by omega)] at this
      exact this
    · have := hc (x' 1) (by simp)
      rw [hadjS, hx' 1 (by omega)] at this
      exact this
  have hws' : IsWheelSystem (G.induce S) z' A' x' 2 := by
    refine ⟨by omega, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro j hj k hk hjk
      refine hws.2.1 j (by omega) k (by omega) ?_
      rw [← hx' j hj, ← hx' k hk, hjk]
    · intro j hj
      refine ⟨fun hmem => hxA j hj ?_, fun he => (hws.2.2.1 j hj).2 ?_⟩
      · rw [← hx' j hj]; exact hmem
      · rw [← hx' j hj, he]
    · obtain ⟨a, haA, hadj⟩ := hA.2.2.1
      refine ⟨⟨a, hAS haA⟩, haA, ?_⟩
      rw [hadjS, hx' 0 (by omega)]
      exact hadj
    · obtain ⟨a, haA, hadj⟩ := hA.2.2.2.1
      refine ⟨⟨a, hAS haA⟩, haA, ?_⟩
      rw [hadjS, hx' 1 (by omega)]
      exact hadj
    · exact hncA'
    · intro i hi2 hile
      have hi : i = 2 := by omega
      subst hi
      obtain ⟨a, haA, hadj⟩ := hA.2.2.2.2.1
      refine ⟨A', Set.Subset.rfl, ?_, ⟨⟨a, hAS haA⟩, haA, ?_⟩, ?_, ?_⟩
      · rw [connectedSet_map hvinj hadjS, himgA]
        exact hA.2.1
      · rw [hadjS, hx' 2 (by omega)]
        exact hadj
      · exact fun v hv => hnbzA v.1 hv
      · intro v hv
        simpa only [Nat.sub_self, hX1] using hncA' v hv
    · intro i h1i hi2
      interval_cases i
      · intro hc
        have := hc (x' 0) ⟨0, by omega, rfl⟩
        rw [hadjS, hx' 0 (by omega), hx' 1 (by omega)] at this
        exact x0_not_adj_x1 hws this.symm
      · intro hc
        refine hws.2.2.2.2.2.1 2 (by omega) (by omega) ?_
        rw [wheelSystemX_one]
        rintro u (rfl | rfl)
        · have := hc (x' 0) (by rw [hX1]; simp)
          rw [hadjS, hx' 0 (by omega), hx' 2 (by omega)] at this
          exact this
        · have := hc (x' 1) (by rw [hX1]; simp)
          rw [hadjS, hx' 1 (by omega), hx' 2 (by omega)] at this
          exact this
    · intro j hj
      rw [hadjS, hx' j hj]
      exact hadjz j hj
  -- ### `Y₀` satisfies the hypotheses of 19.2 there
  have hHyp' : Hyp192 (G.induce S) z' A' x' Y' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨h1, h2, h3, h4⟩ := hHyp.1 w.1 (hY₀Y hw)
      refine ⟨fun he => h1 ?_, fun he => h2 ?_, fun he => h3 ?_, fun he => h4 ?_⟩
      · exact congrArg Subtype.val he
      · rw [← hx' 0 (by omega)]; exact congrArg Subtype.val he
      · rw [← hx' 1 (by omega)]; exact congrArg Subtype.val he
      · rw [← hx' 2 (by omega)]; exact congrArg Subtype.val he
    · rw [anticonnectedSet_map hvinj hadjS, himgY]
      exact hY0
    · intro w hw
      rw [hadjS, hx' 0 (by omega)]
      exact hYx0 w.1 (hY₀Y hw)
    · intro w hw
      rw [hadjS, hx' 1 (by omega)]
      exact hYx1 w.1 (hY₀Y hw)
    · intro hc
      refine hx2 ?_
      intro w hw
      have := hc ⟨w, hY₀S hw⟩ hw
      rw [hadjS, hx' 2 (by omega)] at this
      exact this
    · intro w hw hnadj
      have hnadj' : ¬ G.Adj w.1 (x 2) := by
        intro hadj
        refine hnadj ?_
        rw [hadjS, hx' 2 (by omega)]
        exact hadj
      obtain ⟨a, haA, hadj⟩ := hA.2.2.2.2.2.1 w.1 (hY₀Y hw) hnadj'
      refine ⟨⟨⟨a, hAS haA⟩, ?_, ?_⟩, ?_⟩
      · exact A0_subset_A1 hframe' hws' haA
      · rw [hadjS]; exact hadj
      · rw [hadjS]
        exact (hHyp.2.2.2.2.2 w.1 (hY₀Y hw) hnadj').2
  -- ### The hub has shrunk
  have hcard : Y'.ncard < Y.ncard := by
    have h1 : Y₀.ncard = Y'.ncard := by
      rw [← himgY]; exact Set.ncard_image_of_injective _ hvinj
    have h2 : Y₀.ncard < Y.ncard := hcard0
    omega
  -- ### The induction hypothesis applies
  obtain ⟨-, C', hC', h0C, h1C, hzC, hCsub⟩ :=
    ihu S z' A' x' Y' (Thm192Claim2Heredity.inF7_induce hG S) hframe' hws' hcard hHyp'
  -- ### In the induced graph, `A₁` is `A`
  have hA1' : wheelSystemA (G.induce S) z' A' x' 1 ⊆ A' := by
    intro v hv
    obtain ⟨B, ⟨hA'B, hBc, hBz, hBX⟩, hvB⟩ := mem_wheelSystemA hv
    rcases (show v.1 ∈ S from v.2) with hvA | hv2
    · exact hvA
    · exfalso
      rcases hv2 with hv3 | hvY
      · -- `v` is one of `x₀,x₁,x₂` (a neighbour of `z`) or `z` itself
        have hvz : v.1 = z ∨ ∃ j, j ≤ 2 ∧ v.1 = x j := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv3
          rcases hv3 with h | h | h | h
          · exact Or.inr ⟨0, by omega, h⟩
          · exact Or.inr ⟨1, by omega, h⟩
          · exact Or.inr ⟨2, by omega, h⟩
          · exact Or.inl h
        rcases hvz with hvz | ⟨j, hj, hvj⟩
        · have hvz' : z' = v := (Subtype.ext hvz).symm
          have hiso : ∀ u ∈ B, ¬ (G.induce S).Adj v u := by
            intro u hu hadj
            exact hBz u hu (by rw [hvz']; exact hadj)
          have heq := eq_of_connected_isolated hBc hvB hiso ⟨a₀, hAS ha₀⟩ (hA'B ha₀)
          have ha₀z : a₀ = z := (congrArg Subtype.val heq).trans hvz
          exact hzA (ha₀z ▸ ha₀)
        · refine hBz v hvB ?_
          rw [hadjS]
          show G.Adj z v.1
          rw [hvj]
          exact hadjz j hj
      · -- `v ∈ Y₀` is `{x₀,x₁}`-complete
        refine hBX v hvB ?_
        rw [hX1]
        rintro u (rfl | rfl)
        · rw [hadjS, hx' 0 (by omega)]
          exact (hYx0 v.1 (hY₀Y hvY)).symm
        · rw [hadjS, hx' 1 (by omega)]
          exact (hYx1 v.1 (hY₀Y hvY)).symm
  -- ### Transport the wheel back to `G`
  refine ⟨C'.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
  · have hw := isWheel_map hvinj hadjS hC'
    rwa [himgY] at hw
  · rw [← hx' 0 (by omega)]; exact List.mem_map_of_mem h0C
  · rw [← hx' 1 (by omega)]; exact List.mem_map_of_mem h1C
  · exact List.mem_map_of_mem hzC
  · intro v hv
    obtain ⟨v', hv'C, rfl⟩ := List.mem_map.mp hv
    rcases hCsub hv'C with h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      refine Or.inl ?_
      rcases h with rfl | rfl | rfl
      · exact Or.inl (hx' 0 (by omega))
      · exact Or.inr (Or.inl (hx' 1 (by omega)))
      · exact Or.inr (Or.inr rfl)
    · exact Or.inr (hA1' h)



/-- **Two distinct vertices of `A` are `Y₀`-complete**, for every anticonnected
`Y₀ ⊆ Y` that is smaller than `Y` and to which `x₂` is not complete.

PAPER (19.2, claim (1), printed p. 118): *"By the minimality of `|Y|`, `z` is
`Y \ {y₂}`-complete and there is a `Y \ {y₂}`-complete vertex in `A`."*  The printed
sentence is used with the hub `Y \ {y₂}`; the statement below is the same step for an
arbitrary smaller hub, and it produces *two* such vertices, exactly as claim (2) does
for the hub `Y \ {y}` (`Thm192Infra.two_complete_in_interior`). -/
theorem two_complete_in_A (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (Y₀ : Set V) (hY₀Y : Y₀ ⊆ Y) (hY0 : AnticonnectedSet G Y₀)
    (hx2 : ¬ VertexComplete G (x 2) Y₀)
    (hcard0 : Y₀.ncard < Y.ncard) :
    ∃ c ∈ A, ∃ d ∈ A, c ≠ d ∧ VertexComplete G c Y₀ ∧ VertexComplete G d Y₀ := by
  classical
  have hx0Y0 : VertexComplete G (x 0) Y₀ := fun w hw => hHyp.2.2.1 w (hY₀Y hw)
  have hx1Y0 : VertexComplete G (x 1) Y₀ := fun w hw => hHyp.2.2.2.1 w (hY₀Y hw)
  -- the hypotheses of 19.2 hold for the smaller hub `Y₀`
  have hHyp0 : Hyp192 G z A₀ x Y₀ :=
    ⟨fun w hw => hHyp.1 w (hY₀Y hw), hY0, hx0Y0, hx1Y0, hx2,
      fun w hw hn => hHyp.2.2.2.2.2 w (hY₀Y hw) hn⟩
  -- so the induction on `|Y|` applies to it
  have hcon0 : Concl192 G z A₀ x Y₀ := ih.1 Y₀ hcard0 hHyp0
  obtain ⟨C, hC, h0C, h1C, hzC, hsub⟩ :=
    inductive_wheel_with_rim_in_A G hG z A₀ hframe x hws Y hHyp ih y A hA Y₀ hY₀Y hY0
      hx2 hcard0
  have hne : x 0 ≠ x 1 := by
    intro he
    have := hws.2.1 0 (by omega) 1 (by omega) he
    omega
  obtain ⟨P, hP, hPint, hedges⟩ :=
    Thm192Claim2RimPath.path_of_local_wheel hG.1.1.1.1 hC hzC h0C h1C hne
      (hws.2.2.2.2.2.2 0 (by omega)) (hws.2.2.2.2.2.2 1 (by omega)) hcon0.1 hx0Y0 hx1Y0
      hsub (fun v hv => wheelSystemA_no_z v (hA.1 hv))
  obtain ⟨c, hcI, d, hdI, hcd, hcY, hdY⟩ :=
    Thm192Infra.two_complete_in_interior hws hA.1 hP hPint hedges
  exact ⟨c, hPint c hcI, d, hPint d hdI, hcd, hcY, hdY⟩

end Workspace.ProofLemmas.Thm192Claim9YAdjX2TwoComplete
