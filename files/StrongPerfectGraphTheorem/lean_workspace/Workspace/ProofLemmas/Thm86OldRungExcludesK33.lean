import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# `H₀ ≠ K₃,₃` when the selected strip has disjoint end-sets

**8.6 endgame** (printed p. 46).  The printed sentence is

> *"If `A₁ ∩ A₂ = ∅` then `H₀ ≠ K₃,₃` and `G` admits a proper 2-join, and the theorem holds."*

The authors leave the first half implicit.  The reason is that a `K₃,₃` appearance is
*degenerate*: `K₃,₃` has all degrees `3`, so it has no degree-`2` vertex, so no edge of `J` is
subdivided in `H₀`, so every rung of `L(H₀)` is a single vertex — whence the two ends
`N_{b₁b₂}`, `N_{b₂b₁}` of the surviving old rung `R₀(b₁,b₂)` coincide and `A₁ ∩ A₂ ≠ ∅`.

`FormsLineGraph` supplies no dictionary between the subdivision witnesses `(ι,T)` and the
rungs `R`, so the argument is run through cardinalities instead, which is enough:

* every vertex of `H₀` is a branch-vertex (degree `3`), so `V(J) = V(H₀)` and every track of
  the subdivision has exactly two vertices — hence `|E(H₀)| ≤ |E(J)|`;
* `V(L(H₀))` is the union of the rungs, one nonempty piece per edge of `J`, and these pieces
  lie in pairwise disjoint strips of `(S₀,N₀)`, so `|E(J)| ≤ |V(L(H₀))|`, *strictly* because
  the piece belonging to `b₁b₂` contains the two distinct ends of `R₀(b₁,b₂)`;
* but `L(H₀)` is isomorphic to `G|V(L(H₀))`, so `|V(L(H₀))| = |E(H₀)|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm86OldRungExcludesK33

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- Every vertex of `K₃,₃` has exactly three neighbours. -/
theorem k33_neighborSet_ncard (x : Fin 3 ⊕ Fin 3) :
    ((completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet x).ncard = 3 := by
  have hr : (Set.range (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3)).ncard = 3 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ]
    simp
  have hl : (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ Fin 3)).ncard = 3 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ]
    simp
  cases x with
  | inl i =>
    have h : (completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet (Sum.inl i)
        = Set.range (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3) := by
      ext y
      cases y <;> simp [SimpleGraph.mem_neighborSet, _root_.completeBipartiteGraph_adj]
    rw [h, hr]
  | inr i =>
    have h : (completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet (Sum.inr i)
        = Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ Fin 3) := by
      ext y
      cases y <;> simp [SimpleGraph.mem_neighborSet, _root_.completeBipartiteGraph_adj]
    rw [h, hl]

/-- **8.6 endgame** (printed p. 46): *"If `A₁ ∩ A₂ = ∅` then `H₀ ≠ K₃,₃` …"*. -/
theorem thm86OldRungExcludesK33
    {V U W : Type*} [Fintype V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V)
    (S₀ : U → U → Set V) (N₀ : U → Set V) (R₀ : U → U → List V)
    (H₀ : SimpleGraph W) (hS₀ : IsJStripSystem G J S₀ N₀)
    (hForms : FormsLineGraph G J S₀ N₀ R₀ H₀)
    (b₁ b₂ : U) (hb₁b₂ : J.Adj b₁ b₂)
    (hOldRung : IsUVRung G J S N b₁ b₂ (R₀ b₁ b₂))
    (hEndsDisjoint : Disjoint (N b₁ ∩ S b₁ b₂) (N b₂ ∩ S b₁ b₂)) :
    ¬ Nonempty (H₀ ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  rintro ⟨φ⟩
  obtain ⟨hrungs₀, hsubdiv, ⟨ψ⟩⟩ := hForms
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsubdiv.1
  -- Every vertex of `H₀` has degree three, so every vertex is a branch-vertex.
  have hdeg : ∀ w : W, 3 ≤ (H₀.neighborSet w).ncard := by
    intro w
    have h1 := Workspace.ProofLemmas.SubdivisionCounting.neighborSet_image_of_iso φ w
    have h2 : ((completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet (φ w)).ncard = 3 :=
      k33_neighborSet_ncard _
    rw [h1, Set.ncard_image_of_injective _ (EquivLike.injective φ)] at h2
    omega
  have hrange : ∀ w : W, w ∈ Set.range ι := fun w =>
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      htrack hrev hdisjint hcover hedges (hdeg w)
  -- Hence no track has an internal vertex: every track has exactly two vertices.
  have htlen : ∀ u v : U, J.Adj u v → (T u v).length = 2 := by
    intro u v huv
    have h1 : 2 ≤ (T u v).length := by
      have := hlen u v huv
      simp only [trackLength] at this
      omega
    by_contra hne
    have h3 : 3 ≤ (T u v).length := by omega
    exact hnew u v huv _
      (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem _ 0 (by omega))
      (hrange _)
  -- So the edges of `H₀` are exactly the images of the edges of `J`.
  have hmapedge : ∀ e ∈ J.edgeSet, Sym2.map ι e ∈ H₀.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : J.Adj u v := he
      have h2 := htlen u v huv
      have hadj : H₀.Adj ((T u v)[0]'(by omega)) ((T u v)[1]'(by omega)) :=
        (htrack u v huv).1.2.2 0 (by omega)
      rw [Workspace.ProofLemmas.SubdivisionCounting.track_head (htrack u v huv) (by omega),
        Workspace.ProofLemmas.SubdivisionCounting.track_last (htrack u v huv) h2] at hadj
      simpa only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet] using hadj
  have hsurjτ : ∀ f ∈ H₀.edgeSet, ∃ e : Sym2 U, ∃ _ : e ∈ J.edgeSet, Sym2.map ι e = f := by
    intro f hf
    rw [hedges] at hf
    simp only [Set.mem_iUnion] at hf
    obtain ⟨u, v, huv, hmem⟩ := hf
    obtain ⟨i, hi, rfl⟩ := hmem
    have h2 := htlen u v huv
    obtain rfl : i = 0 := by omega
    refine ⟨s(u, v), huv, ?_⟩
    rw [Sym2.map_pair_eq,
      Workspace.ProofLemmas.SubdivisionCounting.track_head (htrack u v huv) (by omega),
      Workspace.ProofLemmas.SubdivisionCounting.track_last (htrack u v huv) h2]
  -- The vertex set carrying `L(H₀)`
  set Kset : Set V := ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R₀ u v} with hKset
  have hKmem : ∀ x : V, x ∈ Kset ↔ ∃ u v : U, J.Adj u v ∧ x ∈ R₀ u v := by
    intro x
    rw [hKset]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    tauto
  haveI : Fintype ↥Kset := Fintype.ofFinite _
  haveI : Fintype ↥J.edgeSet := Fintype.ofFinite _
  haveI : Fintype ↥H₀.edgeSet := Fintype.ofFinite _
  -- Each vertex of `Kset` lies on a rung, and its strip is uniquely determined.
  have hex : ∀ z : ↥Kset, ∃ p : U × U, J.Adj p.1 p.2 ∧ (z : V) ∈ R₀ p.1 p.2 := by
    intro z
    obtain ⟨u, v, huv, hmem⟩ := (hKmem (z : V)).mp z.2
    exact ⟨(u, v), huv, hmem⟩
  choose fpair hfadj hfmem using hex
  have hkey : ∀ (z : ↥Kset) (u v : U), J.Adj u v → (z : V) ∈ S₀ u v →
      s((fpair z).1, (fpair z).2) = s(u, v) := by
    intro z u v huv hzS
    exact Workspace.ProofLemmas.StripSystemBasics.edge_eq_of_mem_strips hS₀
      (hfadj z) huv
      (Workspace.ProofLemmas.StripSystemBasics.rung_subset_strip
        (hrungs₀ _ _ (hfadj z)) _ (hfmem z)) hzS
  set σ : ↥Kset → ↥J.edgeSet :=
    fun z => ⟨s((fpair z).1, (fpair z).2),
      (SimpleGraph.mem_edgeSet _).mpr (hfadj z)⟩ with hσ
  have hσsurj : Function.Surjective σ := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : J.Adj u v := he
      obtain ⟨x, hxR, hxS, -, -⟩ :=
        Workspace.ProofLemmas.StripSystemBasics.exists_rung_head (hrungs₀ u v huv)
      have hxK : x ∈ Kset := (hKmem x).mpr ⟨u, v, huv, hxR⟩
      exact ⟨⟨x, hxK⟩, Subtype.ext (hkey ⟨x, hxK⟩ u v huv hxS)⟩
  -- The old rung has two distinct ends, so `σ` is not injective.
  obtain ⟨x₁, hx₁R, hx₁S, hx₁N, -⟩ :=
    Workspace.ProofLemmas.StripSystemBasics.exists_rung_head hOldRung
  obtain ⟨x₂, hx₂R, hx₂S, hx₂N, -⟩ :=
    Workspace.ProofLemmas.StripSystemBasics.exists_rung_last hOldRung
  have hx₁₂ : x₁ ≠ x₂ := by
    rintro rfl
    exact (Set.disjoint_left.mp hEndsDisjoint ⟨hx₁N, hx₁S⟩) ⟨hx₂N, hx₂S⟩
  have hx₁K : x₁ ∈ Kset := (hKmem x₁).mpr ⟨b₁, b₂, hb₁b₂, hx₁R⟩
  have hx₂K : x₂ ∈ Kset := (hKmem x₂).mpr ⟨b₁, b₂, hb₁b₂, hx₂R⟩
  have hx₁S₀ : x₁ ∈ S₀ b₁ b₂ :=
    Workspace.ProofLemmas.StripSystemBasics.rung_subset_strip (hrungs₀ b₁ b₂ hb₁b₂) _ hx₁R
  have hx₂S₀ : x₂ ∈ S₀ b₁ b₂ :=
    Workspace.ProofLemmas.StripSystemBasics.rung_subset_strip (hrungs₀ b₁ b₂ hb₁b₂) _ hx₂R
  have hσval : ∀ z : ↥Kset, (σ z).1 = s((fpair z).1, (fpair z).2) := fun _ => rfl
  have hσnotinj : ¬ Function.Injective σ := by
    intro hinj
    have heq2 : σ ⟨x₁, hx₁K⟩ = σ ⟨x₂, hx₂K⟩ := by
      apply Subtype.ext
      rw [hσval, hσval, hkey ⟨x₁, hx₁K⟩ b₁ b₂ hb₁b₂ hx₁S₀,
        hkey ⟨x₂, hx₂K⟩ b₁ b₂ hb₁b₂ hx₂S₀]
    exact hx₁₂ (congrArg Subtype.val (hinj heq2))
  -- Counting: `|E(H₀)| ≤ |E(J)| < |Kset| = |E(H₀)|`.
  have hlt : Fintype.card ↥J.edgeSet < Fintype.card ↥Kset :=
    Fintype.card_lt_of_surjective_not_injective σ hσsurj hσnotinj
  have hle : Fintype.card ↥H₀.edgeSet ≤ Fintype.card ↥J.edgeSet := by
    refine Fintype.card_le_of_surjective
      (fun e => (⟨Sym2.map ι e.1, hmapedge e.1 e.2⟩ : ↥H₀.edgeSet)) ?_
    rintro ⟨f, hf⟩
    obtain ⟨e, he, hef⟩ := hsurjτ f hf
    exact ⟨⟨e, he⟩, Subtype.ext hef⟩
  have heq : Fintype.card ↥H₀.edgeSet = Fintype.card ↥Kset :=
    Fintype.card_congr ψ.toEquiv
  omega

end Workspace.ProofLemmas.Thm86OldRungExcludesK33
