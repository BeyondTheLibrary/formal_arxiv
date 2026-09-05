import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm82RungFamily

/-!
# Choosing rungs, and the non-local pair — the shared helpers of the proof of 8.5

Proof bodies lifted verbatim from `ProofAttempts/Thm85Claim2/Attempt_1.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm85RungChoice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-! ## Private helper (not part of the frozen interface) -/

/-- A set of size ≥ 3 has a member outside any prescribed pair. -/
private theorem exists_mem_ne_pair {α : Type*} {s : Set α} (hs : 3 ≤ s.ncard) (y z : α) :
    ∃ x ∈ s, x ≠ y ∧ x ≠ z := by
  by_contra h
  push_neg at h
  have hsub : s ⊆ ({y, z} : Set α) := by
    intro x hx
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr (h x hx hxy)
  have h1 : s.ncard ≤ ({y, z} : Set α).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({y, z} : Set α).ncard ≤ 2 := by
    have := Set.ncard_insert_le y ({z} : Set α)
    simpa using this
  omega

section

variable {V U : Type*} [Fintype U] {G : SimpleGraph V} {J : SimpleGraph U}
  {S : U → U → Set V} {N : U → Set V}

/-- **From the two ends of an edge of a 3-connected graph one can pick two disjoint edges.**

This is the combinatorial core of the exclusion of outcomes 5.8.2.b, 5.8.2.c, 5.8.2.d in the
printed proof of claim (3): in each of them the ends `p₁, p₂` of the path are complete to
`N_{b₁} \ {r₁}` and `N_{b₂} \ {r₂}`, so the strips of the edges `b₁w` and `b₂w'` both meet the
attachment set. -/
theorem exists_disjoint_edges_at_ends (hJ : IsKConnected J 3) {a b : U} (hab : J.Adj a b) :
    ∃ w w' : U, J.Adj a w ∧ J.Adj b w' ∧ [a, w, b, w'].Nodup := by
  have hdb : 3 ≤ (J.neighborSet b).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ b
  have hda : 3 ≤ (J.neighborSet a).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  obtain ⟨w', hw', hw'a, -⟩ := exists_mem_ne_pair hdb a a
  obtain ⟨w, hw, hwb, hww'⟩ := exists_mem_ne_pair hda b w'
  refine ⟨w, w', hw, hw', ?_⟩
  have hab' : a ≠ b := hab.ne
  have haw : a ≠ w := (SimpleGraph.mem_neighborSet .. |>.mp hw).ne
  have haw' : a ≠ w' := fun h => hw'a h.symm
  have hbw' : b ≠ w' := (SimpleGraph.mem_neighborSet .. |>.mp hw').ne
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, and_true, not_or]
  tauto

/-- **A per-ordered-pair choice of rungs can be made edge-indexed.**

Given any family `C` with `C a b` a `ab`-rung for every ordered adjacent pair, there is a family
`R` which is a choice of rungs in the paper's sense — indexed by the *edges* of `J`, so that
reversing the orientation reverses the list — and each `R a b` is one of `C a b`, `(C b a)ᴿ`.
This is what turns "for each edge `uv` of `J` choose a `uv`-rung with such-and-such a property"
into the hypotheses of `Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph`.

This is the **generic** version of the already-proved
`Thm82RungFamily.exists_symmetric_rung_family`, which only pins the choice down on one
prescribed edge. -/
theorem exists_symmetric_rung_family_of_choice (hSN : IsJStripSystem G J S N)
    (C : U → U → List V) (hC : ∀ a b : U, J.Adj a b → IsUVRung G J S N a b (C a b)) :
    ∃ R : U → U → List V,
      (∀ a b : U, J.Adj a b → IsUVRung G J S N a b (R a b)) ∧
      (∀ a b : U, J.Adj a b → R b a = (R a b).reverse) ∧
      (∀ a b : U, J.Adj a b → R a b = C a b ∨ R a b = (C b a).reverse) := by
  classical
  set f : U → Fin (Fintype.card U) := fun a => (Fintype.equivFin U) a with hf
  have hfinj : Function.Injective f := (Fintype.equivFin U).injective
  refine ⟨fun a b => if f a ≤ f b then C a b else (C b a).reverse, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases h : f a ≤ f b
    · simpa [h] using hC a b hab
    · simp only [h, if_false]
      exact Thm82RungFamily.rung_reverse hSN (hC b a hab.symm)
  · intro a b hab
    have hne : f a ≠ f b := fun h => hab.ne (hfinj h)
    by_cases h : f a ≤ f b
    · have h' : ¬ f b ≤ f a := by
        intro hc; exact hne (le_antisymm h hc)
      simp [h, h']
    · have h' : f b ≤ f a := le_of_not_ge h
      simp [h, h']
  · intro a b _
    by_cases h : f a ≤ f b
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])

/-- **"Make a choice of rungs `R_uv` (`uv ∈ E(J)`) such that `X ∩ V(R_uv) ≠ ∅` for each
`uv ∈ K`"** (proof of 8.5, claims (2) and (3), printed p. 42).

This is **strictly stronger** than the still-`sorry` `TwoPrescribedSymmetricRungFamily`: it
prescribes a meeting point on *every* edge whose strip meets `D`, not merely on two prescribed
edges. -/
theorem exists_rung_family_meeting (hSN : IsJStripSystem G J S N) (D : Set V) :
    ∃ R : U → U → List V,
      (∀ a b : U, J.Adj a b → IsUVRung G J S N a b (R a b)) ∧
      (∀ a b : U, J.Adj a b → R b a = (R a b).reverse) ∧
      (∀ a b : U, J.Adj a b → (D ∩ S a b).Nonempty → ∃ z ∈ D, z ∈ R a b) := by
  classical
  have hCex : ∀ a b : U, ∃ L : List V, (J.Adj a b → IsUVRung G J S N a b L) ∧
      (J.Adj a b → (D ∩ S a b).Nonempty → ∃ z ∈ D, z ∈ L) := by
    intro a b
    by_cases hab : J.Adj a b
    · by_cases hD : (D ∩ S a b).Nonempty
      · obtain ⟨z, hzD, hzS⟩ := hD
        obtain ⟨L, hL, hzL⟩ := StripSystemBasics.exists_rung hSN hab hzS
        exact ⟨L, fun _ => hL, fun _ _ => ⟨z, hzD, hzL⟩⟩
      · obtain ⟨L, hL⟩ := StripSystemBasics.exists_uvRung hSN hab
        exact ⟨L, fun _ => hL, fun _ h => absurd h hD⟩
    · exact ⟨[], fun h => absurd h hab, fun h => absurd h hab⟩
  choose C hC1 hC2 using hCex
  obtain ⟨R, hR1, hR2, hR3⟩ :=
    exists_symmetric_rung_family_of_choice hSN C (fun a b hab => hC1 a b hab)
  refine ⟨R, hR1, hR2, ?_⟩
  intro a b hab hD
  rcases hR3 a b hab with h | h
  · rw [h]; exact hC2 a b hab hD
  · rw [h]
    have hD' : (D ∩ S b a).Nonempty := by
      rwa [StripSystemBasics.strip_symm hSN hab.symm]
    obtain ⟨z, hzD, hzL⟩ := hC2 b a hab.symm hD'
    exact ⟨z, hzD, by simpa using hzL⟩

/-- **The step "`X` is not local, so there are `x ∈ X ∩ S_uv \ N_v` and `x' ∈ X ∩ S_{u'v}` with
`u' ≠ u`, and `{x, x'}` is not local"** (proof of 8.5, claim (2), printed p. 42). -/
theorem exists_nonlocal_pair (hSN : IsJStripSystem G J S N)
    (X : Set V) (hXnotlocal : ¬ LocalForStripSystem J S N X)
    (v : U) (hXv : X ⊆ ⋃ (u : U) (_ : J.Adj u v), S u v) :
    ∃ (u u' : U) (x x' : V), J.Adj u v ∧ J.Adj u' v ∧ u ≠ u' ∧
      x ∈ X ∧ x ∈ S u v ∧ x ∉ N v ∧
      x' ∈ X ∧ x' ∈ S u' v ∧ x' ∉ S u v ∧
      ¬ LocalForStripSystem J S N ({x, x'} : Set V) := by
  classical
  -- `X ⊄ N_v`, since `X` is not local.
  have hXNv : ¬ X ⊆ N v := fun h => hXnotlocal (Or.inl ⟨v, h⟩)
  obtain ⟨x, hxX, hxNv⟩ := Set.not_subset.mp hXNv
  obtain ⟨u, huv, hxS⟩ : ∃ u : U, J.Adj u v ∧ x ∈ S u v := by
    have := hXv hxX
    simp only [Set.mem_iUnion] at this
    obtain ⟨u, huv, hx⟩ := this
    exact ⟨u, huv, hx⟩
  -- `X ⊄ S_uv`, since `X` is not local.
  have hXS : ¬ X ⊆ S u v := fun h => hXnotlocal (Or.inr ⟨u, v, huv, h⟩)
  obtain ⟨x', hx'X, hx'S⟩ := Set.not_subset.mp hXS
  obtain ⟨u', hu'v, hx'S'⟩ : ∃ u' : U, J.Adj u' v ∧ x' ∈ S u' v := by
    have := hXv hx'X
    simp only [Set.mem_iUnion] at this
    obtain ⟨u', hu'v, hx'⟩ := this
    exact ⟨u', hu'v, hx'⟩
  have huu' : u ≠ u' := by
    intro h; exact hx'S (h ▸ hx'S')
  refine ⟨u, u', x, x', huv, hu'v, huu', hxX, hxS, hxNv, hx'X, hx'S', hx'S, ?_⟩
  rintro (⟨w, hw⟩ | ⟨a, b, hab, hsub⟩)
  · -- `x ∈ N_w` forces `w = u` (it cannot be `v`), while `x' ∈ N_w` forces `w ∈ {v, u'}`.
    have hxw : x ∈ N w := hw (by simp)
    have hx'w : x' ∈ N w := hw (by simp)
    have hwu : w = u := by
      by_contra hc
      have hwv : w ≠ v := by rintro rfl; exact hxNv hxw
      have h0 : x ∈ S u v ∩ N w := ⟨hxS, hxw⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN huv hc hwv] at h0
      exact h0
    subst hwu
    have hwu'v : w = u' ∨ w = v := by
      by_contra hc
      push_neg at hc
      have h0 : x' ∈ S u' v ∩ N w := ⟨hx'S', hx'w⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN hu'v hc.1 hc.2] at h0
      exact h0
    rcases hwu'v with h | h
    · exact huu' h
    · exact huv.ne h
  · -- both would lie in one strip, but they lie in the distinct strips `S_uv`, `S_{u'v}`.
    have h1 : s(a, b) = s(u, v) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hab huv (hsub (by simp)) hxS
    have h2 : s(a, b) = s(u', v) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hab hu'v (hsub (by simp)) hx'S'
    have h3 : s(u, v) = s(u', v) := h1.symm.trans h2
    rcases Sym2.eq_iff.mp h3 with ⟨h4, -⟩ | ⟨h4, h5⟩
    · exact huu' h4
    · exact huv.ne h4

/-- **"`d` meets all edges of `J` in `K`, contrary to (2)"** (proof of 8.5, claim (3), printed
p. 42): if every edge of `J` whose strip meets `X` has `w₀` as an end, then `X` is contained in
the union of the strips at `w₀`. -/
theorem subset_iUnion_of_common_end (hSN : IsJStripSystem G J S N)
    (X : Set V) (hXV : X ⊆ stripSystemVertices J S) (w₀ : U)
    (hK : ∀ u v : U, J.Adj u v → (X ∩ S u v).Nonempty → w₀ = u ∨ w₀ = v) :
    X ⊆ ⋃ (u : U) (_ : J.Adj u w₀), S u w₀ := by
  intro x hx
  obtain ⟨u, v, huv, hxS⟩ : ∃ u v : U, J.Adj u v ∧ x ∈ S u v := by
    have := hXV hx
    simp only [stripSystemVertices, Set.mem_iUnion] at this
    obtain ⟨u, v, huv, hxS⟩ := this
    exact ⟨u, v, huv, hxS⟩
  have hne : (X ∩ S u v).Nonempty := ⟨x, hx, hxS⟩
  simp only [Set.mem_iUnion]
  rcases hK u v huv hne with rfl | rfl
  · exact ⟨v, huv.symm, (StripSystemBasics.strip_symm hSN huv) ▸ hxS⟩
  · exact ⟨u, huv, hxS⟩

end

end Workspace.ProofLemmas.Thm85RungChoice
