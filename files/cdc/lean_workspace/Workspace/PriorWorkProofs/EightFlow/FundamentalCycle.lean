import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.PriorWorkProofs.EightFlow.EvenSubgraph

/-!
# Fundamental cycles and the spanning-tree even cover (Dvořák Lemma 12)

The classical fundamental-cycle argument, carried out over `𝔽₂ = ZMod 2` through the boundary
`(degreeWithin G S v : ZMod 2)`: for a connected spanning edge set `T` of a finite multigraph `G`,
`spanning_tree_even_cover_core` produces an even subgraph `H` containing every non-tree edge
`E(G) \ T`. It inducts on the non-tree edges, each contributing its fundamental cycle `P ∆ {e}`.
-/

open Set
open scoped Graph symmDiff
open Workspace.Types.Orientation

namespace Workspace.PriorWorkProofs.EightFlow

open scoped Classical

variable {α β : Type*} {G : Graph α β} {x y v : α} {e : β}

/-! ## `𝔽₂` `ite` identities -/

private lemma zmod2_ite_or_and {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P ∨ Q then (1 : ZMod 2) else 0) + (if P ∧ Q then 1 else 0)
      = (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

private lemma zmod2_ite_symmDiff {P Q : Prop} [Decidable P] [Decidable Q] :
    (if (P ∧ ¬ Q) ∨ (Q ∧ ¬ P) then (1 : ZMod 2) else 0)
      = (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ] <;> decide

/-! ## A tiny cardinality helper -/

lemma ncard_inter_singleton (A : Set β) (e : β) :
    (A ∩ {e}).ncard = if e ∈ A then 1 else 0 := by
  by_cases h : e ∈ A
  · rw [if_pos h, Set.inter_eq_right.mpr (by simpa using h), Set.ncard_singleton]
  · rw [if_neg h, Set.inter_singleton_eq_empty.mpr h, Set.ncard_empty]

/-! ## The `ZMod 2` boundary and its `𝔽₂`-linearity -/

/-- Boundary of a single edge, as a natural number: `[Inc e v] + [IsLoopAt e v]`. -/
lemma degreeWithin_singleton (v : α) (e : β) :
    degreeWithin G {e} v
      = (if G.Inc e v then 1 else 0) + (if G.IsLoopAt e v then 1 else 0) := by
  unfold degreeWithin
  rw [ncard_inter_singleton, ncard_inter_singleton]
  simp only [Graph.mem_incidenceSet, Graph.mem_loopSet]

/-- The `𝔽₂`-boundary of a single edge `e` with ends `x, y` is `χ_x + χ_y`. -/
lemma bdry_singleton (he : G.IsLink e x y) (v : α) :
    (↑(degreeWithin G {e} v) : ZMod 2)
      = (if v = x then (1 : ZMod 2) else 0) + (if v = y then 1 else 0) := by
  have hInc : G.Inc e v ↔ (v = x ∨ v = y) :=
    ⟨fun h => h.eq_or_eq_of_isLink he,
      fun h => h.elim (fun hh => hh ▸ he.inc_left) (fun hh => hh ▸ he.inc_right)⟩
  have hLoop : G.IsLoopAt e v ↔ (v = x ∧ v = y) := by
    refine ⟨fun h => ?_, fun ⟨hx, hy⟩ => ?_⟩
    · rcases he.eq_and_eq_or_eq_and_eq (show G.IsLink e v v from h) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact ⟨h1.symm, h2.symm⟩
    · subst hx; subst hy; exact he
  rw [degreeWithin_singleton, Nat.cast_add]
  simp only [hInc, hLoop, apply_ite (Nat.cast : ℕ → ZMod 2), Nat.cast_one, Nat.cast_zero]
  exact zmod2_ite_or_and

/-- `𝔽₂`-linearity of the boundary over symmetric difference. -/
lemma bdry_symmDiff (hE : E(G).Finite) (A B : Set β) (v : α) :
    (↑(degreeWithin G (A ∆ B) v) : ZMod 2)
      = ↑(degreeWithin G A v) + ↑(degreeWithin G B v) := by
  have hI : (G.incidenceSet v).Finite := hE.subset (G.incidenceSet_subset_edgeSet v)
  have hind : ∀ e : β, indicator (A ∆ B) e = indicator A e + indicator B e := by
    intro e
    simp only [indicator_apply, Set.mem_symmDiff]
    exact zmod2_ite_symmDiff
  rw [← indicator_endSum_eq hE, ← indicator_endSum_eq hE, ← indicator_endSum_eq hE,
    ← finsum_mem_add_distrib hI]
  refine finsum_mem_congr rfl (fun e _ => ?_)
  rw [hind e, smul_add]

/-- `H` is an even subgraph iff its `𝔽₂`-boundary vanishes on every vertex of `G`. -/
lemma isEvenSubgraph_iff_bdry (H : Set β) :
    IsEvenSubgraph G H ↔ ∀ v ∈ V(G), (↑(degreeWithin G H v) : ZMod 2) = 0 := by
  unfold IsEvenSubgraph
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [ZMod.natCast_eq_zero_iff, ← even_iff_two_dvd]

/-- Symmetric difference of two even subgraphs is even. -/
lemma IsEvenSubgraph.symmDiff (hE : E(G).Finite) {A B : Set β}
    (hA : IsEvenSubgraph G A) (hB : IsEvenSubgraph G B) :
    IsEvenSubgraph G (A ∆ B) := by
  rw [isEvenSubgraph_iff_bdry] at hA hB ⊢
  intro v hv
  rw [bdry_symmDiff hE, hA v hv, hB v hv, add_zero]

/-! ## The `T`-path between reachable vertices (fundamental path) -/

/-- **The `T`-path.** If `x` reaches `y` inside `G.restrict T`, there is an edge set `P ⊆ T`
whose `𝔽₂`-boundary is `χ_x + χ_y`. Built by induction on the walk: each step across a tree
edge `f` (ends `b, c`) toggles `P` by `{f}`, and `bdry` telescopes over `𝔽₂`. -/
lemma exists_path_of_reachable (hE : E(G).Finite) {T : Set β} {x y : α}
    (hR : (G.restrict T).Reachable x y) :
    ∃ P : Set β, P ⊆ T ∧ ∀ v : α,
      (↑(degreeWithin G P v) : ZMod 2)
        = (if v = x then (1 : ZMod 2) else 0) + (if v = y then 1 else 0) := by
  rw [Graph.reachable_def] at hR
  induction hR with
  | refl =>
    refine ⟨∅, Set.empty_subset _, fun v => ?_⟩
    have h0 : degreeWithin G (∅ : Set β) v = 0 := by simp [degreeWithin]
    rw [h0, Nat.cast_zero]
    generalize (if v = x then (1 : ZMod 2) else 0) = t
    revert t; decide
  | @tail b c hab hbc ih =>
    obtain ⟨P, hPT, hPb⟩ := ih
    obtain ⟨f, hf⟩ := hbc
    rw [Graph.restrict_isLink] at hf
    obtain ⟨hfT, hflink⟩ := hf
    refine ⟨P ∆ {f}, ?_, fun v => ?_⟩
    · have h : P ∆ {f} ⊆ P ∪ {f} := symmDiff_le_sup
      exact h.trans (Set.union_subset hPT (Set.singleton_subset_iff.mpr hfT))
    · rw [bdry_symmDiff hE, hPb v, bdry_singleton hflink v]
      generalize (if v = x then (1 : ZMod 2) else 0) = a
      generalize (if v = b then (1 : ZMod 2) else 0) = bb
      generalize (if v = c then (1 : ZMod 2) else 0) = cc
      revert a bb cc; decide

/-! ## The spanning-tree even cover -/

/-- **Spanning-tree even cover (core).** If `T ⊆ E(G)` is spanning-connected (`G.restrict T`
connected), then `G` has an even subgraph `H ⊇ E(G) \ T`. No acyclicity is required. -/
theorem spanning_tree_even_cover_core (hE : E(G).Finite) {T : Set β}
    (hTsub : T ⊆ E(G)) (hconn : (G.restrict T).Connected) :
    ∃ H : Set β, IsEvenSubgraph G H ∧ (E(G) \ T) ⊆ H := by
  suffices h : ∀ D : Set β, D.Finite → D ⊆ E(G) \ T →
      ∃ H : Set β, IsEvenSubgraph G H ∧ D ⊆ H ∧ H ⊆ T ∪ D by
    obtain ⟨H, hev, hsub, -⟩ := h (E(G) \ T) (hE.diff) subset_rfl
    exact ⟨H, hev, hsub⟩
  intro D hDfin
  induction D, hDfin using Set.Finite.induction_on with
  | empty =>
    intro _
    refine ⟨∅, ?_, Set.empty_subset _, by simp⟩
    rw [isEvenSubgraph_iff_bdry]; intro v _; simp [degreeWithin]
  | @insert a s ha hs ih =>
    intro hDsub
    have hsD : s ⊆ E(G) \ T := (Set.subset_insert a s).trans hDsub
    have haD : a ∈ E(G) \ T := hDsub (Set.mem_insert a s)
    obtain ⟨Hs, hHsEven, hsHs, hHsT⟩ := ih hsD
    obtain ⟨x, y, hlink⟩ := (G.edge_mem_iff_exists_isLink a).mp haD.1
    obtain ⟨P, hPT, hPbdry⟩ := exists_path_of_reachable hE
      (hconn.reachable (by simpa using hlink.left_mem) (by simpa using hlink.right_mem))
    have haP : a ∉ P := fun h => haD.2 (hPT h)
    have hKeven : IsEvenSubgraph G (P ∆ {a}) := by
      rw [isEvenSubgraph_iff_bdry]; intro v _
      rw [bdry_symmDiff hE, hPbdry v, bdry_singleton hlink v]
      generalize (if v = x then (1 : ZMod 2) else 0) = p
      generalize (if v = y then (1 : ZMod 2) else 0) = q
      revert p q; decide
    refine ⟨Hs ∆ (P ∆ {a}), hHsEven.symmDiff hE hKeven, ?_, ?_⟩
    · intro g hg
      rcases Set.mem_insert_iff.mp hg with rfl | hgs
      · have haK : g ∈ P ∆ {g} :=
          Set.mem_symmDiff.mpr (Or.inr ⟨Set.mem_singleton g, haP⟩)
        have haHs : g ∉ Hs := fun h =>
          (hHsT h).elim (fun hT => haD.2 hT) (fun hs' => ha hs')
        exact Set.mem_symmDiff.mpr (Or.inr ⟨haK, haHs⟩)
      · have hgHs : g ∈ Hs := hsHs hgs
        have hgnT : g ∉ T := (hsD hgs).2
        have hgK : g ∉ P ∆ {a} := by
          rw [Set.mem_symmDiff]
          rintro (⟨hgP, _⟩ | ⟨hgf, _⟩)
          · exact hgnT (hPT hgP)
          · exact ha (by rwa [Set.mem_singleton_iff.mp hgf] at hgs)
        exact Set.mem_symmDiff.mpr (Or.inl ⟨hgHs, hgK⟩)
    · intro g hg
      have hgU : g ∈ Hs ∪ (P ∆ {a}) := (symmDiff_le_sup (a := Hs) (b := (P ∆ {a}))) hg
      rcases hgU with hgHs | hgK
      · rcases hHsT hgHs with hT | hgs
        · exact Set.mem_union_left _ hT
        · exact Set.mem_union_right _ (Set.mem_insert_of_mem a hgs)
      · have hgU2 : g ∈ P ∪ {a} := (symmDiff_le_sup (a := P) (b := ({a} : Set β))) hgK
        rcases hgU2 with hgP | hgf
        · exact Set.mem_union_left _ (hPT hgP)
        · rw [Set.mem_singleton_iff.mp hgf]; exact Set.mem_union_right _ (Set.mem_insert a s)

end Workspace.PriorWorkProofs.EightFlow
