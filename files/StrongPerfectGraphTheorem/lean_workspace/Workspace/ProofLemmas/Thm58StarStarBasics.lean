import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Thm58BranchBranchBasics
import Workspace.ProofLemmas.Thm82BranchDelta

/-!
# Attachment bookkeeping for claims (3) and (4) of 5.8

Both attachment sets lie in vertex stars.  This file records what the hypotheses of that case
say about the neighbours of the two ends of the outside path, and it identifies the branch
between the two star vertices when they are adjacent in `J`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarBasics

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}

/-- The hypotheses of the star--star case, expressed in `G`. -/
structure Context (G : SimpleGraph V) (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (N : Fin n → Set V)
    (F : Set V) (P : List V) (p₁ p₂ : V) (c₁ c₂ : Fin n) : Prop where
  ready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂
  star₁ : c₁ ∈ branchVertices H
  star₂ : c₂ ∈ branchVertices H
  first : attachments G (F \ {p₂}) K ⊆ N c₁
  last : attachments G (F \ {p₁}) K ⊆ N c₂

variable {c₁ c₂ : Fin n} (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

theorem berge : Berge G := h.ready.1

theorem path : IsPathFrom G P p₁ p₂ := h.ready.2.2.2.2.2.2.1

theorem vertices : {x : V | x ∈ P} = F := h.ready.2.2.2.2.2.2.2.1

theorem two_le_length : 2 ≤ P.length := by
  classical
  have hcard := h.ready.2.2.2.2.2.2.2.2
  have hset : F = (↑P.toFinset : Set V) := by
    rw [← vertices h]
    ext x
    simp
  rw [hset, Set.ncard_coe_finset] at hcard
  exact hcard.trans P.toFinset_card_le

theorem ends_ne : p₁ ≠ p₂ :=
  PathBasics.isPathFrom_ends_ne (path h) (by
    have := two_le_length h
    simp only [pathLength]
    omega)

theorem first_mem : p₁ ∈ F := by
  rw [← vertices h]
  exact PathBasics.head_mem (path h).2.1

theorem last_mem : p₂ ∈ F := by
  rw [← vertices h]
  exact PathBasics.getLast_mem (path h).2.2

theorem mem_path {z : V} (hz : z ∈ F) : z ∈ P := by
  have := vertices h
  rw [Set.ext_iff] at this
  exact (this z).mpr hz

theorem star_eq (d : Fin n) : N d = edgeImage φ (incidentEdges H d) := h.ready.2.2.2.1 d

theorem star_subset (d : Fin n) : N d ⊆ K := by
  rw [star_eq h d]
  exact image_subset

theorem first_adj_mem {x : V} (hx : x ∈ K) (ha : G.Adj p₁ x) : x ∈ N c₁ :=
  h.first ⟨hx, p₁, ⟨first_mem h, ends_ne h⟩, ha.symm⟩

theorem last_adj_mem {x : V} (hx : x ∈ K) (ha : G.Adj p₂ x) : x ∈ N c₂ :=
  h.last ⟨hx, p₂, ⟨last_mem h, (ends_ne h).symm⟩, ha.symm⟩

/-- An internal vertex of the outside path can only attach to both stars at once. -/
theorem mid_adj_mem {z x : V} (hz : z ∈ P) (hz₁ : z ≠ p₁) (hz₂ : z ≠ p₂)
    (hx : x ∈ K) (ha : G.Adj z x) : x ∈ N c₁ ∩ N c₂ := by
  have hzF : z ∈ F := by rw [← vertices h]; exact hz
  exact ⟨h.first ⟨hx, z, ⟨hzF, hz₂⟩, ha.symm⟩, h.last ⟨hx, z, ⟨hzF, hz₁⟩, ha.symm⟩⟩

/-- Nonlocality forces a neighbour of the first end outside the second star. -/
theorem first_outside : ∃ x ∈ N c₁ \ N c₂, G.Adj p₁ x := by
  classical
  by_contra hn
  apply h.ready.2.2.2.2.2.1
  refine Or.inl ⟨c₂, h.star₂, ?_⟩
  rintro e ⟨he, hxK, z, hzF, hxz⟩
  apply (image_mem_iff (φ := φ) he).mp
  rw [← star_eq h c₂]
  by_cases hz : z = p₁
  · have ha : G.Adj p₁ (φ ⟨e, he⟩ : V) := hz ▸ hxz.symm
    by_contra hout
    exact hn ⟨_, ⟨first_adj_mem h hxK ha, hout⟩, ha⟩
  · exact h.last ⟨hxK, z, ⟨hzF, hz⟩, hxz⟩

/-- Nonlocality forces a neighbour of the last end outside the first star. -/
theorem last_outside : ∃ x ∈ N c₂ \ N c₁, G.Adj p₂ x := by
  classical
  by_contra hn
  apply h.ready.2.2.2.2.2.1
  refine Or.inl ⟨c₁, h.star₁, ?_⟩
  rintro e ⟨he, hxK, z, hzF, hxz⟩
  apply (image_mem_iff (φ := φ) he).mp
  rw [← star_eq h c₁]
  by_cases hz : z = p₂
  · have ha : G.Adj p₂ (φ ⟨e, he⟩ : V) := hz ▸ hxz.symm
    by_contra hout
    exact hn ⟨_, ⟨last_adj_mem h hxK ha, hout⟩, ha⟩
  · exact h.first ⟨hxK, z, ⟨hzF, hz⟩, hxz⟩

/-- The two stars are different: each end sees a vertex the other star misses. -/
theorem stars_ne : c₁ ≠ c₂ := by
  rintro rfl
  obtain ⟨x, hx, -⟩ := first_outside h
  exact hx.2 hx.1

/-- A vertex in both stars is the vertex of `L(H)` given by the edge `c₁c₂` of `H`. -/
theorem adj_of_star_inter {x : V} (hx : x ∈ N c₁ ∩ N c₂) :
    ∃ he : s(c₁, c₂) ∈ H.edgeSet, x = (φ ⟨s(c₁, c₂), he⟩ : V) := by
  rw [star_eq h c₁] at hx
  obtain ⟨⟨e, he, hec₁, rfl⟩, hx₂⟩ := hx
  rw [star_eq h c₂] at hx₂
  obtain ⟨f, hf, hfc₂, hef⟩ := hx₂
  have : e = f := congrArg Subtype.val (φ.injective (Subtype.ext hef))
  subst this
  have hE : e = s(c₁, c₂) :=
    (Sym2.mem_and_mem_iff (stars_ne h)).mp ⟨hec₁.2, hfc₂.2⟩
  subst hE
  exact ⟨he, rfl⟩

/-- If the two stars meet, then `c₁c₂` is an edge of `H`. -/
theorem star_inter_adj {x : V} (hx : x ∈ N c₁ ∩ N c₂) : H.Adj c₁ c₂ := by
  obtain ⟨he, -⟩ := adj_of_star_inter h hx
  exact (SimpleGraph.mem_edgeSet _).mp he

/-- The one-edge track between two adjacent branch-vertices is a branch. -/
theorem isBranch_pair (hadj : H.Adj c₁ c₂) : IsBranch H [c₁, c₂] := by
  have htrack : IsTrackFrom H [c₁, c₂] c₁ c₂ := by
    refine ⟨⟨by simp, by simp [stars_ne h], ?_⟩, rfl, rfl⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst i
    simpa using hadj
  refine Thm82BranchDelta.isBranch_of_ends_branch htrack (stars_ne h) ?_ h.star₁ h.star₂
  intro w hw
  simp [trackInterior] at hw

end Workspace.ProofLemmas.Thm58StarStarBasics
