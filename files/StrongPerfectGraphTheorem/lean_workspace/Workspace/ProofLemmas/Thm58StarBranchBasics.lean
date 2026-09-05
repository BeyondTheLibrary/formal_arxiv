import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm58Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.Thm84RungEndDictionary

/-! Attachment bookkeeping for claims (2) and (6) of 5.8. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58StarBranchBasics

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}

/-- Edges of `H`, read as vertices of the given appearance. -/
def edgeImage (φ : H.lineGraph ≃g G.induce K) (S : Set (Sym2 (Fin n))) : Set V :=
  {x | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
    e ∈ S ∧ x = (φ ⟨e, he⟩ : V)}

theorem image_mem_iff {S : Set (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (he : e ∈ H.edgeSet) : (φ ⟨e, he⟩ : V) ∈ edgeImage φ S ↔ e ∈ S := by
  constructor
  · rintro ⟨f, hf, hfS, heq⟩
    have hef : e = f := congrArg Subtype.val (φ.injective (Subtype.ext heq))
    exact hef ▸ hfS
  · exact fun h => ⟨e, he, h, rfl⟩

theorem image_subset {S : Set (Sym2 (Fin n))} : edgeImage φ S ⊆ K := by
  rintro x ⟨e, he, _, rfl⟩
  exact (φ ⟨e, he⟩).2

theorem exists_edge {x : V} (hx : x ∈ K) :
    ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), x = (φ ⟨e, he⟩ : V) := by
  refine ⟨(φ.symm ⟨x, hx⟩).1, (φ.symm ⟨x, hx⟩).2, ?_⟩
  exact (congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)).symm

theorem attachments_subset_image {A : Set V} {S : Set (Sym2 (Fin n))}
    (h : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      (φ ⟨e, he⟩ : V) ∈ attachments G A K} ⊆ S) :
    attachments G A K ⊆ edgeImage φ S := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := exists_edge (φ := φ) hx.1
  exact ⟨e, he, h ⟨he, hx⟩, rfl⟩

/-- The hypotheses of the star--branch case, now expressed in `G`. -/
structure Context (G : SimpleGraph V) (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (N : Fin n → Set V)
    (F : Set V) (P : List V) (p₁ p₂ : V) (c : Fin n) (q : List (Fin n)) : Prop where
  ready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂
  star : c ∈ branchVertices H
  branch : IsBranch H q
  first : attachments G (F \ {p₂}) K ⊆ N c
  last : attachments G (F \ {p₁}) K ⊆ edgeImage φ (trackEdges q)

variable {c : Fin n} {q : List (Fin n)}
  (h : Context G m J n H K φ N F P p₁ p₂ c q)

include h

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

theorem star_eq (d : Fin n) : N d = edgeImage φ (incidentEdges H d) :=
  h.ready.2.2.2.1 d

theorem star_subset (d : Fin n) : N d ⊆ K := by
  rw [star_eq h d]
  exact image_subset

theorem first_adj_mem {x : V} (hx : x ∈ K) (ha : G.Adj p₁ x) : x ∈ N c :=
  h.first ⟨hx, p₁, ⟨first_mem h, ends_ne h⟩, ha.symm⟩

theorem last_adj_mem {x : V} (hx : x ∈ K) (ha : G.Adj p₂ x) :
    x ∈ edgeImage φ (trackEdges q) :=
  h.last ⟨hx, p₂, ⟨last_mem h, (ends_ne h).symm⟩, ha.symm⟩

/-- Nonlocality forces a neighbor of the first end outside the branch. -/
theorem first_outside_branch : ∃ x ∈ N c \ edgeImage φ (trackEdges q), G.Adj p₁ x := by
  classical
  by_contra hn
  apply h.ready.2.2.2.2.2.1
  refine Or.inr ⟨q, h.branch, ?_⟩
  rintro e ⟨he, hxK, z, hzF, hxz⟩
  apply (image_mem_iff (φ := φ) he).mp
  by_cases hz : z = p₁
  · have ha : G.Adj p₁ (φ ⟨e, he⟩ : V) := hz ▸ hxz.symm
    by_contra hout
    exact hn ⟨_, ⟨first_adj_mem h hxK ha, hout⟩, ha⟩
  · exact h.last ⟨hxK, z, ⟨hzF, hz⟩, hxz⟩

/-- Nonlocality also forces a neighbor of the last end outside the star. -/
theorem last_outside_star : ∃ x ∈ edgeImage φ (trackEdges q) \ N c, G.Adj p₂ x := by
  classical
  by_contra hn
  apply h.ready.2.2.2.2.2.1
  refine Or.inl ⟨c, h.star, ?_⟩
  rintro e ⟨he, hxK, z, hzF, hxz⟩
  apply (image_mem_iff (φ := φ) he).mp
  rw [← star_eq h c]
  by_cases hz : z = p₂
  · have ha : G.Adj p₂ (φ ⟨e, he⟩ : V) := hz ▸ hxz.symm
    by_contra hout
    exact hn ⟨_, ⟨last_adj_mem h hxK ha, hout⟩, ha⟩
  · exact h.first ⟨hxK, z, ⟨hzF, hz⟩, hxz⟩

theorem branch_two_le_length : 2 ≤ q.length := by
  obtain ⟨x, ⟨⟨e, he, ⟨i, hi, _⟩, _⟩, _⟩, _⟩ := last_outside_star h
  omega

/-- Away from an overlap vertex, only the two ends can attach to the appearance. -/
theorem edges_except_overlap {r : V}
    (hoverlap : N c ∩ edgeImage φ (trackEdges q) ⊆ {r}) :
    ∀ x ∈ P, ∀ y ∈ K, y ≠ r → G.Adj x y →
      (x = p₁ ∧ y ∈ N c \ {r}) ∨
      (x = p₂ ∧ y ∈ edgeImage φ (trackEdges q) \ {r}) := by
  intro x hx y hy hyr ha
  have hxF : x ∈ F := by rw [← vertices h]; exact hx
  by_cases hx1 : x = p₁
  · exact Or.inl ⟨hx1, first_adj_mem h hy (hx1 ▸ ha), hyr⟩
  by_cases hx2 : x = p₂
  · exact Or.inr ⟨hx2, last_adj_mem h hy (hx2 ▸ ha), hyr⟩
  exact (hyr (hoverlap ⟨h.first ⟨hy, x, ⟨hxF, hx2⟩, ha.symm⟩,
    h.last ⟨hy, x, ⟨hxF, hx1⟩, ha.symm⟩⟩)).elim

theorem edges_of_disjoint
    (hdisj : Disjoint (N c) (edgeImage φ (trackEdges q))) :
    ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ y ∈ N c) ∨ (x = p₂ ∧ y ∈ edgeImage φ (trackEdges q)) := by
  intro x hx y hy ha
  have hxF : x ∈ F := by rw [← vertices h]; exact hx
  by_cases hx1 : x = p₁
  · exact Or.inl ⟨hx1, first_adj_mem h hy (hx1 ▸ ha)⟩
  by_cases hx2 : x = p₂
  · exact Or.inr ⟨hx2, last_adj_mem h hy (hx2 ▸ ha)⟩
  exact (Set.disjoint_left.mp hdisj
    (h.first ⟨hy, x, ⟨hxF, hx2⟩, ha.symm⟩)
    (h.last ⟨hy, x, ⟨hxF, hx1⟩, ha.symm⟩)).elim

/-- A star outside a branch has no vertex in its rung. -/
theorem star_disjoint_branch (hcq : c ∉ q) :
    Disjoint (N c) (edgeImage φ (trackEdges q)) := by
  apply Set.disjoint_left.mpr
  intro x hxN hxR
  rw [star_eq h c] at hxN
  obtain ⟨e, he, hec, rfl⟩ := hxN
  have heq := (image_mem_iff he).mp hxR
  obtain ⟨d, hed⟩ := Sym2.mem_iff_exists.mp hec.2
  rw [hed] at heq
  exact hcq (BranchClassification.mem_of_mem_trackEdges heq).1

end Workspace.ProofLemmas.Thm58StarBranchBasics
