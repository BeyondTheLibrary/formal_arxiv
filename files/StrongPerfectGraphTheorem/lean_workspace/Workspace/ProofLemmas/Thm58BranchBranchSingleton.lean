import Workspace.ProofLemmas.Thm58BranchBranchStars

/-!
# A single neighbor cannot satisfy the conclusion with the fixed first end

Every vertex of `H` has degree at least two. At a branch-vertex the degree is at
least three. Hence neither a full star nor a branch-vertex star with one edge
removed fits in a singleton. This lets claim (6) dispose of the case in claim (7)
where the unique neighbor is an end-edge of its branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- The appearance isomorphism preserves the size of every vertex star. -/
theorem star_ncard (hN : ∀ c, N c =
    {x | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)}) (c : Fin n) :
    (N c).ncard = (H.neighborSet c).ncard := by
  let f : ↥(incidentEdges H c) → ↥(N c) := fun e =>
    ⟨(↑(φ ⟨e.1, e.2.1⟩) : V), by rw [hN]; exact ⟨e.1, e.2.1, e.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro e d hed
    have hval : (↑(φ ⟨e.1, e.2.1⟩) : V) = (↑(φ ⟨d.1, d.2.1⟩) : V) :=
      congrArg (fun y : ↥(N c) => (y : V)) hed
    exact Subtype.ext (congrArg (fun d : H.edgeSet => d.1) (φ.injective (Subtype.ext hval)))
  have hsurj : Function.Surjective f := by
    intro y
    have hy := Eq.mp (congrArg (fun S : Set V => y.1 ∈ S) (hN c)) y.2
    obtain ⟨e, he, hec, hye⟩ := hy
    exact ⟨⟨e, hec⟩, Subtype.ext hye.symm⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Thm84RungEndDictionary.incidentEdges_ncard] at hcard
  exact hcard.symm

/-- Subdividing a graph of minimum degree three leaves minimum degree at least two. -/
theorem two_le_degree (hJ : IsKConnected J 3) (hsub : IsSubdivision J H) (c : Fin n) :
    2 ≤ (H.neighborSet c).ncard := by
  obtain ⟨ι, T, hι, ht, hl, _, hd, hnew, hcover, _⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hbv := SubdivisionCounting.range_subset_branchVertices hι ht hl hd hnew hdeg
  rcases hcover c with ⟨u, rfl⟩ | ⟨u, v, huv, hc⟩
  · have h3 : 3 ≤ (H.neighborSet (ι u)).ncard := hbv ⟨u, rfl⟩
    omega
  · obtain ⟨e, f, he, hf, hef, hce, hcf⟩ :=
      Thm58SingletonCase.two_edges_at_interior (ht u v huv).1 hc
    have hmem : ∀ e ∈ trackEdges (T u v), e ∈ H.edgeSet := by
      rintro g ⟨i, hi, rfl⟩
      exact (ht u v huv).1.2.2 i hi
    have hsubpair : ({e, f} : Set (Sym2 (Fin n))) ⊆ incidentEdges H c := by
      rintro g (rfl | rfl)
      · exact ⟨hmem _ he, hce⟩
      · exact ⟨hmem _ hf, hcf⟩
    have hle := Set.ncard_le_ncard hsubpair (Set.toFinite _)
    rwa [Set.ncard_pair hef, Thm84RungEndDictionary.incidentEdges_ncard] at hle

/-- An end with just one neighbor cannot meet any alternative with its current name. -/
theorem not_outcome_of_unique_neighbor
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {r : V} (hunique : ∀ y ∈ K, G.Adj p₁ y → y = r) :
    ¬ Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  have hNK : ∀ c, N c ⊆ K := by
    intro c y hy
    rw [h.2.2.2.1 c] at hy
    obtain ⟨e, he, _, rfl⟩ := hy
    exact (φ ⟨e, he⟩).2
  have hfull : ∀ c, ¬ (∀ y ∈ N c, G.Adj p₁ y) := by
    intro c hc
    have hsub : N c ⊆ {r} := fun y hy => hunique y (hNK c hy) (hc y hy)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [star_ncard h.2.2.2.1 c, Set.ncard_singleton] at hle
    have htwo := two_le_degree h.2.1 h.2.2.1.1 c
    omega
  have hmissing : ∀ c ∈ branchVertices H, ∀ s : V,
      ¬ (∀ y ∈ N c \ {s}, G.Adj p₁ y) := by
    intro c hc s hcomp
    have hsub : N c ⊆ {r, s} := by
      intro y hy
      by_cases hys : y = s
      · exact Or.inr hys
      · exact Or.inl (hunique y (hNK c hy) (hcomp y ⟨hy, hys⟩))
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hpair : ({r, s} : Set V).ncard ≤ 2 := by
      by_cases hrs : r = s
      · simp [hrs]
      · rw [Set.ncard_pair hrs]
    rw [star_ncard h.2.2.2.1 c] at hle
    change 3 ≤ (H.neighborSet c).ncard at hc
    omega
  rintro (⟨c₁, _, _, hcomp, _⟩ |
    ⟨b₁, _, _, _, r₁, _, hb₁, _, _, _, _, _, _, _, halt⟩)
  · exact hfull c₁ hcomp
  · rcases halt with ha | hb | hc | hd
    · exact hmissing b₁ hb₁ r₁ ha.1
    · exact hmissing b₁ hb₁ r₁ hb.1
    · exact ends_ne h hc.1
    · exact hmissing b₁ hb₁ r₁ hd.2.1

end Workspace.ProofLemmas.Thm58BranchBranch
