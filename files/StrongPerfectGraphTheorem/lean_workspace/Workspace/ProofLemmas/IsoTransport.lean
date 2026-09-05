import Mathlib
import Workspace.Types.Core

/-!
# Transport of the SPGT vocabulary along graph isomorphisms

Infrastructure for the proof of 1.2.  The paper argues about a *minimum
counterexample* among **all** finite graphs, while the Lean statement of 1.2 is
about one fixed finite vertex type `V`.  Bridging the two requires knowing that
every notion the paper uses (holes, Bergeness, perfection) is invariant under
graph isomorphism, and that every finite graph is isomorphic to a graph on
`Fin n`.

None of this has a counterpart in the printed paper — the authors treat graphs
up to isomorphism silently.
-/

namespace Workspace.ProofLemmas.IsoTransport

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V W : Type*}

/-! ## Group A — complement and holes transport -/

section GroupA

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- An isomorphism `G ≃g H` is also an isomorphism `Gᶜ ≃g Hᶜ`.

Mathlib has `SimpleGraph.Embedding.complEquiv : (G ↪g H) ≃ (Gᶜ ↪g Hᶜ)` but no
isomorphism counterpart, so we build it by hand. -/
def Iso.compl (e : G ≃g H) : Gᶜ ≃g Hᶜ :=
  { e.toEquiv with
    map_rel_iff' := by
      intro a b
      simp only [RelIso.coe_fn_toEquiv, SimpleGraph.compl_adj, ne_eq,
        EmbeddingLike.apply_eq_iff_eq, SimpleGraph.Iso.map_adj_iff] }

@[simp]
theorem Iso.compl_apply (e : G ≃g H) (v : V) : (Iso.compl e) v = e v := rfl

/-- An alias for `Iso.compl` under a name that cannot be confused with anything
in Mathlib's `SimpleGraph.Iso` namespace. -/
abbrev isoCompl (e : G ≃g H) : Gᶜ ≃g Hᶜ := Iso.compl e

/-- Holes are transported by isomorphisms: the image of a hole is a hole. -/
theorem isHoleList_map (e : G ≃g H) {c : List V} (hc : IsHoleList G c) :
    IsHoleList H (c.map (⇑e)) := by
  obtain ⟨h4, hnd, hadj⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · simpa using h4
  · exact hnd.map (EquivLike.injective e)
  · intro i j hi hj
    simp only [List.getElem_map, List.length_map, SimpleGraph.Iso.map_adj_iff]
    exact hadj i j _ _

/-- Mapping a list along an isomorphism does not change its hole length. -/
@[simp]
theorem holeLength_map (e : G ≃g H) (c : List V) :
    holeLength (c.map (⇑e)) = holeLength c := by
  simp [holeLength]

/-- Bergeness is preserved by isomorphisms. -/
theorem berge_of_iso (e : G ≃g H) (h : Berge G) : Berge H := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro c hc
    have := h1 (c.map (⇑e.symm)) (isHoleList_map e.symm hc)
    simpa [holeLength] using this
  · intro c hc
    have := h2 (c.map (⇑(Iso.compl e).symm)) (isHoleList_map (Iso.compl e).symm hc)
    simpa [holeLength] using this

/-- Bergeness is an isomorphism invariant. -/
theorem berge_iso (e : G ≃g H) : Berge G ↔ Berge H :=
  ⟨berge_of_iso e, berge_of_iso e.symm⟩

/-- `Berge` is symmetric under complementation.  (A private version, to avoid a
name clash with `HoleBasics.berge_compl`.) -/
theorem berge_compl_iso (G : SimpleGraph V) : Berge Gᶜ ↔ Berge G := by
  simp only [Berge, compl_compl]
  exact and_comm

end GroupA

/-! ## Group B — perfection transport -/

section GroupB

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- The chromatic number is an isomorphism invariant. -/
theorem chromaticNumber_iso (e : G ≃g H) : G.chromaticNumber = H.chromaticNumber :=
  le_antisymm (SimpleGraph.chromaticNumber_mono_of_hom e.toHom)
    (SimpleGraph.chromaticNumber_mono_of_hom e.symm.toHom)

/-- The image of an `n`-clique under an isomorphism is an `n`-clique. -/
theorem isNClique_map (e : G ≃g H) {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) :
    H.IsNClique n (s.map e.toEquiv.toEmbedding) := by
  constructor
  · rintro a ha b hb hab
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, Set.mem_image,
      Finset.mem_coe] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [SimpleGraph.Iso.map_adj_iff]
    exact hs.1 ha' hb' fun h => hab (congrArg _ h)
  · rw [Finset.card_map]
    exact hs.2

/-- The clique number is an isomorphism invariant. -/
theorem cliqueNum_iso (e : G ≃g H) : G.cliqueNum = H.cliqueNum := by
  simp only [SimpleGraph.cliqueNum]
  congr 1
  ext n
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s.map e.toEquiv.toEmbedding, isNClique_map e hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s.map e.symm.toEquiv.toEmbedding, isNClique_map e.symm hs⟩

/-- An isomorphism restricts to an isomorphism of induced subgraphs. -/
noncomputable def induceIso (e : G ≃g H) (X : Set V) :
    G.induce X ≃g H.induce (⇑e '' X) :=
  { Equiv.Set.image (⇑e) X (EquivLike.injective e) with
    map_rel_iff' := by
      intro a b
      simp [SimpleGraph.Iso.map_adj_iff] }

/-- Perfection is preserved by isomorphisms. -/
theorem isPerfect_of_iso (e : G ≃g H) (h : IsPerfect G) : IsPerfect H := by
  intro Y
  obtain ⟨X, rfl⟩ : ∃ X : Set V, ⇑e '' X = Y :=
    ⟨⇑e ⁻¹' Y, Set.image_preimage_eq _ (EquivLike.surjective e)⟩
  rw [← chromaticNumber_iso (induceIso e X), ← cliqueNum_iso (induceIso e X)]
  exact h X

/-- Perfection is an isomorphism invariant. -/
theorem isPerfect_iso (e : G ≃g H) : IsPerfect G ↔ IsPerfect H :=
  ⟨isPerfect_of_iso e, isPerfect_of_iso e.symm⟩

/-- Being a counterexample to 1.2 is an isomorphism invariant. -/
theorem not_perfect_iff_berge_iso (e : G ≃g H) :
    (¬ (IsPerfect G ↔ Berge G)) ↔ (¬ (IsPerfect H ↔ Berge H)) := by
  rw [isPerfect_iso e, berge_iso e]

end GroupB

/-! ## Group C — the minimum counterexample -/

section GroupC

/-- Every finite graph is isomorphic to a graph on `Fin (Fintype.card V)`. -/
theorem exists_iso_fin [Fintype V] (G : SimpleGraph V) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), Nonempty (G ≃g H) :=
  ⟨G.overFin rfl, ⟨G.overFinIso rfl⟩⟩

/-- If some finite graph is a counterexample to "perfect iff Berge", then a
*minimum* counterexample exists, on some `Fin n`. -/
theorem exists_minimumImperfect [Fintype V] (G : SimpleGraph V)
    (h : ¬ (IsPerfect G ↔ Berge G)) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), MinimumImperfect H := by
  classical
  have hex : ∃ n : ℕ, ∃ K : SimpleGraph (Fin n), ¬ (IsPerfect K ↔ Berge K) := by
    obtain ⟨H, ⟨e⟩⟩ := exists_iso_fin G
    exact ⟨Fintype.card V, H, (not_perfect_iff_berge_iso e).mp h⟩
  obtain ⟨H₀, hH₀⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, H₀, hH₀, ?_⟩
  intro m K hK
  have hm : ∃ K' : SimpleGraph (Fin m), ¬ (IsPerfect K' ↔ Berge K') := ⟨K, hK⟩
  simpa using Nat.find_min' hex hm

variable {G : SimpleGraph V}

/-- A minimum imperfect graph is not perfect — given the implication
"perfect ⇒ Berge" (the paper's E5) for the graph itself. -/
theorem minimumImperfect_not_perfect [Fintype V] (hG : MinimumImperfect G)
    (hE5 : IsPerfect G → Berge G) : ¬ IsPerfect G := by
  intro hp
  exact hG.1 ⟨fun _ => hE5 hp, fun _ => hp⟩

/-- A minimum imperfect graph is Berge — given the implication "perfect ⇒ Berge"
(the paper's E5) for the graph itself. -/
theorem minimumImperfect_berge [Fintype V] (hG : MinimumImperfect G)
    (hE5 : IsPerfect G → Berge G) : Berge G := by
  by_contra hb
  have hnp : ¬ IsPerfect G := fun hp => hb (hE5 hp)
  exact hG.1 ⟨fun hp => absurd hp hnp, fun hbb => absurd hbb hb⟩

/-- The complement of a minimum imperfect graph is minimum imperfect — given the
paper's 1.1 at `Gᶜ` (perfection is preserved by complementation) and E5 at `G`. -/
theorem minimumImperfect_compl [Fintype V] (hG : MinimumImperfect G)
    (h11 : IsPerfect Gᶜ → IsPerfect Gᶜᶜ) (hE5 : IsPerfect G → Berge G) :
    MinimumImperfect Gᶜ := by
  refine ⟨?_, hG.2⟩
  have hnp : ¬ IsPerfect G := minimumImperfect_not_perfect hG hE5
  have hb : Berge G := minimumImperfect_berge hG hE5
  have hbc : Berge Gᶜ := (berge_compl_iso G).mpr hb
  intro hiff
  have hpc : IsPerfect Gᶜ := hiff.mpr hbc
  exact hnp (by simpa using h11 hpc)

/-- Variant of `minimumImperfect_compl` that takes the paper's 1.1 in its general
form (for every graph on `V`) instead of E5. -/
theorem minimumImperfect_compl' [Fintype V] (hG : MinimumImperfect G)
    (h11 : ∀ K : SimpleGraph V, IsPerfect K → IsPerfect Kᶜ) :
    MinimumImperfect Gᶜ := by
  refine ⟨?_, hG.2⟩
  intro hiff
  have hcc : ¬ (IsPerfect G ↔ Berge G) := hG.1
  rw [berge_compl_iso G] at hiff
  by_cases hb : Berge G
  · have hpc : IsPerfect Gᶜ := hiff.mpr hb
    have hp : IsPerfect G := by simpa using h11 Gᶜ hpc
    exact hcc ⟨fun _ => hb, fun _ => hp⟩
  · have hp : IsPerfect G := by
      by_contra hp
      exact hcc ⟨fun hx => absurd hx hp, fun hx => absurd hx hb⟩
    exact hb (hiff.mp (h11 G hp))

end GroupC

end Workspace.ProofLemmas.IsoTransport
