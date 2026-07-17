import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.MultigraphBasic

/-!
# Two-element assignments (the paper's relaxed 3-edge-colouring)

The hypothesis of Lemma 2.1 of *"A Proof of the Cycle Double Cover Conjecture"*: an
assignment `P : β → Set Gamma` of a two-element palette to every edge such that, for every
vertex `v` and colour `s`, the number of edges incident to `v` whose palette contains `s`
is `0` or `2`. Looplessness and cubicness are separate hypotheses of Lemma 2.1 and are not
part of this predicate. Cardinalities use `Set.encard` (`ℕ∞`-valued), so `∈ {0, 2}` says
exactly "zero or two" with no finiteness side-condition.
-/

open Set

open scoped Graph

open Workspace.Types.Gamma

namespace Graph

variable {α β : Type*} {G : Graph α β} {P Q : β → Set Gamma} {e f : β} {v : α} {s : Gamma}

/-! ## The edges at a vertex carrying a given colour -/

/-- The set of edges **incident to `v`** whose palette contains the colour `s`; the paper's
`{e ∋ v : s ∈ P_e}`. This is a set of edges, not of edge-ends. -/
def paletteIncidenceSet (G : Graph α β) (P : β → Set Gamma) (v : α) (s : Gamma) :
    Set β :=
  {e ∈ G.incidenceSet v | s ∈ P e}

@[simp]
lemma mem_paletteIncidenceSet (G : Graph α β) (P : β → Set Gamma) (v : α) (s : Gamma)
    (e : β) : e ∈ G.paletteIncidenceSet P v s ↔ G.Inc e v ∧ s ∈ P e := Iff.rfl

lemma paletteIncidenceSet_subset_incidenceSet (G : Graph α β) (P : β → Set Gamma)
    (v : α) (s : Gamma) : G.paletteIncidenceSet P v s ⊆ G.incidenceSet v :=
  fun _ he ↦ he.1

lemma paletteIncidenceSet_subset_edgeSet (G : Graph α β) (P : β → Set Gamma)
    (v : α) (s : Gamma) : G.paletteIncidenceSet P v s ⊆ E(G) :=
  (G.paletteIncidenceSet_subset_incidenceSet P v s).trans (G.incidenceSet_subset_edgeSet v)

/-! ## The predicate -/

/-- **The paper's relaxed 3-edge-colouring** (hypothesis of Lemma 2.1): an assignment `P`
such that every edge of `G` receives a two-element palette, and at every vertex every colour
is carried by exactly `0` or exactly `2` incident edges. Looplessness and cubicness of `G`
are not part of this predicate. -/
structure IsTwoElementAssignment (G : Graph α β) (P : β → Set Gamma) : Prop where
  /-- Every edge of `G` is assigned a two-element subset of `Γ`. -/
  encard_palette : ∀ e ∈ E(G), (P e).encard = 2
  /-- At every vertex, every colour is carried by exactly `0` or exactly `2` incident edges. -/
  encard_paletteIncidenceSet :
    ∀ v ∈ V(G), ∀ s : Gamma, (G.paletteIncidenceSet P v s).encard ∈ ({0, 2} : Set ℕ∞)

/-- The incidence-count condition, spelled out as a disjunction. -/
lemma IsTwoElementAssignment.encard_eq_zero_or_eq_two
    (h : G.IsTwoElementAssignment P) (hv : v ∈ V(G)) (s : Gamma) :
    (G.paletteIncidenceSet P v s).encard = 0 ∨ (G.paletteIncidenceSet P v s).encard = 2 := by
  simpa using h.encard_paletteIncidenceSet v hv s

/-- **The two colours of an edge are distinct**: the palette of an edge is an unordered pair
of different elements of `Γ`. -/
lemma IsTwoElementAssignment.exists_pair_palette
    (h : G.IsTwoElementAssignment P) (he : e ∈ E(G)) :
    ∃ a b : Gamma, a ≠ b ∧ P e = {a, b} :=
  Set.encard_eq_two.1 (h.encard_palette e he)

/-- The palette of an edge of `G` contains two distinct colours. -/
lemma IsTwoElementAssignment.nontrivial_palette
    (h : G.IsTwoElementAssignment P) (he : e ∈ E(G)) : (P e).Nontrivial := by
  obtain ⟨a, b, hab, hP⟩ := h.exists_pair_palette he
  exact hP ▸ Set.nontrivial_pair hab

/-- **A colour seen at a vertex is seen exactly twice there.** -/
lemma IsTwoElementAssignment.encard_eq_two_of_mem
    (h : G.IsTwoElementAssignment P) (hv : v ∈ V(G)) (he : G.Inc e v)
    (hs : s ∈ P e) : (G.paletteIncidenceSet P v s).encard = 2 := by
  refine (h.encard_eq_zero_or_eq_two hv s).resolve_left fun h0 ↦ ?_
  rw [Set.encard_eq_zero] at h0
  exact absurd (h0 ▸ (⟨he, hs⟩ : e ∈ G.paletteIncidenceSet P v s)) (Set.notMem_empty e)

/-- **A colour occurring at a vertex occurs on a second edge there**: colours come in pairs
at each vertex. -/
lemma IsTwoElementAssignment.exists_ne_inc_mem_palette
    (h : G.IsTwoElementAssignment P) (hv : v ∈ V(G)) (he : G.Inc e v)
    (hs : s ∈ P e) : ∃ f, f ≠ e ∧ G.Inc f v ∧ s ∈ P f := by
  obtain ⟨a, b, hab, hset⟩ := Set.encard_eq_two.1 (h.encard_eq_two_of_mem hv he hs)
  have ha : a ∈ G.paletteIncidenceSet P v s := by rw [hset]; exact Or.inl rfl
  have hb : b ∈ G.paletteIncidenceSet P v s := by rw [hset]; exact Or.inr rfl
  have hmem : e ∈ ({a, b} : Set β) := hset ▸ (⟨he, hs⟩ : e ∈ G.paletteIncidenceSet P v s)
  rcases hmem with rfl | rfl
  · exact ⟨b, Ne.symm hab, hb.1, hb.2⟩
  · exact ⟨a, hab, ha.1, ha.2⟩

/-- The incidence-count condition restated with `Set.ncard`. -/
lemma IsTwoElementAssignment.ncard_mem
    (h : G.IsTwoElementAssignment P) (hv : v ∈ V(G)) (s : Gamma) :
    (G.paletteIncidenceSet P v s).ncard ∈ ({0, 2} : Set ℕ) := by
  rcases h.encard_eq_zero_or_eq_two hv s with hc | hc <;> rw [Set.ncard_def, hc] <;> simp

/-! ## Junk-independence

The predicate only inspects `P` on `E(G)`, so two assignments agreeing on `E(G)` are
interchangeable. -/

lemma paletteIncidenceSet_congr (G : Graph α β) (v : α) (s : Gamma)
    (hPQ : ∀ e ∈ E(G), P e = Q e) :
    G.paletteIncidenceSet P v s = G.paletteIncidenceSet Q v s := by
  ext e
  simp only [Graph.mem_paletteIncidenceSet, and_congr_right_iff]
  exact fun he ↦ by rw [hPQ e (he.edge_mem)]

lemma isTwoElementAssignment_congr (G : Graph α β) (hPQ : ∀ e ∈ E(G), P e = Q e) :
    G.IsTwoElementAssignment P ↔ G.IsTwoElementAssignment Q := by
  have key : ∀ (R S : β → Set Gamma), (∀ e ∈ E(G), R e = S e) →
      G.IsTwoElementAssignment R → G.IsTwoElementAssignment S := by
    refine fun R S hRS h ↦ ⟨fun e he ↦ ?_, fun v hv s ↦ ?_⟩
    · rw [← hRS e he]; exact h.encard_palette e he
    · rw [← Graph.paletteIncidenceSet_congr G v s hRS]
      exact h.encard_paletteIncidenceSet v hv s
  exact ⟨key P Q hPQ, key Q P fun e he ↦ (hPQ e he).symm⟩

end Graph
