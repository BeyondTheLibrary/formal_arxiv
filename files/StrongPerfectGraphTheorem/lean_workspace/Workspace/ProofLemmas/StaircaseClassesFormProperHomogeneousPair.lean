import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.StrongStaircaseComponentStructure

set_option autoImplicit false

/-!
# The last line of the proof of 13.4

PAPER (§13, printed p. 86, the closing line of the proof of 13.4): *"But then
`(A, B)` is a proper homogeneous pair in `G`.  (This is the only place in the
entire paper where we use such pairs.)  This proves 13.4."*

At that point of the printed proof `V(G)` has been partitioned into
`A, B, C, D, A₀, B₀, N, M`, claim (2) has given `N ≠ ∅`, and claim (3) has given
`C ∪ D = ∅`.  So `V(G) \ (A ∪ B) = A₀ ∪ B₀ ∪ N ∪ M`, and the four classes are
exactly the four cells the definition of a proper homogeneous pair asks for:

* `A₀` (the left-stars) is `A`-complete and `B`-anticomplete,
* `B₀` (the right-stars) is `B`-complete and `A`-anticomplete,
* `N` (the `A ∪ B`-complete vertices) is complete to both,
* `M` (the union of the components of `H` with no attachment in `V(S)`) is
  anticomplete to both,

`N ≠ ∅` and `M ≠ ∅` (the latter because `M` contains the interior of the
banister `R₀`), while `a₀ ∈ A₀` and `b₀ ∈ B₀` because `a₀` is a left-star and
`b₀` a right-star; so all four cells are nonempty.  The only inputs beyond the
listed hypotheses are the two facts, read straight off step-connectedness of
the strip `S = (A, C, B)`, that

* no vertex of `B` is `A`-complete and no vertex of `A` is `B`-complete
  (each vertex of `A ∪ B ∪ C` lies in a step, and the two rungs of a step have
  no edges between them beyond `a₁a₂` and `b₁b₂`), and
* with `C = ∅` every rung is a single edge, so every vertex of `A` has a
  neighbour in `B` and conversely.
-/

namespace Workspace.ProofLemmas.StaircaseClassesFormProperHomogeneousPair

open Workspace.Types.Core.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions.SPGT

theorem staircaseClassesFormProperHomogeneousPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀) :
    let VS : Set V := A ∪ B ∪ C
    let A₀ : Set V := {v : V | IsLeftStar H A C B v}
    let B₀ : Set V := {v : V | IsRightStar H A C B v}
    let N : Set V := {v : V | VertexComplete H v (A ∪ B)}
    let H₀ : Set V := Set.univ \ (VS ∪ A₀ ∪ B₀ ∪ N)
    let M : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      attachments H F VS = ∅}
    let D : Set V := {v : V | ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧
      (attachments H F VS).Nonempty}
    Disjoint A B ∧ Disjoint A C ∧ Disjoint A D ∧ Disjoint A A₀ ∧ Disjoint A B₀ ∧
      Disjoint A N ∧ Disjoint A M ∧ Disjoint B C ∧ Disjoint B D ∧ Disjoint B A₀ ∧
      Disjoint B B₀ ∧ Disjoint B N ∧ Disjoint B M ∧ Disjoint C D ∧ Disjoint C A₀ ∧
      Disjoint C B₀ ∧ Disjoint C N ∧ Disjoint C M ∧ Disjoint D A₀ ∧ Disjoint D B₀ ∧
      Disjoint D N ∧ Disjoint D M ∧ Disjoint A₀ B₀ ∧ Disjoint A₀ N ∧ Disjoint A₀ M ∧
      Disjoint B₀ N ∧ Disjoint B₀ M ∧ Disjoint N M ∧
      A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M = Set.univ →
    (∀ F : Set V, F.Nonempty → IsComponent H H₀ F → F ⊆ M →
      attachments H F VS = ∅) →
    ({v : V | v ∈ interior R₀}).Nonempty → {v : V | v ∈ interior R₀} ⊆ M →
    N.Nonempty → C ∪ D = ∅ →
    IsProperHomogeneousPair H A B := by
  intro VS A₀ B₀ N H₀ M D hpart _hMatt hRne hRsub hN hCD
  have hVS : VS = A ∪ B ∪ C := rfl
  -- the union equation of the partition is the only piece of `hpart` we use
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    huniv⟩ := hpart
  obtain ⟨hCempty, hDempty⟩ := Set.union_empty_iff.mp hCD
  -- the staircase data
  have hsc : StepConnected H A C B := hstairs.1.1.1
  have hban : IsBanister H A C B a₀ R₀ b₀ := hstairs.1.1.2.1
  obtain ⟨⟨hAB, _hAC, _hBC⟩, ⟨hAne, hBne⟩, hrung, hstep, _hpart2⟩ := hsc
  have hnAB : ∀ x : V, x ∈ A → x ∈ B → False := fun x hx hx' =>
    (Set.disjoint_left.mp hAB hx) hx'
  ---------------------------------------------------------------------------
  -- With `C = ∅` every rung is a single edge.
  ---------------------------------------------------------------------------
  have hrungAdj : ∀ (a' : V) (p : List V) (b' : V),
      IsRungOfStrip H A C B a' p b' → H.Adj a' b' := by
    intro a' p b' hr
    obtain ⟨hp, ha', hb', -, -, hC'⟩ := hr
    have hlen2 : p.length ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      have hIL := PathBasics.interior_length p
      have hpos : 0 < (interior p).length := by omega
      have hx : (interior p)[0]'hpos ∈ interior p := List.getElem_mem hpos
      have hmemC := hC' _ hx
      rw [hCempty] at hmemC
      exact hmemC
    have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
    have hne1 : p.length ≠ 1 := by
      intro h1
      obtain ⟨x, hxe⟩ := List.length_eq_one_iff.mp h1
      subst hxe
      have h1' : x = a' := by have := hp.2.1; simpa using this
      have h2' : x = b' := by have := hp.2.2; simpa using this
      exact hnAB a' ha' (by rw [← h1', h2']; exact hb')
    have hl1 : pathLength p = 1 := by
      simp only [pathLength]; omega
    exact PathBasics.isPathFrom_ends_adj_of_length_one hp hl1
  ---------------------------------------------------------------------------
  -- No vertex of `B` is `A`-complete, and no vertex of `A` is `B`-complete.
  ---------------------------------------------------------------------------
  have key : ∀ b ∈ B, ¬ VertexComplete H b A := by
    intro b hb hcomp
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hmem⟩ := hstep b (Or.inl (Or.inr hb))
    obtain ⟨hr1, hr2, -, hadj⟩ := hs
    have ha₁A : a₁ ∈ A := hr1.2.1
    have hb₁B : b₁ ∈ B := hr1.2.2.1
    have ha₂A : a₂ ∈ A := hr2.2.1
    have hb₂B : b₂ ∈ B := hr2.2.2.1
    have ha₁mem : a₁ ∈ R₁ := PathBasics.head_mem hr1.1.2.1
    have ha₂mem : a₂ ∈ R₂ := PathBasics.head_mem hr2.1.2.1
    rcases hmem with h | h
    · have hAdj : H.Adj b a₂ := hcomp a₂ ha₂A
      rcases (hadj b h a₂ ha₂mem).mp hAdj with ⟨he, -⟩ | ⟨-, he⟩
      · exact hnAB b (by rw [he]; exact ha₁A) hb
      · exact hnAB a₂ ha₂A (by rw [he]; exact hb₂B)
    · have hAdj : H.Adj a₁ b := (hcomp a₁ ha₁A).symm
      rcases (hadj a₁ ha₁mem b h).mp hAdj with ⟨-, he⟩ | ⟨he, -⟩
      · exact hnAB b (by rw [he]; exact ha₂A) hb
      · exact hnAB a₁ ha₁A (by rw [he]; exact hb₁B)
  have key2 : ∀ a ∈ A, ¬ VertexComplete H a B := by
    intro a ha hcomp
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hmem⟩ := hstep a (Or.inl (Or.inl ha))
    obtain ⟨hr1, hr2, -, hadj⟩ := hs
    have ha₁A : a₁ ∈ A := hr1.2.1
    have hb₁B : b₁ ∈ B := hr1.2.2.1
    have ha₂A : a₂ ∈ A := hr2.2.1
    have hb₂B : b₂ ∈ B := hr2.2.2.1
    have hb₁mem : b₁ ∈ R₁ := PathBasics.getLast_mem hr1.1.2.2
    have hb₂mem : b₂ ∈ R₂ := PathBasics.getLast_mem hr2.1.2.2
    rcases hmem with h | h
    · have hAdj : H.Adj a b₂ := hcomp b₂ hb₂B
      rcases (hadj a h b₂ hb₂mem).mp hAdj with ⟨-, he⟩ | ⟨he, -⟩
      · exact hnAB a₂ ha₂A (by rw [← he]; exact hb₂B)
      · exact hnAB a ha (by rw [he]; exact hb₁B)
    · have hAdj : H.Adj b₁ a := (hcomp b₁ hb₁B).symm
      rcases (hadj b₁ hb₁mem a h).mp hAdj with ⟨he, -⟩ | ⟨-, he⟩
      · exact hnAB a₁ ha₁A (by rw [← he]; exact hb₁B)
      · exact hnAB a ha (by rw [he]; exact hb₂B)
  ---------------------------------------------------------------------------
  -- Every vertex of `A` has a neighbour in `B`, and conversely.
  ---------------------------------------------------------------------------
  have hAnbr : ∀ a ∈ A, ¬ VertexAnticomplete H a B := by
    intro a ha hanti
    obtain ⟨a', p, b', hr, hmem⟩ := hrung a (Or.inl (Or.inl ha))
    have haa : a = a' := hr.2.2.2.1 a hmem ha
    have hadj := hrungAdj a' p b' hr
    exact hanti b' hr.2.2.1 (by rw [haa]; exact hadj)
  have hBnbr : ∀ b ∈ B, ¬ VertexAnticomplete H b A := by
    intro b hb hanti
    obtain ⟨a', p, b', hr, hmem⟩ := hrung b (Or.inl (Or.inr hb))
    have hbb : b = b' := hr.2.2.2.2.1 b hmem hb
    have hadj := hrungAdj a' p b' hr
    exact hanti a' hr.2.1 (by rw [hbb]; exact hadj.symm)
  ---------------------------------------------------------------------------
  -- `M` is anticomplete to `V(S)`.
  ---------------------------------------------------------------------------
  have hMnbr : ∀ v : V, v ∈ M → ∀ x ∈ VS, ¬ H.Adj v x := by
    intro v hv x hx hadjvx
    have hv' : ∃ F : Set V, IsComponent H H₀ F ∧ v ∈ F ∧ attachments H F VS = ∅ := hv
    obtain ⟨F, -, hvF, hFatt⟩ := hv'
    have hxatt : x ∈ attachments H F VS := ⟨hx, v, hvF, hadjvx.symm⟩
    rw [hFatt] at hxatt
    exact hxatt
  have hMnbrA : ∀ v : V, v ∈ M → VertexAnticomplete H v A := fun v hv x hx =>
    hMnbr v hv x (by rw [hVS]; exact Or.inl (Or.inl hx))
  have hMnbrB : ∀ v : V, v ∈ M → VertexAnticomplete H v B := fun v hv x hx =>
    hMnbr v hv x (by rw [hVS]; exact Or.inl (Or.inr hx))
  ---------------------------------------------------------------------------
  -- The two union equations of the definition of a proper homogeneous pair.
  ---------------------------------------------------------------------------
  have hmemuniv : ∀ v : V, v ∈ A ∪ B ∪ C ∪ D ∪ A₀ ∪ B₀ ∪ N ∪ M := by
    intro v; rw [huniv]; trivial
  have hEqA : {v : V | VertexComplete H v A} ∪ {v : V | v ∉ A ∧ VertexAnticomplete H v A}
      = (A ∪ B)ᶜ := by
    apply Set.eq_of_subset_of_subset
    · rintro v (hc | ⟨hnA, hanti⟩)
      · rintro (hvA | hvB)
        · exact H.irrefl (hc v hvA)
        · exact key v hvB hc
      · rintro (hvA | hvB)
        · exact hnA hvA
        · exact hBnbr v hvB hanti
    · intro v hv
      have hvA : v ∉ A := fun h => hv (Or.inl h)
      have hvB : v ∉ B := fun h => hv (Or.inr h)
      rcases hmemuniv v with (((((((h | h) | h) | h) | h) | h) | h) | h)
      · exact absurd h hvA
      · exact absurd h hvB
      · rw [hCempty] at h; exact absurd h (Set.notMem_empty v)
      · rw [hDempty] at h; exact absurd h (Set.notMem_empty v)
      · exact Or.inl (h.2.1)
      · exact Or.inr ⟨hvA, fun x hx => h.2.2 x (Or.inl hx)⟩
      · exact Or.inl (fun x hx => h x (Or.inl hx))
      · exact Or.inr ⟨hvA, hMnbrA v h⟩
  have hEqB : {v : V | VertexComplete H v B} ∪ {v : V | v ∉ B ∧ VertexAnticomplete H v B}
      = (A ∪ B)ᶜ := by
    apply Set.eq_of_subset_of_subset
    · rintro v (hc | ⟨hnB, hanti⟩)
      · rintro (hvA | hvB)
        · exact key2 v hvA hc
        · exact H.irrefl (hc v hvB)
      · rintro (hvA | hvB)
        · exact hAnbr v hvA hanti
        · exact hnB hvB
    · intro v hv
      have hvA : v ∉ A := fun h => hv (Or.inl h)
      have hvB : v ∉ B := fun h => hv (Or.inr h)
      rcases hmemuniv v with (((((((h | h) | h) | h) | h) | h) | h) | h)
      · exact absurd h hvA
      · exact absurd h hvB
      · rw [hCempty] at h; exact absurd h (Set.notMem_empty v)
      · rw [hDempty] at h; exact absurd h (Set.notMem_empty v)
      · exact Or.inr ⟨hvB, fun x hx => h.2.2 x (Or.inl hx)⟩
      · exact Or.inl (h.2.1)
      · exact Or.inl (fun x hx => h x (Or.inr hx))
      · exact Or.inr ⟨hvB, hMnbrB v h⟩
  ---------------------------------------------------------------------------
  -- The four cells are nonempty: `N`, `a₀ ∈ A₀`, `b₀ ∈ B₀`, and `R₀* ⊆ M`.
  ---------------------------------------------------------------------------
  have hls : IsLeftStar H A C B a₀ := hban.2.2.1
  have hrs : IsRightStar H A C B b₀ := hban.2.2.2.1
  obtain ⟨n, hn⟩ := hN
  have hn' : VertexComplete H n (A ∪ B) := hn
  obtain ⟨w, hw⟩ := hRne
  have hwM : w ∈ M := hRsub hw
  refine ⟨hAB, hAne, hBne, hEqA, hEqB, ⟨n, ?_, ?_⟩, ⟨a₀, ?_, ?_⟩, ⟨b₀, ?_, ?_⟩,
    ⟨w, ?_, ?_⟩⟩
  · exact fun x hx => hn' x (Or.inl hx)
  · exact fun x hx => hn' x (Or.inr hx)
  · exact hls.2.1
  · exact fun x hx => hls.2.2 x (Or.inl hx)
  · exact fun x hx => hrs.2.2 x (Or.inl hx)
  · exact hrs.2.1
  · exact hMnbrA w hwM
  · exact hMnbrB w hwM

end Workspace.ProofLemmas.StaircaseClassesFormProperHomogeneousPair
