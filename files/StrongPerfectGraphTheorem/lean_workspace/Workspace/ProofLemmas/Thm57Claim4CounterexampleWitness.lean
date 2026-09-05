import Workspace.ProofLemmas.Thm57Claim4Counterexample

/-! All hypotheses of the frozen six-terminal core hold for the nonedge example. -/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm57Claim4Counterexample

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Core Workspace.ProofLemmas.Thm57Setup

/-- None of the marked pairs is an edge of the graph. -/
theorem marked_nonedge : ∀ e ∈ X, e ∉ H.edgeSet := by
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    change s(a,b) ∈ X → ¬ H.Adj a b
    revert a b
    decide

/-- Deleting the marked nonedges leaves the graph unchanged. -/
theorem delete_eq : H.deleteEdges X = H := by
  ext a b
  rw [SimpleGraph.deleteEdges_adj]
  exact ⟨And.left, fun h => ⟨h, fun hx => marked_nonedge _ hx h⟩⟩

private def parent : Fin 18 → Fin 18 :=
  ![0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,0,13,0]

/-- All vertices belong to one component of `H \ X`. -/
theorem connected : ConnectedSet (H.deleteEdges X) Set.univ := by
  rw [delete_eq]
  have step : ∀ v : Fin 18, v ≠ 0 →
      (parent v).val < v.val ∧ H.Adj (parent v) v := by decide
  have reach (v : Fin 18) : (H.induce Set.univ).Reachable
      ⟨0, Set.mem_univ _⟩ ⟨v, Set.mem_univ _⟩ := by
    induction hn : v.val using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = 0
      · subst v
        exact SimpleGraph.Reachable.refl _
      · obtain ⟨hlt, hadj⟩ := step v hv
        exact (ih (parent v).val (by omega) (parent v) rfl).trans
          (SimpleGraph.Adj.reachable hadj)
  intro a b
  exact (reach a.val).symm.trans (reach b.val)

/-- Every marked pair lies inside the connected set, and the pairs are disjoint. -/
theorem marked_data :
    (∀ i, x i ∈ X) ∧
    (∀ i j, i ≠ j → DisjointEdges (x i) (x j)) ∧
    (∀ i, ∃ v ∈ (Set.univ : Set (Fin 18)), v ∈ x i) ∧
    (∃ i, ∀ v ∈ x i, v ∈ (Set.univ : Set (Fin 18))) := by
  unfold DisjointEdges
  decide

/-- The forbidden even track cannot exist because none of its edges can belong to `X`. -/
theorem noEvenTrack : NoEvenTrack57 H X := by
  rintro ⟨q, hq, htrack, _, hfirst, _⟩
  exact marked_nonedge _ hfirst (htrack.2.2 0 (by omega))

/-- For equally coloured ends of different marked pairs, this set separates the ends
once the two other ends of those pairs are removed. -/
private def side (i j : Fin 3) (u z : Fin 18) : Prop :=
  if u.val % 2 = 1 then
    if i < j then z.val < 4 * i.val + 4 ∨ 4 * j.val + 4 < z.val
    else 4 * j.val + 4 < z.val ∧ z.val < 4 * i.val + 4
  else
    if i < j then 4 * i.val + 1 < z.val ∧ z.val < 4 * j.val + 1
    else z.val < 4 * j.val + 1 ∨ 4 * i.val + 1 < z.val

private instance sideDecidable (i j : Fin 3) (u z : Fin 18) : Decidable (side i j u z) := by
  unfold side
  infer_instance

private theorem separation_certificate :
    ∀ (i j : Fin 3) (u v : Fin 18), i ≠ j → u ∈ x i → v ∈ x j → col u = col v →
      side i j u u ∧ ¬ side i j u v ∧
      ∀ s t : Fin 18, H.Adj s t →
        (s ∈ x i → s = u) → (s ∈ x j → s = v) →
        (t ∈ x i → t = u) → (t ∈ x j → t = v) →
        side i j u s → side i j u t := by
  decide

/-- Every endpoint-clean connection between different marked pairs has opposite-coloured
ends. The proof uses the finite separating sets, so it covers tracks of every length. -/
theorem different_color :
    ∀ i j, i ≠ j → ∀ u v P, u ∈ x i → v ∈ x j →
      EndpointCleanConnection H X (x i) (x j) u v P → col u ≠ col v := by
  intro i j hij u v P hu hv hP hcol
  obtain ⟨huS, hvS, hclosed⟩ := separation_certificate i j u v hij hu hv hcol
  have hlen : 0 < P.length := List.length_pos_of_ne_nil hP.1.1.1
  have hhead : P[0]'hlen = u := by
    have hh := hP.1.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at hh
    exact Option.some_injective _ hh
  have hlast : P[P.length - 1]'(by omega) = v := by
    have hh := hP.1.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have stays : ∀ k (hk : k < P.length), side i j u (P[k]'hk) := by
    intro k
    induction k with
    | zero => intro hk; simpa only [hhead] using huS
    | succ k ih =>
      intro hk
      exact hclosed (P[k]'(by omega)) (P[k + 1]'hk)
        (SimpleGraph.deleteEdges_adj.mp (hP.1.1.2.2 k hk)).1
        (hP.2.1 _ (List.getElem_mem (by omega)))
        (hP.2.2 _ (List.getElem_mem (by omega)))
        (hP.2.1 _ (List.getElem_mem hk))
        (hP.2.2 _ (List.getElem_mem hk)) (ih (by omega))
  exact hvS (hlast ▸ stays (P.length - 1) (by omega))

/-- The exact frozen statement of `sixTerminalCore`, specialized to `Fin 18`, is false.
The paper assumes `X ⊆ E(H)`, but this core statement does not. -/
theorem original_statement_false : ¬ (∀
    (H : SimpleGraph (Fin 18)) (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 (Fin 18)))
    (col : H.Coloring Bool) (x : Fin 3 → Sym2 (Fin 18)) (A : Set (Fin 18))
    (hconn : ConnectedSet (H.deleteEdges X) A)
    (hxX : ∀ i, x i ∈ X)
    (hdisj : ∀ i j, i ≠ j → DisjointEdges (x i) (x j))
    (hmeet : ∀ i, ∃ v ∈ A, v ∈ x i)
    (hinternal : ∃ i, ∀ v ∈ x i, v ∈ A)
    (hpair : ∀ i j, i ≠ j → ∀ u v P, u ∈ x i → v ∈ x j →
      EndpointCleanConnection H X (x i) (x j) u v P → col u ≠ col v)
    (hclaim3 :
      ¬ ∃ (b a₁ a₂ a₃ : (Fin 18)) (P₁ P₂ P₃ : List (Fin 18))
          (_h₁ : 2 ≤ P₁.length) (_h₂ : 2 ≤ P₂.length) (_h₃ : 2 ≤ P₃.length),
        IsTrackFrom H P₁ b a₁ ∧ IsTrackFrom H P₂ b a₂ ∧ IsTrackFrom H P₃ b a₃ ∧
        (∀ v : (Fin 18), v ∈ P₁ → v ∈ P₂ → v = b) ∧
        (∀ v : (Fin 18), v ∈ P₁ → v ∈ P₃ → v = b) ∧
        (∀ v : (Fin 18), v ∈ P₂ → v ∈ P₃ → v = b) ∧
        (∃ e ∈ trackEdges P₁, e ∈ X) ∧
        (∃ e ∈ trackEdges P₂, e ∈ X) ∧
        (∃ e ∈ trackEdges P₃, e ∈ X) ∧
        ((s(P₁[0], P₁[1]) ∉ X ∧ s(P₂[0], P₂[1]) ∉ X) ∨
         (s(P₁[0], P₁[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X) ∨
         (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X))), False) := by
  intro claimed
  obtain ⟨hxX, hdisj, hmeet, hinternal⟩ := marked_data
  exact claimed H cyclicallyThreeConnected X col x Set.univ connected hxX hdisj hmeet
    hinternal different_color (Thm57Claim3.thm57Claim3 H X noEvenTrack)

end Workspace.ProofLemmas.Thm57Claim4Counterexample
