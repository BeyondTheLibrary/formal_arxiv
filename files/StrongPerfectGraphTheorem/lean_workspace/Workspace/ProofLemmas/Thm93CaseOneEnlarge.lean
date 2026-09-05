import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.LineGraphDegree
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
import Workspace.ProofLemmas.EnlargementFromNonlocalStructure

/-!
# Outcome 5.8.1 in a degenerate appearance of `K₄`

PAPER (9.3, printed p. 48): *"If 5.8.1 holds then there is an appearance in `G` of some
`K₄`-enlargement, a contradiction."*

Two things have to be supplied.

*The path is off the appearance.*  Outcome 5.8.1 does not say in so many words that the path
`P` avoids `K`; it says that the only edges between `V(P)` and `K` are those from `p₁` to the
clique `N(c₁)` and from `p₂` to the clique `N(c₂)`.  That already forces `V(P) ∩ K = ∅`:
a vertex of `K` is an edge `e` of `H`, and every vertex of `H` has degree at least two, so `e`
has a neighbour in `L(H)`; that neighbour makes the vertex an end of `P`, and then the vertex
would have to be adjacent in `L(H)` to all of `δ_H(c)` for one of the two `c`, which is
impossible — either `e ∈ δ_H(c)`, and then the vertex is adjacent to itself, or `e` contains
two distinct neighbours of `c`, and then `H` has a triangle, contradicting bipartiteness.

*The construction itself.*  It is the construction of
`EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath`, for which the
paper prints no proof.  That lemma also concludes that the new appearance is nondegenerate, and
for that it needs the old appearance to be nondegenerate — which is exactly what fails here, the
whole point of case (1) of 9.3 being that `L(H)` *is* degenerate.  Since 9.3 only needs an
appearance of an enlargement, and not a nondegenerate one, the same construction is replayed
below with the nondegeneracy step dropped.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93CaseOneEnlarge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- Every element of `Sym2` is a pair. -/
private theorem sym2_pair {W : Type*} (e : Sym2 W) : ∃ a b : W, e = s(a, b) := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, rfl⟩

/-- **The path of outcome 5.8.1 is disjoint from the appearance.** -/
theorem path_disjoint {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (H : SimpleGraph (Fin n)) (K : Set V) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K) (N : Fin n → Set V)
    (hN : ∀ c, N c = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (P : List V) (p₁ p₂ : V) (d₁ d₂ : Fin n)
    (h₁ : ∀ x ∈ N d₁, G.Adj p₁ x) (h₂ : ∀ x ∈ N d₂, G.Adj p₂ x)
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ y ∈ N d₁) ∨ (x = p₂ ∧ y ∈ N d₂)) :
    ∀ x ∈ P, x ∉ K := by
  classical
  obtain ⟨col⟩ := happ.1.2
  have hdeg2 : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard := fun w =>
    LineGraphDegree.two_le_degree_of_isSubdivision SubdivisionCounting.k4_three_connected
      happ.1.1 w
  -- two distinct neighbours of any vertex
  have htwo : ∀ w : Fin n, ∃ u₁ u₂ : Fin n, H.Adj w u₁ ∧ H.Adj w u₂ ∧ u₁ ≠ u₂ := by
    intro w
    have hnt : (H.neighborSet w).Nontrivial := by
      rw [← Set.one_lt_ncard_iff_nontrivial]
      have := hdeg2 w; omega
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := hnt
    exact ⟨u₁, u₂, hu₁, hu₂, hne⟩
  -- adjacency in `G` between two vertices of `K` is adjacency in `L(H)`
  have hadjK : ∀ a b : H.edgeSet,
      G.Adj (↑(phi a) : V) (↑(phi b) : V) ↔ H.lineGraph.Adj a b := by
    intro a b
    constructor
    · intro h
      exact phi.map_adj_iff.mp h
    · intro h
      exact phi.map_adj_iff.mpr h
  -- a vertex of `K` cannot see every edge of `H` at a vertex `c`
  have hA : ∀ (c : Fin n) (v : V) (hv : v ∈ K), (∀ x ∈ N c, G.Adj v x) → False := by
    intro c v hv hall
    have hphi : (↑(phi (phi.symm ⟨v, hv⟩)) : V) = v := by simp
    have hmemN : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c ∈ e →
        (↑(phi ⟨e, he⟩) : V) ∈ N c := by
      intro e he hce
      rw [hN c]
      exact ⟨e, he, ⟨he, hce⟩, rfl⟩
    by_cases hc : c ∈ ((phi.symm ⟨v, hv⟩ : H.edgeSet) : Sym2 (Fin n))
    · have hvN : v ∈ N c := by
        have := hmemN _ (phi.symm ⟨v, hv⟩).2 hc
        rwa [Subtype.coe_eta, hphi] at this
      exact G.irrefl (hall v hvN)
    · have key : ∀ w : Fin n, H.Adj c w →
          w ∈ ((phi.symm ⟨v, hv⟩ : H.edgeSet) : Sym2 (Fin n)) := by
        intro w hcw
        have hedge : s(c, w) ∈ H.edgeSet := hcw
        have hadj : G.Adj v (↑(phi ⟨s(c, w), hedge⟩) : V) :=
          hall _ (hmemN _ hedge (by simp))
        rw [← hphi] at hadj
        have hl := (hadjK _ _).mp hadj
        rw [← SimpleGraph.mem_neighborSet, LineGraphDegree.mem_lineGraph_neighborSet_iff] at hl
        obtain ⟨-, z, hz1, hz2⟩ := hl
        have : z = c ∨ z = w := by simpa using hz2
        rcases this with rfl | rfl
        · exact absurd hz1 hc
        · exact hz1
      obtain ⟨u₁, u₂, hu₁, hu₂, hne⟩ := htwo c
      have hm : ((phi.symm ⟨v, hv⟩ : H.edgeSet) : Sym2 (Fin n)) = s(u₁, u₂) :=
        (Sym2.mem_and_mem_iff hne).mp ⟨key u₁ hu₁, key u₂ hu₂⟩
      have hadj12 : H.Adj u₁ u₂ := by
        have := (phi.symm ⟨v, hv⟩ : H.edgeSet).2
        rwa [hm] at this
      have c1 : col c ≠ col u₁ := col.valid hu₁
      have c2 : col c ≠ col u₂ := col.valid hu₂
      have c3 : col u₁ ≠ col u₂ := col.valid hadj12
      have : ∀ a b d : Fin 2, a ≠ b → a ≠ d → b ≠ d → False := by decide
      exact this _ _ _ c1 c2 c3
  -- every vertex of `K` has a neighbour in `K`
  have hnbr : ∀ (v : V) (hv : v ∈ K), ∃ y ∈ K, G.Adj v y := by
    intro v hv
    obtain ⟨a, b, hab⟩ := sym2_pair ((phi.symm ⟨v, hv⟩ : H.edgeSet) : Sym2 (Fin n))
    have habE : s(a, b) ∈ H.edgeSet := by
      have := (phi.symm ⟨v, hv⟩ : H.edgeSet).2
      rwa [hab] at this
    obtain ⟨u₁, u₂, hu₁, hu₂, hne⟩ := htwo a
    have hex : ∃ u : Fin n, H.Adj a u ∧ u ≠ b := by
      by_cases h : u₁ = b
      · exact ⟨u₂, hu₂, by rw [← h]; exact hne.symm⟩
      · exact ⟨u₁, hu₁, h⟩
    obtain ⟨u, hu, hub⟩ := hex
    have huE : s(a, u) ∈ H.edgeSet := hu
    have hadj : H.lineGraph.Adj (phi.symm ⟨v, hv⟩) ⟨s(a, u), huE⟩ := by
      rw [← SimpleGraph.mem_neighborSet, LineGraphDegree.mem_lineGraph_neighborSet_iff]
      refine ⟨?_, a, by rw [hab]; simp, by simp⟩
      intro hcon
      have : s(a, u) = s(a, b) := by rw [← hab]; exact congrArg Subtype.val hcon
      exact hub (Sym2.congr_right.mp this)
    have hG := (hadjK _ _).mpr hadj
    rw [show (↑(phi (phi.symm ⟨v, hv⟩)) : V) = v by simp] at hG
    exact ⟨_, (phi ⟨s(a, u), huE⟩).2, hG⟩
  intro x hx hxK
  obtain ⟨y, hyK, hadj⟩ := hnbr x hxK
  rcases hno x hx y hyK hadj with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hA d₁ x hxK h₁
  · exact hA d₂ x hxK h₂


/-- **Outcome 5.8.1 yields an appearance of a `K₄`-enlargement.**

PAPER (9.3, printed p. 48): *"If 5.8.1 holds then there is an appearance in `G` of some
`K₄`-enlargement, a contradiction."*

This is the construction of
`EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath`, minus its
nondegeneracy conclusion, which is unavailable (and unneeded) here because the appearance
`L(H)` carried by a knot with two short antipaths is degenerate.  The paper prints no proof of
the construction anywhere; see the module docstring of `EnlargementFromNonlocalAttachmentPath`.
-/
theorem enlargement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) {n : ℕ}
    (H : SimpleGraph (Fin n)) (K : Set V) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K) (N : Fin n → Set V)
    (hN : ∀ c, N c = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂)
    (d₁ d₂ : Fin n)
    (hnb : ¬ ∃ q, IsBranch H q ∧ d₁ ∈ q ∧ d₂ ∈ q)
    (h₁ : ∀ x ∈ N d₁, G.Adj p₁ x) (h₂ : ∀ x ∈ N d₂, G.Adj p₂ x)
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ y ∈ N d₁) ∨ (x = p₂ ∧ y ∈ N d₂)) :
    ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ Appears G J' := by
  classical
  have hPK := path_disjoint G H K phi happ N hN P p₁ p₂ d₁ d₂ h₁ h₂ hno
  have hc :=
    Workspace.ProofLemmas.EnlargementFromNonlocalStructure.ne_and_not_adj_of_no_common_branch
      (⊤ : SimpleGraph (Fin 4)) SubdivisionCounting.k4_three_connected H happ.1.1 d₁ d₂ hnb
  have h₁' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), d₁ ∈ e →
      G.Adj p₁ (↑(phi ⟨e, he⟩) : V) := by
    intro e he hce
    exact h₁ _ (by rw [hN d₁]; exact ⟨e, he, ⟨he, hce⟩, rfl⟩)
  have h₂' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), d₂ ∈ e →
      G.Adj p₂ (↑(phi ⟨e, he⟩) : V) := by
    intro e he hce
    exact h₂ _ (by rw [hN d₂]; exact ⟨e, he, ⟨he, hce⟩, rfl⟩)
  have hno' : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), d₁ ∈ e ∧
        y = (↑(phi ⟨e, he⟩) : V)) ∨
      (x = p₂ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), d₂ ∈ e ∧
        y = (↑(phi ⟨e, he⟩) : V)) := by
    intro x hx y hy hxy
    rcases hno x hx y hy hxy with h | h
    · refine Or.inl ⟨h.1, ?_⟩
      rw [hN d₁] at h
      obtain ⟨e, he, hinc, hval⟩ := h.2
      exact ⟨e, he, hinc.2, hval⟩
    · refine Or.inr ⟨h.1, ?_⟩
      rw [hN d₂] at h
      obtain ⟨e, he, hinc, hval⟩ := h.2
      exact ⟨e, he, hinc.2, hval⟩
  obtain ⟨D, qq, psi, hext, -⟩ :=
    Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack.addTrack
      G H K phi P p₁ p₂ hP hPK d₁ d₂ hc.1 hc.2 h₁' h₂' hno'
  obtain ⟨m, J', henl, hDsub, -⟩ :=
    Workspace.ProofLemmas.EnlargementFromNonlocalStructure.promotedChordEnlargement
      (⊤ : SimpleGraph (Fin 4)) SubdivisionCounting.k4_three_connected H happ.1.1 d₁ d₂ hnb
      D Sum.inl qq hext
  have hbip : D.IsBipartite :=
    Workspace.ProofLemmas.EnlargementFromNonlocalStructure.branchExtensionBipartite
      G hG (⊤ : SimpleGraph (Fin 4)) SubdivisionCounting.k4_three_connected H happ.1 d₁ d₂ hnb
      D Sum.inl qq hext (K ∪ {x : V | x ∈ P}) psi
  let ee := Fintype.equivFin (Fin n ⊕ Fin (P.length - 1))
  let H' : SimpleGraph (Fin (Fintype.card (Fin n ⊕ Fin (P.length - 1)))) :=
    D.map ee.toEmbedding
  let θ : D ≃g H' := SimpleGraph.Iso.map ee D
  refine ⟨m, J', henl, Fintype.card (Fin n ⊕ Fin (P.length - 1)), H',
    K ∪ {x : V | x ∈ P}, ⟨?_, ?_⟩, ?_⟩
  · exact SubdivisionCounting.isSubdivision_of_iso θ hDsub
  · exact SimpleGraph.Colorable.of_hom θ.symm.toHom hbip
  · exact ⟨θ.lineGraph.symm.trans psi⟩

end Workspace.ProofLemmas.Thm93CaseOneEnlarge
