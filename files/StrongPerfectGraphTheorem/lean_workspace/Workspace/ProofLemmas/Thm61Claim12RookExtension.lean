import Workspace.ProofLemmas.L33SelfComplementary
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Claim12RookTheta
import Workspace.ProofLemmas.Thm61Claim12RookBranch
import Workspace.ProofLemmas.Thm61Claim12RookIso
import Workspace.ProofLemmas.Thm61OddBranchSubdivision
import Workspace.ProofLemmas.Thm61Claim1Helpers
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm85Five8Transported

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm61Claim12RookExtension

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.L33SelfComplementary
open Workspace.ProofLemmas.Thm61Claim12RookTheta
open Workspace.ProofLemmas.Thm61Claim12RookIso
open Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance

/-- **Remaining gap: the edge replacement in the short case of 6.1(12).**

PAPER: "if `B` has length 1 then the second outcome of the theorem holds" (printed p. 33).

The nine vertices are the cells of `L(K₃,₃)`. In the complement, the shear
`(i,j) ↦ (i+j,i+2j)` again gives `L(K₃,₃)`. Remove the vertex `w (2,2)` and replace its
edge by the path `Q`. The two pairs in `hattach` are exactly the remaining edges at its two
ends. The new branch has `Q.length` edges, which is odd and at least three. The omitted
vertex `w (2,2)` is adjacent to the other two edges at each end and witnesses overshadowing.

Only this explicit line-graph edge replacement remains open. No conclusion of 6.1 or
minimal-counterexample hypothesis is assumed here. -/
theorem rook_path_replacement
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : Fin 3 × Fin 3 → V) (hwinj : Function.Injective w)
    (hrel : ∀ i j, G.Adj (w i) (w j) ↔ rook33.Adj i j)
    (Q : List V) (y₁ y₂ : V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hy : y₁ ≠ y₂) (hQeven : Even (pathLength Q))
    (hQout : ∀ x ∈ Q, x ∉ Set.range w)
    (hattach : ∀ x ∈ Q, ∀ i : Fin 3 × Fin 3, i ≠ (2, 2) →
      (Gᶜ.Adj x (w i) ↔
        (x = y₁ ∧ (i = (0, 0) ∨ i = (1, 1))) ∨
        (x = y₂ ∧ (i = (0, 1) ∨ i = (1, 0))))) :
    ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
        (φ' : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (completeBipartiteGraph (Fin 3) (Fin 3)) H' K' ∧
        IsOvershadowedAppearance Gᶜ H' K' φ' := by
  classical
  ---------------------------------------------------------------------------
  -- 1.  The eight cells other than `(2,2)` carry `L(rookTheta)` in `Gᶜ`.
  ---------------------------------------------------------------------------
  have hcompl : ∀ i j, Gᶜ.Adj (w i) (w j) ↔ rook33ᶜ.Adj i j := by
    intro i j
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj, hrel]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h]), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (hwinj h), h2⟩
  set w8 : Fin 8 → V := fun k => w (rookCell k) with hw8def
  have hw8k : ∀ k : Fin 8, w8 k = w (rookCell k) := fun _ => rfl
  have hw8inj : Function.Injective w8 := by
    intro k l h
    exact rookCell_injective (hwinj h)
  have hrel8 : ∀ k l : Fin 8,
      rookTheta.lineGraph.Adj (rookEdge k) (rookEdge l) ↔ Gᶜ.Adj (w8 k) (w8 l) := by
    intro k l
    rw [rookEdge_lineGraph_adj, hw8k, hw8k, hcompl]
  set K₀ : Set V := Set.range w8 with hK₀def
  set φ₀ : rookTheta.lineGraph ≃g Gᶜ.induce K₀ :=
    lineGraphIsoInduceOfEdgeIndex Gᶜ rookTheta rookEdgeEquiv w8 hw8inj hrel8 with hφ₀def
  have hφ₀ : ∀ k : Fin 8, (↑(φ₀ (rookEdge k)) : V) = w8 k := by
    intro k
    rw [hφ₀def]
    exact apply_edge Gᶜ rookTheta rookEdgeEquiv w8 hw8inj hrel8 k
  ---------------------------------------------------------------------------
  -- 2.  The attachments of `Q`, transported to the eight indices.
  ---------------------------------------------------------------------------
  have hy₁Q : y₁ ∈ Q := List.mem_of_mem_head? hQ.2.1
  have hy₂Q : y₂ ∈ Q := List.mem_of_mem_getLast? hQ.2.2
  have hcell : ∀ k : Fin 8,
      ((rookCell k = ((0 : Fin 3), (0 : Fin 3)) ∨ rookCell k = (1, 1)) ↔ (k = 0 ∨ k = 4)) ∧
      ((rookCell k = ((0 : Fin 3), (1 : Fin 3)) ∨ rookCell k = (1, 0)) ↔ (k = 1 ∨ k = 3)) := by
    decide
  have hatt : ∀ x ∈ Q, ∀ k : Fin 8, (Gᶜ.Adj x (w8 k) ↔
      (x = y₁ ∧ (k = 0 ∨ k = 4)) ∨ (x = y₂ ∧ (k = 1 ∨ k = 3))) := by
    intro x hx k
    have h := hattach x hx (rookCell k) (rookCell_ne_two_two k)
    rw [hw8k, h, (hcell k).1, (hcell k).2]
  have hy₁0 : Gᶜ.Adj y₁ (w8 0) := (hatt y₁ hy₁Q 0).2 (Or.inl ⟨rfl, Or.inl rfl⟩)
  have hy₁4 : Gᶜ.Adj y₁ (w8 4) := (hatt y₁ hy₁Q 4).2 (Or.inl ⟨rfl, Or.inr rfl⟩)
  have hy₂1 : Gᶜ.Adj y₂ (w8 1) := (hatt y₂ hy₂Q 1).2 (Or.inr ⟨rfl, Or.inl rfl⟩)
  have hy₂3 : Gᶜ.Adj y₂ (w8 3) := (hatt y₂ hy₂Q 3).2 (Or.inr ⟨rfl, Or.inr rfl⟩)
  have h04 : Gᶜ.Adj (w8 0) (w8 4) := by
    rw [hw8k, hw8k, hcompl]
    decide
  have h13 : Gᶜ.Adj (w8 1) (w8 3) := by
    rw [hw8k, hw8k, hcompl]
    decide
  have hQK : ∀ x ∈ Q, x ∈ K₀ᶜ := by
    intro x hx hmem
    obtain ⟨k, hk⟩ := hmem
    exact hQout x hx ⟨rookCell k, by rw [← hk, hw8k]⟩
  have hother : ∀ x ∈ Q, ∀ k ∈ K₀, Gᶜ.Adj x k →
      (x = y₁ ∧ (k = w8 0 ∨ k = w8 4)) ∨ (x = y₂ ∧ (k = w8 1 ∨ k = w8 3)) := by
    intro x hx k hk hxk
    obtain ⟨j, rfl⟩ := hk
    rcases (hatt x hx j).1 hxk with ⟨hxy, hj | hj⟩ | ⟨hxy, hj | hj⟩ <;> subst hj
    · exact Or.inl ⟨hxy, Or.inl rfl⟩
    · exact Or.inl ⟨hxy, Or.inr rfl⟩
    · exact Or.inr ⟨hxy, Or.inl rfl⟩
    · exact Or.inr ⟨hxy, Or.inr rfl⟩
  have hzinc : ∀ e : rookTheta.edgeSet,
      (3 : Fin 6) ∈ (e : Sym2 (Fin 6)) ↔
        ((↑(φ₀ e) : V) = w8 0 ∨ (↑(φ₀ e) : V) = w8 4) := by
    intro e
    obtain ⟨k, rfl⟩ := rookEdge_bijective.2 e
    rw [hφ₀ k, rookEdge_mem_three k]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (hw8inj h)
      · exact Or.inr (hw8inj h)
  have hz'inc : ∀ e : rookTheta.edgeSet,
      (1 : Fin 6) ∈ (e : Sym2 (Fin 6)) ↔
        ((↑(φ₀ e) : V) = w8 1 ∨ (↑(φ₀ e) : V) = w8 3) := by
    intro e
    obtain ⟨k, rfl⟩ := rookEdge_bijective.2 e
    rw [hφ₀ k, rookEdge_mem_one k]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (hw8inj h)
      · exact Or.inr (hw8inj h)
  ---------------------------------------------------------------------------
  -- 3.  Attach `Q` as a new branch from the column end `3` to the row end `1`.
  ---------------------------------------------------------------------------
  obtain ⟨H, ρ, p, -, hext, hplen⟩ :=
    Workspace.ProofLemmas.Thm101ThetaAddBranch Gᶜ K₀ 6 rookTheta φ₀ 3 1
      (by decide) rookTheta_not_adj
      Q y₁ y₂ (w8 0) (w8 4) (w8 1) (w8 3) hQ hQK
      ⟨0, rfl⟩ ⟨4, rfl⟩ ⟨1, rfl⟩ ⟨3, rfl⟩ h04 h13
      hy₁0 hy₁4 hy₂1 hy₂3 hother hzinc hz'inc
  obtain ⟨ψ, hold, hnew⟩ :=
    Workspace.ProofLemmas.thetaBranchExtensionLabelledIso Gᶜ K₀ 6 rookTheta φ₀ 3 1
      rookTheta_not_adj Q y₁ y₂ (w8 0) (w8 4) (w8 1) (w8 3) hQ hQK
      hy₁0 hy₁4 hy₂1 hy₂3 hother hzinc hz'inc
      (6 + (Q.length - 1)) H ρ p hext hplen
  obtain ⟨hρ, hhom, hpfrom, hp2, hpint, hpcover, hpedges⟩ := hext
  have hext' : Workspace.ProofLemmas.ThetaData.IsThetaBranchExtension rookTheta 3 1 H ρ p :=
    ⟨hρ, hhom, hpfrom, hp2, hpint, hpcover, hpedges⟩
  ---------------------------------------------------------------------------
  -- 4.  Lengths and parity: the new branch is odd and has at least three edges.
  ---------------------------------------------------------------------------
  have hQlen2 : 2 ≤ Q.length := by
    have hpos : 0 < Q.length := List.length_pos_of_ne_nil hQ.1.1
    by_contra hnot
    have hlen : Q.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hh := hQ.2.1
    have hl := hQ.2.2
    simp only [List.head?_cons, List.getLast?_singleton] at hh hl
    exact hy ((Option.some.inj hh).symm.trans (Option.some.inj hl))
  have hQmod : Q.length % 2 = 1 := by
    rw [Nat.even_iff] at hQeven
    simp only [pathLength] at hQeven
    omega
  have hQlen3 : 3 ≤ Q.length := by omega
  have hpLength : trackLength p = Q.length := by
    simp only [trackLength]
    omega
  have hpOdd : Odd (trackLength p) := by
    rw [Nat.odd_iff, hpLength]
    exact hQmod
  have hpLong : 3 ≤ trackLength p := by rw [hpLength]; exact hQlen3
  have hp3 : 3 ≤ p.length := by omega
  ---------------------------------------------------------------------------
  -- 5.  The new track is a branch of `H`, and `H` is a bipartite subdivision of `K₃,₃`.
  ---------------------------------------------------------------------------
  have hb3 : ρ 3 ∈ branchVertices H :=
    Thm61Claim12RookBranch.end_mem_branchVertices hext' hp3
      (show (0 : Fin 6) ≠ 2 by decide) rookTheta_adj_three_zero rookTheta_adj_three_two
  have hb1 : ρ 1 ∈ branchVertices H :=
    Thm61Claim12RookBranch.end_mem_branchVertices
      (Thm61Claim12RookBranch.reverse_extension hext') (by simpa using hp3)
      (show (4 : Fin 6) ≠ 5 by decide) rookTheta_adj_one_four rookTheta_adj_one_five
  have hpNotBranch : ∀ v ∈ trackInterior p, v ∉ branchVertices H :=
    Thm61Claim12RookBranch.interior_not_branchVertex hext'
  have hpBranch : IsBranch H p :=
    Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch hpfrom
      (fun h => (show (3 : Fin 6) ≠ 1 by decide) (hρ h)) hpNotBranch hb3 hb1
  have hbip : H.IsBipartite :=
    Thm61Claim12RookBranch.bipartite_of_odd_extension rookColoring rookColoring_three
      rookColoring_one hext' hpOdd
  have hsubd0 : IsSubdivision (rookTheta ⊔ SimpleGraph.edge (3 : Fin 6) 1) H :=
    Workspace.ProofLemmas.Thm61OddBranchSubdivision.subdivision_of_extension rookTheta 3 1
      (by decide) rookTheta_not_adj H ρ p hext'
  rw [rookTheta_sup_edge] at hsubd0
  obtain ⟨σ⟩ := k33Six_iso
  have happ : IsAppearance Gᶜ (completeBipartiteGraph (Fin 3) (Fin 3)) H
      (K₀ ∪ {x : V | x ∈ Q}) :=
    ⟨⟨Workspace.ProofLemmas.Thm85Five8Transported.isSubdivision_of_iso σ hsubd0, hbip⟩, ⟨ψ⟩⟩
  ---------------------------------------------------------------------------
  -- 6.  The omitted cell `(2,2)` overshadows the new branch.
  ---------------------------------------------------------------------------
  set a : V := w (2, 2) with hadef
  have ha : ∀ k : Fin 8, k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 4 → Gᶜ.Adj a (w8 k) := by
    intro k hk
    rw [hadef, hw8k, hcompl]
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  have exception : ∀ (c : Fin 6) (k l : Fin 8),
      (∀ e : rookTheta.edgeSet, c ∈ (e : Sym2 (Fin 6)) → e = rookEdge k ∨ e = rookEdge l) →
      Gᶜ.Adj a (w8 k) → Gᶜ.Adj a (w8 l) →
      ∀ e : Sym2 (Fin (6 + (Q.length - 1))),
        e ∈ incidentEdges H (ρ c) \
            {e : Sym2 (Fin (6 + (Q.length - 1))) |
              ∃ he : e ∈ H.edgeSet, Gᶜ.Adj a (↑(ψ ⟨e, he⟩) : V)} →
        e ∈ trackEdges p := by
    intro c k l hstar hak hal e he
    have heEdge := he.1.1
    rw [hpedges] at heEdge
    rcases heEdge with ⟨e₀, he₀, hemapEq⟩ | hep
    · exfalso
      have hmem : c ∈ e₀ := by
        have hinc : ρ c ∈ Sym2.map ρ e₀ := by rw [hemapEq]; exact he.1.2
        obtain ⟨d, hd, hdρ⟩ := Sym2.mem_map.mp hinc
        have : d = c := hρ hdρ
        rwa [this] at hd
      have heMap : Sym2.map ρ e₀ ∈ H.edgeSet := by rw [hemapEq]; exact he.1.1
      have hedgeEq :
          (⟨Sym2.map ρ ((⟨e₀, he₀⟩ : rookTheta.edgeSet) : Sym2 (Fin 6)), heMap⟩ :
            H.edgeSet) = ⟨e, he.1.1⟩ := Subtype.ext hemapEq
      apply he.2
      refine ⟨he.1.1, ?_⟩
      rcases hstar ⟨e₀, he₀⟩ hmem with hidx | hidx
      · have hlab : (↑(ψ ⟨e, he.1.1⟩) : V) = w8 k := by
          rw [← hedgeEq, hold ⟨e₀, he₀⟩ heMap, hidx, hφ₀ k]
        rw [hlab]
        exact hak
      · have hlab : (↑(ψ ⟨e, he.1.1⟩) : V) = w8 l := by
          rw [← hedgeEq, hold ⟨e₀, he₀⟩ heMap, hidx, hφ₀ l]
        rw [hlab]
        exact hal
    · exact hep
  refine ⟨6 + (Q.length - 1), H, K₀ ∪ {x : V | x ∈ Q}, ψ, happ, ?_⟩
  refine ⟨p, ρ 3, ρ 1, hpBranch, hpfrom, hpOdd, hpLong, a, ?_, ?_⟩
  · intro e he f hf
    have h1 := Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdge_at_head hpfrom hp2
      (exception 3 0 4 edge_incident_three (ha 0 (by decide)) (ha 4 (by decide)) e he) he.1.2
    have h2 := Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdge_at_head hpfrom hp2
      (exception 3 0 4 edge_incident_three (ha 0 (by decide)) (ha 4 (by decide)) f hf) hf.1.2
    exact h1.trans h2.symm
  · intro e he f hf
    have h1 := Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdge_at_last hpfrom hp2
      (exception 1 1 3 edge_incident_one (ha 1 (by decide)) (ha 3 (by decide)) e he) he.1.2
    have h2 := Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdge_at_last hpfrom hp2
      (exception 1 1 3 edge_incident_one (ha 1 (by decide)) (ha 3 (by decide)) f hf) hf.1.2
    exact h1.trans h2.symm

end Workspace.ProofLemmas.Thm61Claim12RookExtension
