import Workspace.ProofLemmas.Thm61OddFiniteModel
import Workspace.ProofLemmas.Thm61OddBranchBipartite
import Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance

/-! The enlargement appearance in the complement, at the end of 6.1(7). -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Workspace.ProofLemmas.Thm61OddComplement
open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61OddFiniteModel
open Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance

/-- Paper, 6.1(7): "there is a `J`-enlargement that appears in the complement
of `G`." Relabel the nine old edges by `(r,s) ↦ (r-s,-r-s)`. The complement
is again the line graph of `K₃,₃`, and the antipath adds a branch from `0` to `1`.
Its even length makes the new host bipartite. -/
theorem appears_enlarged
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYout : ∀ y ∈ Y, y ∉ K)
    (Q : List V) (y₁ y₂ : V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hodd : Odd (pathLength Q))
    (a c : Fin 3 → Fin n) (ha : Function.Injective a) (hc : Function.Injective c)
    (hcross : ∀ i j, H.Adj (a i) (c j))
    (hclasses : ∀ i j : Fin 3, s(a i, c j) ∈
      if j = i then extraEdges G H K φ Y y₁
      else if j = i + 1 then extraEdges G H K φ Y y₂
      else completeEdges G H K φ Y) : Appears Gᶜ enlarged := by
  classical
  let oldEdge : (Fin 3 × Fin 3) → H.edgeSet := fun ij =>
    ⟨s(a (oldIndex ij).1, c (oldIndex ij).2), hcross _ _⟩
  let w : (Fin 3 × Fin 3) → V := fun ij => (φ (oldEdge ij) : V)
  have hwinj : Function.Injective w := by
    intro i j hij
    have heq : oldEdge i = oldEdge j := φ.injective (Subtype.ext hij)
    have hval : s(a (oldIndex i).1, c (oldIndex i).2) =
        s(a (oldIndex j).1, c (oldIndex j).2) := congrArg Subtype.val heq
    apply oldIndex_injective
    rcases Sym2.eq_iff.mp hval with ⟨hA, hC⟩ | ⟨hAC, _⟩
    · exact Prod.ext (ha hA) (hc hC)
    · exact False.elim ((hcross _ _).ne hAC)
  have hdisj : ∀ i j : Fin 3 × Fin 3,
      DisjointEdges s(a i.1, c i.2) s(a j.1, c j.2) ↔ i.1 ≠ j.1 ∧ i.2 ≠ j.2 := by
    intro i j
    constructor
    · intro hd
      constructor
      · intro h; exact hd (a i.1) ⟨by simp, by simp [h]⟩
      · intro h; exact hd (c i.2) ⟨by simp, by simp [h]⟩
    · rintro ⟨hA, hC⟩ v ⟨hv, hv'⟩
      rcases Sym2.mem_iff.mp hv with hv | hv <;> rcases Sym2.mem_iff.mp hv' with hv' | hv'
      · exact hA (ha (hv.symm.trans hv'))
      · exact (hcross _ _).ne (hv.symm.trans hv')
      · exact (hcross _ _).ne (hv'.symm.trans hv)
      · exact hC (hc (hv.symm.trans hv'))
  have hrel : ∀ i j : Fin 3 × Fin 3,
      k33.lineGraph.Adj (edgeEquiv i) (edgeEquiv j) ↔ Gᶜ.Adj (w i) (w j) := by
    intro i j
    change k33.lineGraph.Adj (edge i) (edge j) ↔ _
    rw [line_adj, compl_adj_image_iff_disjoint G H K φ (oldEdge i) (oldEdge j)]
    exact (hdisj (oldIndex i) (oldIndex j)).trans (oldIndex_disjoint i j) |>.symm
  let φ₀ := lineGraphIsoInduceOfEdgeIndex Gᶜ k33 edgeEquiv w hwinj hrel
  have hlabel : ∀ ij, (φ₀ (edge ij) : V) = w ij := by
    intro ij
    change w (edgeEquiv.symm (edgeEquiv ij)) = w ij
    rw [Equiv.symm_apply_apply]
  have hQout : ∀ x ∈ Q, x ∈ (Set.range w)ᶜ := by
    intro x hx ⟨ij, heq⟩
    have hxK : x ∈ K := by rw [← heq]; exact (φ (oldEdge ij)).property
    exact hYout x ((hQY x).mp hx) hxK
  have hYrel : ∀ x ∈ Y, ∀ ij : Fin 3 × Fin 3,
      Gᶜ.Adj x (w ij) ↔ (x = y₁ ∧ ij.1 = 0) ∨ (x = y₂ ∧ ij.1 = 1) := by
    intro x hx ij
    have hclass := hclasses (oldIndex ij).1 (oldIndex ij).2
    have hi0 := (oldIndex_class ij).1
    have hi1 := (oldIndex_class ij).2
    by_cases h0 : ij.1 = 0
    · rw [if_pos (hi0.mpr h0)] at hclass
      have h := compl_adj_image_of_extraEdges_iff G H K Y φ (hcross _ _) hclass hx (hYout x hx)
      change Gᶜ.Adj x (φ (oldEdge ij) : V) ↔ _
      rw [h]
      simp [h0]
    · rw [if_neg (fun h => h0 (hi0.mp h))] at hclass
      by_cases h1 : ij.1 = 1
      · rw [if_pos (hi1.mpr h1)] at hclass
        have h := compl_adj_image_of_extraEdges_iff G H K Y φ (hcross _ _) hclass hx (hYout x hx)
        change Gᶜ.Adj x (φ (oldEdge ij) : V) ↔ _
        rw [h]
        simp [h0, h1]
      · rw [if_neg (fun h => h1 (hi1.mp h))] at hclass
        have h := not_compl_adj_image_of_completeEdges G H K Y φ (hcross _ _) hclass hx
        exact iff_of_false h (by simp [h0, h1])
  have hlen : 0 < Q.length := List.length_pos_of_ne_nil hQ.1.1
  have hhead : Q[0]'hlen = y₁ := by
    have h := hQ.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
    exact Option.some.inj h
  have hlast : Q[Q.length - 1]'(by omega) = y₂ := by
    have h := hQ.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hattach : ∀ (i : Fin Q.length) (e : k33.edgeSet),
      Gᶜ.Adj Q[i.val] (φ₀ e : V) ↔
        (i.val = 0 ∧ (0 : Fin 6) ∈ (e : Sym2 (Fin 6))) ∨
        (i.val + 1 = Q.length ∧ (1 : Fin 6) ∈ (e : Sym2 (Fin 6))) := by
    intro i e
    obtain ⟨ij, rfl⟩ := edge_bijective.2 e
    rw [hlabel, hYrel _ ((hQY _).mp (List.getElem_mem i.isLt))]
    have h0 : Q[i.val] = y₁ ↔ i.val = 0 := by
      rw [← hhead]; exact hQ.1.2.1.getElem_inj_iff
    have h1 : Q[i.val] = y₂ ↔ i.val + 1 = Q.length := by
      rw [← hlast, hQ.1.2.1.getElem_inj_iff]
      omega
    change _ ↔ (i.val = 0 ∧ (0 : Fin 6) ∈ edgeVal ij) ∨
      (i.val + 1 = Q.length ∧ (1 : Fin 6) ∈ edgeVal ij)
    rw [zero_incident, one_incident, h0, h1]
  obtain ⟨H', ρ, p, ψ, hext, hplen⟩ := Thm61OddAddBranch.add_branch
    Gᶜ (Set.range w) 6 k33 φ₀ 0 1 (by decide) (by decide) Q y₁ y₂ hQ hQout hattach
  have hsub := Thm61OddBranchSubdivision.subdivision_of_extension k33 0 1
    (by decide) (by decide) H' ρ p hext
  have heven : Even (trackLength p) := by
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hodd
    simp only [pathLength] at hodd
    simp only [trackLength, hplen]
    omega
  have hbip := Thm61OddBranchBipartite.bipartite_of_even_extension k33 0 1 coloring
    (by rfl) (by rfl) H' ρ p hext heven
  exact ⟨_, H', Set.range w ∪ {x | x ∈ Q}, ⟨hsub, hbip⟩, ⟨ψ⟩⟩

end Workspace.ProofLemmas.Thm61OddComplement
