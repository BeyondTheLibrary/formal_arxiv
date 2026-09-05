import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75BranchEnds

/-!
# 7.5: a `Bc₁c₂`-dominant vertex lies outside `L(H)`

The printed proof of 7.5 uses this silently.  It is needed twice: to know that `Y` is disjoint
from `V(L(H))` — so that `S` and `T` really are disjoint from the cutset `X₀ ∪ X₁ ∪ Y` — and in
the sentence *"Suppose some vertex in `v ∈ F` is major with respect to `L(H)`.  Then since
`v ∉ X` it follows that `v` has a nonneighbour in `Y`"*, where the paper freely treats `Y` as
living outside the line graph.

The reason is degree together with bipartiteness.  A vertex `y` of `L(H)` is an edge `e₀` of `H`.
Since `c₁` and `c₂` are nonadjacent branch-vertices (`Thm75BranchEnds`), at least one of them —
say `c` — is not an end of `e₀`.  Now `c` has `≥ 3` neighbours in `H`, and at most one of them
lies on `e₀`: two would give a triangle of `H`, and `H` is bipartite.  So `≥ 2` edges of
`δ_H(c)` are disjoint from `e₀`, i.e. `y` has `≥ 2` non-neighbours in `N_c`, and `y` is not
dominant.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75DominantOutsideLineGraph

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- No vertex of `L(H)` is `Bc₁c₂`-dominant, when `Bc₁c₂` is a branch of odd length `≥ 3` with
ends `c₁, c₂` and `J` is 3-connected. -/
theorem thm75DominantOutsideLineGraph {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hlen : 3 ≤ trackLength B)
    (y : V) (hy : IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) :
    y ∉ K := by
  classical
  intro hyK
  obtain ⟨hne, hc₁b, hc₂b, hnadj⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H happ.1.1 B c₁ c₂ hbranch hfrom
      (by omega)
  obtain ⟨col⟩ := happ.1.2
  -- the edge of `H` that the vertex `y` of `L(H)` is
  set e₀ : H.edgeSet := φ.symm ⟨y, hyK⟩ with he₀
  have hy₀ : (↑(φ e₀) : V) = y := by rw [he₀, RelIso.apply_symm_apply]
  -- adjacency across the appearance
  have hdict : ∀ f : H.edgeSet, G.Adj y (↑(φ f) : V) ↔ H.lineGraph.Adj e₀ f := by
    intro f
    rw [← hy₀]
    exact φ.map_adj_iff
  -- the counting step, applied to whichever of `c₁, c₂` is not an end of `e₀`
  have key : ∀ c : W, c ∈ branchVertices H → c ∉ (↑e₀ : Sym2 W) →
      ¬ (NSet G H K φ c \ G.neighborSet y).Subsingleton := by
    intro c hcb hce hsubs
    -- at most one neighbour of `c` lies on `e₀`, else `H` has a triangle
    have hbad : {w : W | w ∈ H.neighborSet c ∧ w ∈ (↑e₀ : Sym2 W)}.Subsingleton := by
      rintro w₁ ⟨hw₁n, hw₁e⟩ w₂ ⟨hw₂n, hw₂e⟩
      by_contra hw
      have hedge : (↑e₀ : Sym2 W) = s(w₁, w₂) := (Sym2.mem_and_mem_iff hw).mp ⟨hw₁e, hw₂e⟩
      have hw₁w₂ : H.Adj w₁ w₂ := by
        have : (↑e₀ : Sym2 W) ∈ H.edgeSet := e₀.2
        rw [hedge] at this
        exact this
      have h1 : col c ≠ col w₁ := col.valid hw₁n
      have h2 : col c ≠ col w₂ := col.valid hw₂n
      have h3 : col w₁ ≠ col w₂ := col.valid hw₁w₂
      have b1 : ((col c : Fin 2) : ℕ) < 2 := (col c).isLt
      have b2 : ((col w₁ : Fin 2) : ℕ) < 2 := (col w₁).isLt
      have b3 : ((col w₂ : Fin 2) : ℕ) < 2 := (col w₂).isLt
      have n1 : ((col c : Fin 2) : ℕ) ≠ ((col w₁ : Fin 2) : ℕ) := fun h => h1 (Fin.ext h)
      have n2 : ((col c : Fin 2) : ℕ) ≠ ((col w₂ : Fin 2) : ℕ) := fun h => h2 (Fin.ext h)
      have n3 : ((col w₁ : Fin 2) : ℕ) ≠ ((col w₂ : Fin 2) : ℕ) := fun h => h3 (Fin.ext h)
      omega
    -- hence `c` has two neighbours off `e₀`
    have hnontriv : (H.neighborSet c \ {w : W | w ∈ (↑e₀ : Sym2 W)}).Nontrivial := by
      by_contra hcon
      rw [Set.not_nontrivial_iff] at hcon
      have hcover : H.neighborSet c ⊆
          {w : W | w ∈ H.neighborSet c ∧ w ∈ (↑e₀ : Sym2 W)} ∪
            (H.neighborSet c \ {w : W | w ∈ (↑e₀ : Sym2 W)}) := by
        intro w hw
        by_cases hwe : w ∈ (↑e₀ : Sym2 W)
        · exact Or.inl ⟨hw, hwe⟩
        · exact Or.inr ⟨hw, hwe⟩
      have hle1 : {w : W | w ∈ H.neighborSet c ∧ w ∈ (↑e₀ : Sym2 W)}.ncard ≤ 1 := by
        rcases hbad.eq_empty_or_singleton with h | ⟨a, h⟩ <;> rw [h] <;> simp
      have hle2 : (H.neighborSet c \ {w : W | w ∈ (↑e₀ : Sym2 W)}).ncard ≤ 1 := by
        rcases hcon.eq_empty_or_singleton with h | ⟨a, h⟩ <;> rw [h] <;> simp
      have := Set.ncard_le_ncard hcover (Set.toFinite _)
      have hun := Set.ncard_union_le
        {w : W | w ∈ H.neighborSet c ∧ w ∈ (↑e₀ : Sym2 W)}
        (H.neighborSet c \ {w : W | w ∈ (↑e₀ : Sym2 W)})
      have hcb' : 3 ≤ (H.neighborSet c).ncard := hcb
      omega
    obtain ⟨w₁, ⟨hw₁n, hw₁e⟩, w₂, ⟨hw₂n, hw₂e⟩, hw₁₂⟩ := hnontriv
    -- the two corresponding edges of `δ_H(c)`
    have hf₁ : s(c, w₁) ∈ H.edgeSet := hw₁n
    have hf₂ : s(c, w₂) ∈ H.edgeSet := hw₂n
    have hmemN : ∀ (w : W) (hw : s(c, w) ∈ H.edgeSet),
        (↑(φ ⟨s(c, w), hw⟩) : V) ∈ NSet G H K φ c :=
      fun w hw => ⟨s(c, w), hw, ⟨hw, by simp⟩, rfl⟩
    have hnotadj : ∀ (w : W) (hw : s(c, w) ∈ H.edgeSet), w ∉ (↑e₀ : Sym2 W) →
        (↑(φ ⟨s(c, w), hw⟩) : V) ∉ G.neighborSet y := by
      intro w hw hwe hcon
      have := (hdict ⟨s(c, w), hw⟩).mp hcon
      rw [SimpleGraph.lineGraph_adj_iff_exists] at this
      obtain ⟨-, z, hz₁, hz₂⟩ := this
      rcases Sym2.mem_iff.mp hz₂ with rfl | rfl
      · exact hce hz₁
      · exact hwe hz₁
    have heq := hsubs ⟨hmemN w₁ hf₁, hnotadj w₁ hf₁ hw₁e⟩
      ⟨hmemN w₂ hf₂, hnotadj w₂ hf₂ hw₂e⟩
    -- `φ` is injective, so the two vertices are distinct
    apply hw₁₂
    have : (⟨s(c, w₁), hf₁⟩ : H.edgeSet) = ⟨s(c, w₂), hf₂⟩ := by
      apply φ.injective
      exact Subtype.ext heq
    have h' : s(c, w₁) = s(c, w₂) := congrArg Subtype.val this
    exact (Sym2.congr_right).mp h'
  -- at least one of `c₁, c₂` is not an end of `e₀`
  by_cases h₁ : c₁ ∈ (↑e₀ : Sym2 W)
  · have h₂ : c₂ ∉ (↑e₀ : Sym2 W) := by
      intro h₂
      have hedge : (↑e₀ : Sym2 W) = s(c₁, c₂) := (Sym2.mem_and_mem_iff hne).mp ⟨h₁, h₂⟩
      have : (↑e₀ : Sym2 W) ∈ H.edgeSet := e₀.2
      rw [hedge] at this
      exact hnadj this
    exact key c₂ hc₂b h₂ hy.2
  · exact key c₁ hc₁b h₁ hy.1

end Workspace.ProofLemmas.Thm75DominantOutsideLineGraph
