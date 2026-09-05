import Workspace.ProofLemmas.Thm175Claim2Basics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim2Antipath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm175Claim2Basics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Completing `X \ {x}` but not `X` means missing `x`. -/
theorem misses_deleted (G : SimpleGraph V) (X : Set V) (u x : V)
    (hc : VertexComplete G u (X \ {x})) (hn : ¬ VertexComplete G u X) :
    ¬ G.Adj u x := by
  intro hux
  apply hn
  intro w hw
  by_cases he : w = x
  · simpa [he] using hux
  · exact hc w ⟨hw, he⟩

/-- PAPER: "Since `pᵢ-x₁-Q-x₂-pⱼ-pᵢ` is an antihole it follows that
`Q` is odd." For adjacent `pᵢ,pⱼ`, the extra vertex `z` instead makes
`z-pᵢ-x₁-Q-x₂-pⱼ-z` an antihole, forcing the opposite parity. -/
theorem cross_pair_parity (G : SimpleGraph V) (hG : Berge G)
    (X : Set V) (x₁ x₂ : V) (hne : x₁ ≠ x₂)
    (Q : List V) (hQ : IsAntipathFrom G Q x₁ x₂) (hQX : ∀ w ∈ Q, w ∈ X)
    (u v z : V) (hu : u ∉ X) (hv : v ∉ X) (huv : u ≠ v)
    (huc : VertexComplete G u (X \ {x₁}))
    (hvc : VertexComplete G v (X \ {x₂}))
    (humiss : ¬ G.Adj u x₁) (hvmiss : ¬ G.Adj v x₂)
    (hzX : VertexComplete G z X) (hzu : ¬ G.Adj z u) (hzv : ¬ G.Adj z v)
    (hznu : z ≠ u) (hznv : z ≠ v) :
    (¬ G.Adj u v → Odd (pathLength Q)) ∧
    (G.Adj u v → Even (pathLength Q)) := by
  have hx₁X := hQX x₁ (PathBasics.head_mem hQ.2.1)
  have hx₂X := hQX x₂ (PathBasics.getLast_mem hQ.2.2)
  have huQ : u ∉ Q := fun h => hu (hQX u h)
  have hvQ : v ∉ Q := fun h => hv (hQX v h)
  have hux : Gᶜ.Adj u x₁ :=
    ⟨fun he => hu (he ▸ hx₁X), humiss⟩
  have hvx : Gᶜ.Adj v x₂ :=
    ⟨fun he => hv (he ▸ hx₂X), hvmiss⟩
  have huother : ∀ w ∈ Q, w ≠ x₁ → ¬ Gᶜ.Adj u w := by
    intro w hw hn hc
    exact hc.2 (huc w ⟨hQX w hw, hn⟩)
  have hvother : ∀ w ∈ Q, w ≠ x₂ → ¬ Gᶜ.Adj v w := by
    intro w hw hn hc
    exact hc.2 (hvc w ⟨hQX w hw, hn⟩)
  have hQlen : 1 ≤ pathLength Q := by
    have hpos := PathBasics.path_length_pos hQ.1
    by_contra hn
    have hlen : Q.length = 1 := by simp only [pathLength] at hn; omega
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen
    have h1 : w = x₁ := by simpa using hQ.2.1
    have h2 : w = x₂ := by simpa using hQ.2.2
    exact hne (h1.symm.trans h2)
  constructor
  · intro hnuv
    have hhole := PrismBasics.isHoleList_of_path_add_two_vertices hQ hQlen
      hux hvx (show Gᶜ.Adj u v from ⟨huv, hnuv⟩) huQ hvQ
      (huother x₂ (PathBasics.getLast_mem hQ.2.2) hne.symm)
      (hvother x₁ (PathBasics.head_mem hQ.2.1) hne)
      (fun w hw => huother w (PathBasics.interior_subset hw)
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mp hw).2.1)
      (fun w hw => hvother w (PathBasics.interior_subset hw)
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mp hw).2.2)
    have he := hG.2 _ hhole
    rw [PrismBasics.holeLength_cons_cons u v hQ.1.1, Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · intro huvAdj
    have hpath := PathAttach.isPathFrom_cons_concat hQ hux hvx
      (fun h => h.2 huvAdj) huv huQ hvQ huother hvother
    have hzQ : z ∉ Q := fun h => G.irrefl (hzX z (hQX z h))
    have hzout : z ∉ u :: (Q ++ [v]) := by
      simp [hznu, hzQ, hznv]
    have hlen : pathLength (u :: (Q ++ [v])) = pathLength Q + 2 := by
      have hpos := PathBasics.path_length_pos hQ.1
      simp only [pathLength, List.length_cons, List.length_append, List.length_nil]
      omega
    have hhole := PrismBasics.isHoleList_of_path_add_vertex hpath (by omega)
      (show Gᶜ.Adj z u from ⟨hznu, hzu⟩)
      (show Gᶜ.Adj z v from ⟨hznv, hzv⟩) hzout (by
        intro w hw hc
        have hwQ : w ∈ Q := by simpa [SPGT.interior] using hw
        exact hc.2 (hzX w (hQX w hwQ)))
    have he := hG.2 _ hhole
    rw [PrismBasics.holeLength_cons z hpath.1.1, hlen, Nat.even_iff] at he
    rw [Nat.even_iff]
    omega

end Workspace.ProofLemmas.Thm175Claim2Antipath
