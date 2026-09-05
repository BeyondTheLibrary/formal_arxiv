import Workspace.ProofLemmas.Thm192Claim6Basics

/-! The long prism at the end of the first case of claim (7) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim7GapPrism

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem cross_pair {G : SimpleGraph V} {W : Set V} {Q : List V}
    {r s y u : V} (hQ : IsAntipathFrom G Q y u)
    (hQI : ∀ v ∈ SPGT.interior Q, v ∈ W)
    (hrW : VertexComplete G r W) (hsW : VertexComplete G s W)
    (hry : Gᶜ.Adj r y) (hsu : Gᶜ.Adj s u)
    (hru : G.Adj r u) (hsy : G.Adj s y) (hrs : r ≠ s) :
    ∀ t ∈ [r, s], ∀ v ∈ Q,
      (Gᶜ.Adj t v ↔ (t = r ∧ v = y) ∨ (t = s ∧ v = u)) := by
  intro t ht v hv
  have ht' : t = r ∨ t = s := by simpa using ht
  rcases ht' with ht | ht
  · subst t
    constructor
    · intro hadj
      by_cases hvy : v = y
      · exact Or.inl ⟨rfl, hvy⟩
      by_cases hvu : v = u
      · rw [hvu] at hadj
        exact (((SimpleGraph.compl_adj G r u).mp hadj).2 hru).elim
      · have hI := (PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hv, hvy, hvu⟩
        exact (((SimpleGraph.compl_adj G r v).mp hadj).2 (hrW v (hQI v hI))).elim
    · rintro (⟨_, hvy⟩ | ⟨heq, _⟩)
      · rw [hvy]; exact hry
      · exact (hrs heq).elim
  · subst t
    constructor
    · intro hadj
      by_cases hvu : v = u
      · exact Or.inr ⟨rfl, hvu⟩
      by_cases hvy : v = y
      · rw [hvy] at hadj
        exact (((SimpleGraph.compl_adj G s y).mp hadj).2 hsy).elim
      · have hI := (PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hv, hvy, hvu⟩
        exact (((SimpleGraph.compl_adj G s v).mp hadj).2 (hsW v (hQI v hI))).elim
    · rintro (⟨heq, _⟩ | ⟨_, hvu⟩)
      · exact (hrs heq.symm).elim
      · rw [hvu]; exact hsu

/-- PAPER (claim (7)): "the three antipaths `p₁-x₁`, `pₙ-x₀` and `y-Q-x₂`
form a long prism in [the complement] with triangles `{p₁,pₙ,y}` and
`{x₁,x₀,x₂}`, a contradiction." -/
theorem prism_absurd {G : SimpleGraph V} (hG : InF7 G) {W : Set V}
    {p q a b y u : V} {Q : List V}
    (hQ : IsAntipathFrom G Q y u) (hQI : ∀ v ∈ SPGT.interior Q, v ∈ W)
    (hpW : VertexComplete G p W) (hqW : VertexComplete G q W)
    (haW : VertexComplete G a W) (hbW : VertexComplete G b W)
    (hpq : Gᶜ.Adj p q) (hpy : Gᶜ.Adj p y) (hqy : Gᶜ.Adj q y)
    (hba : Gᶜ.Adj b a) (hbu : Gᶜ.Adj b u) (hau : Gᶜ.Adj a u)
    (hpb : Gᶜ.Adj p b) (hqa : Gᶜ.Adj q a)
    (hpa : G.Adj p a) (hpu : G.Adj p u) (hqb : G.Adj q b) (hqu : G.Adj q u)
    (hby : G.Adj b y) (hay : G.Adj a y) (hyu : G.Adj y u) : False := by
  have hcross : ∀ r ∈ [p, b], ∀ s ∈ [q, a],
      (Gᶜ.Adj r s ↔ (r = p ∧ s = q) ∨ (r = b ∧ s = a)) := by
    intro r hr s hs
    have hr' : r = p ∨ r = b := by simpa using hr
    have hs' : s = q ∨ s = a := by simpa using hs
    rcases hr' with hr | hr <;> rcases hs' with hs | hs
    · rw [hr, hs]
      simp [hpq]
    · rw [hr, hs]
      simp [SimpleGraph.compl_adj, hpa, hpb.ne, hqa.ne.symm]
    · rw [hr, hs]
      simp [SimpleGraph.compl_adj, hqb.symm, hpb.ne.symm, hqa.ne]
    · rw [hr, hs]
      simp [hba]
  apply hG.1.1.2.2
  apply PrismBasics.formPrism_mk hpq hpy hqy hba hbu hau
    hpb.ne hpa.ne hpu.ne hqb.ne hqa.ne hqu.ne hby.ne.symm hay.ne.symm hyu.ne
    (show IsPathFrom Gᶜ [p, b] p b from ⟨PathBasics.isPathList_pair hpb, rfl, rfl⟩)
    (show IsPathFrom Gᶜ [q, a] q a from ⟨PathBasics.isPathList_pair hqa, rfl, rfl⟩)
    hQ hcross (cross_pair hQ hQI hpW hbW hpy hbu hpu hby hpb.ne)
    (cross_pair hQ hQI hqW haW hqy hau hqu hay hqa.ne)
  right; right
  have hlen := AntiholeCompletion.three_le_length_of_antipath hQ hyu
  simp only [pathLength]
  omega

end Workspace.ProofLemmas.Thm192Claim7GapPrism
