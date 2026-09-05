import Workspace.ProofLemmas.Thm61Claim12DegreeThree
import Workspace.ProofLemmas.Thm61Claim12VEq
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61EvenClaims
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61EvenEndgameClaim12
import Workspace.ProofLemmas.Thm61EvenFinalClaim13
import Workspace.ProofLemmas.Thm61EvenFinalClosing

/-!
# The remaining terminal steps of the even endgame of 6.1

The helper modules prove the common skeleton of claim (12) and its degree-two case.  This file
isolates the two other terminal cases and the two printed blocks after claim (12).  Each open
lemma below is one consecutive assertion of the published proof.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenEndgameRemaining

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61BranchChoice

/-- The first terminal case of 6.1(12), exactly the paper sentence:

> *"If `v = b₃`, then `B₃` has length 2 and both its edges belong to `X`, and the fourth
> outcome of the theorem holds."*

The preceding helper `claim12_v_eq_b3_short_complete` proves the first two clauses.  The open
part is the cardinal count and the identification of the original graph with `K₄`. -/
theorem claim12_v_eq_b3_conclusion
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ d₁ d₂ : Sym2 (Fin n)) (u v : Fin n)
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂))
    (hd₁ : d₁ ∈ incidentEdges H b₁) (hd₁X : d₁ ∈ extraEdges G H K φ Y y₂)
    (hd₂ : d₂ ∈ incidentEdges H b₂) (hd₂X : d₂ ∈ extraEdges G H K φ Y y₁)
    (hf₁eq : f₁ = s(b₁, u)) (hf₂eq : f₂ = s(b₂, u))
    (hd₁eq : d₁ = s(b₁, v)) (hd₂eq : d₂ = s(b₂, v))
    (hu₁ : u ≠ b₁) (hu₂ : u ≠ b₂) (hv₁ : v ≠ b₁) (hv₂ : v ≠ b₂)
    (huv : u ≠ v) (hvdeg : (H.neighborSet v).ncard = 2 ∨
      (H.neighborSet v).ncard = 3) (hvb₃ : v = b₃) :
    Thm61Concl G m J n H K φ Y := by
  exact Workspace.ProofLemmas.Thm61Claim12VEq.conclusion G hG m J hJ n H K hsub φ Y
    hYanti hYmajor hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ d₁ d₂ u v
    hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne hd₁ hd₁X hd₂ hd₂X
    hf₁eq hf₂eq hd₁eq hd₂eq hu₁ hu₂ hv₁ hv₂ huv hvdeg hvb₃

/-- The degree-three terminal case of 6.1(12), exactly the paper sentence:

> *"If `v ≠ b₃` and `v` has degree 3, then the third edge incident with `v` is `vb₃`, and `b`
> is a triad, and `H` consists of the vertices `b,b₁,b₂,b₃,v` and a branch `B` with ends `b₃`
> and `u`; but then `J = K₃,₃`, and if `B` has length 1 then the second outcome of the theorem
> holds, and otherwise the first outcome holds."* -/
theorem claim12_degree_three_conclusion
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ d₁ d₂ : Sym2 (Fin n)) (u v : Fin n)
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂))
    (hd₁ : d₁ ∈ incidentEdges H b₁) (hd₁X : d₁ ∈ extraEdges G H K φ Y y₂)
    (hd₂ : d₂ ∈ incidentEdges H b₂) (hd₂X : d₂ ∈ extraEdges G H K φ Y y₁)
    (hf₁eq : f₁ = s(b₁, u)) (hf₂eq : f₂ = s(b₂, u))
    (hd₁eq : d₁ = s(b₁, v)) (hd₂eq : d₂ = s(b₂, v))
    (hu₁ : u ≠ b₁) (hu₂ : u ≠ b₂) (hv₁ : v ≠ b₁) (hv₂ : v ≠ b₂)
    (huv : u ≠ v) (hvb₃ : v ≠ b₃) (hvdeg : (H.neighborSet v).ncard = 3) :
    Thm61Concl G m J n H K φ Y := by
  exact Workspace.ProofLemmas.Thm61Claim12DegreeThree.conclusion G hG m J hJ n H K hsub φ Y
    hYanti hYmajor hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ d₁ d₂ u v
    hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne hd₁ hd₁X hd₂ hd₂X
    hf₁eq hf₂eq hd₁eq hd₂eq hu₁ hu₂ hv₁ hv₂ huv hvb₃ hvdeg

/-- The bridging paragraph and claim (13), starting with the oriented parity choice
`B₁` even and `B₂` odd.  The conclusion records the branch `B₄` introduced by the paper and
the four assertions of (13). -/
theorem even_final_claim13
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (hB₁even : Even (trackLength B₁)) (hB₂odd : Odd (trackLength B₂)) :
    ∃ (e₄ : Sym2 (Fin n)) (B₄ : List (Fin n)) (b₄ : Fin n),
      e₄ ∈ incidentEdges H b₂ ∧ IsBranch H B₄ ∧ e₄ ∈ trackEdges B₄ ∧
      IsTrackFrom H B₄ b₂ b₄ ∧ b₄ = b₃ ∧ trackLength B₃ = 1 ∧
      Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ Even (trackLength B₄) := by
  exact Workspace.ProofLemmas.Thm61EvenFinalClaim13.even_final_claim13
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
    y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
    hbc hadj hXb hB₁even hB₂odd

/-- The closing paragraph after 6.1(13), exactly from *"Let `B₅` be the branch of `H` between
`b₁,b₃`"* through *"But then the fourth outcome of the theorem holds. This proves 6.1."* -/
theorem even_final_closing
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ e₄ : Sym2 (Fin n)) (B₁ B₂ B₃ B₄ : List (Fin n))
    (b₁ b₂ b₃ b₄ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (hB₁even : Even (trackLength B₁)) (hB₂odd : Odd (trackLength B₂))
    (he₄ : e₄ ∈ incidentEdges H b₂) (hB₄ : IsBranch H B₄)
    (he₄B₄ : e₄ ∈ trackEdges B₄) (hfrom₄ : IsTrackFrom H B₄ b₂ b₄)
    (hb₄ : b₄ = b₃) (hB₃one : trackLength B₃ = 1)
    (hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (hB₄even : Even (trackLength B₄)) :
    Thm61Concl G m J n H K φ Y := by
  exact Workspace.ProofLemmas.Thm61EvenFinalClosing.even_final_closing
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
    y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ e₄ B₁ B₂ B₃ B₄
    b₁ b₂ b₃ b₄ hbc hadj hXb hB₁even hB₂odd he₄ hB₄ he₄B₄ hfrom₄ hb₄
    hB₃one hJiso hB₄even

/-- The oriented form of the final even-case argument. -/
theorem even_final_oriented
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (hB₁even : Even (trackLength B₁)) (hB₂odd : Odd (trackLength B₂)) :
    Thm61Concl G m J n H K φ Y := by
  obtain ⟨e₄, B₄, b₄, he₄, hB₄, he₄B₄, hfrom₄, hb₄, hB₃one, hJiso, hB₄even⟩ :=
    even_final_claim13 G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
      hbc hadj hXb hB₁even hB₂odd
  exact even_final_closing G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
    y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ e₄ B₁ B₂ B₃ B₄
    b₁ b₂ b₃ b₄ hbc hadj hXb hB₁even hB₂odd he₄ hB₄ he₄B₄ hfrom₄ hb₄
    hB₃one hJiso hB₄even

end Workspace.ProofLemmas.Thm61EvenEndgameRemaining
