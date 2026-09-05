/-  Assembly of 10.1 from the six commissioned carve-outs.  See paper/proofs/10_1.md. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.Thm101Assembly
import Workspace.ProofLemmas.Thm101ClaimOne
import Workspace.ProofLemmas.Thm101ClaimTwo
import Workspace.ProofLemmas.Thm101ClaimThree
import Workspace.ProofLemmas.Thm101Endgame
import Workspace.ProofLemmas.Thm101NonlocalPair

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S10

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Bookkeeping -/

/-- Locality passes to subsets. -/
private theorem local_mono {a b : Fin 3 → V} {R₁ R₂ R₃ : List V} {Y Z : Set V}
    (h : LocalForPrism a b R₁ R₂ R₃ Y) (hZY : Z ⊆ Y) :
    LocalForPrism a b R₁ R₂ R₃ Z := by
  rcases h with h | h | h | h | h
  exacts [Or.inl (hZY.trans h), Or.inr (Or.inl (hZY.trans h)),
    Or.inr (Or.inr (Or.inl (hZY.trans h))),
    Or.inr (Or.inr (Or.inr (Or.inl (hZY.trans h)))),
    Or.inr (Or.inr (Or.inr (Or.inr (hZY.trans h))))]

/-- PAPER: *"We may assume that `F` is minimal such that it is connected and its set of
attachments in `K` is not local."* -/
private theorem exists_minimal_nonlocal (G : SimpleGraph V) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (hFconn : ConnectedSet G F)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K)) :
    ∃ F₀ : Set V, F₀ ⊆ F ∧ ConnectedSet G F₀ ∧
      ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F₀ K) ∧
      ∀ F₁ : Set V, F₁ ⊆ F₀ → ConnectedSet G F₁ →
        ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F₁ K) → F₁ = F₀ := by
  classical
  obtain ⟨F₀, hF₀, hmin⟩ :=
    Set.exists_min_image
      {F' : Set V | F' ⊆ F ∧ ConnectedSet G F' ∧
        ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F' K)}
      Set.ncard (Set.toFinite _) ⟨F, subset_rfl, hFconn, hFloc⟩
  exact ⟨F₀, hF₀.1, hF₀.2.1, hF₀.2.2, fun F₁ h1 h2 h3 =>
    Set.eq_of_subset_of_ncard_le h1 (hmin F₁ ⟨h1.trans hF₀.1, h2, h3⟩) (Set.toFinite _)⟩

/-- The conclusion of 10.1 transported along *"by exchanging `A` and `B` if necessary"*
(which reverses each `Rᵢ`). -/
private theorem concl_swap_rev (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K : Set V) (f : List V) (f₁ fn : V)
    (h : Thm101Assembly.Concl G b a (fun i => (R i).reverse) K f f₁ fn) :
    Thm101Assembly.Concl G a b R K f f₁ fn := by
  obtain ⟨a', b', R', σ, hR', hab, hcase⟩ := h
  subst hR'
  exact ⟨a', b', fun i => R (σ i), σ, rfl, hab.symm, by
    simpa only [List.mem_reverse] using hcase⟩

/-! ### The three printed cases, with the prism relabelled -/

/-- Claim (2) of the printed proof, after relabelling the three paths by `σ`.

**Orientation.**  In claim (2)'s configuration it is `fₙ`, not `f₁`, that acquires the two
triangle neighbours (*"If `fₙ` is adjacent to both `a₂, a₃` then statement 4 of the theorem
holds"*), so the conclusion delivered is the one for the path traversed the other way round,
`Concl … f.reverse fn f₁`.  See `Thm101ClaimTwo.claim_two`. -/
private theorem case_two_fwd (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V) (σ : Equiv.Perm (Fin 3))
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length) (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({a 0, a 1, a 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ {v : V | v ∈ R (σ 0)}) :
    Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  refine Thm101Assembly.concl_perm σ ?_
  refine Thm101ClaimTwo.claim_two G hG (fun i => a (σ i)) (fun i => b (σ i))
    (fun i => R (σ i)) K F f f₁ fn (PrismSymmetry.formPrism_perm hprism σ) ?_ hFK hf hfF hn
    (fun w hw h => hFmaj w hw ((PrismSymmetry.majorForPrism_perm σ).mp h))
    (fun h => hFloc ((PrismSymmetry.localForPrism_perm σ).mp h)) ?_ hX2
  · rw [hK]; exact (PrismSymmetry.prismVertices_perm R σ).symm
  · show attachments G (F \ {f₁}) K ⊆ ({a (σ 0), a (σ 1), a (σ 2)} : Set V)
    rw [PrismSymmetry.triple_perm a σ]; exact hX1

/-- Claim (2), with the two triangles interchanged as well. -/
private theorem case_two_swap (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V) (σ : Equiv.Perm (Fin 3))
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length) (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({b 0, b 1, b 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ {v : V | v ∈ R (σ 0)}) :
    Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  refine concl_swap_rev G a b R K f.reverse fn f₁ ?_
  refine case_two_fwd G hG b a (fun i => (R i).reverse) K F f f₁ fn σ
    (PrismSymmetry.formPrism_swap hprism) ?_ hFK hf hfF hn
    (fun w hw h => hFmaj w hw (PrismSymmetry.majorForPrism_swap.mp h))
    (fun h => hFloc (PrismSymmetry.localForPrism_swap.mp h)) hX1 ?_
  · rw [hK]; exact (PrismSymmetry.prismVertices_reverse (R 0) (R 1) (R 2)).symm
  · intro z hz
    have h := hX2 hz
    simpa only [Set.mem_setOf_eq, List.mem_reverse] using h

/-- Claim (3) of the printed proof.

**Orientation.**  The printed same-parity branch ends *"either `fₙ` is adjacent to `a₃` or `f₁`
to `b₃`"*, and the two sub-cases land on opposite orientations of the path, so claim (3)
delivers a genuine disjunction, which this lemma simply forwards.  See
`Thm101ClaimThree.claim_three`. -/
private theorem case_three_fwd (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length) (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({a 0, a 1, a 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ ({b 0, b 1, b 2} : Set V)) :
    Thm101Assembly.Concl G a b R K f f₁ fn ∨
      Thm101Assembly.Concl G a b R K f.reverse fn f₁ :=
  Thm101ClaimThree.claim_three G hG a b R K F f f₁ fn hprism hK hFK hf hfF hn hFmaj hFloc hX1 hX2

/-- Claim (3), with the two triangles interchanged. -/
private theorem case_three_swap (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length) (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({b 0, b 1, b 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ ({a 0, a 1, a 2} : Set V)) :
    Thm101Assembly.Concl G a b R K f f₁ fn ∨
      Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  have hKr : K = {v : V | v ∈ (R 0).reverse} ∪ {v : V | v ∈ (R 1).reverse} ∪
      {v : V | v ∈ (R 2).reverse} := by
    rw [hK]; exact (PrismSymmetry.prismVertices_reverse (R 0) (R 1) (R 2)).symm
  rcases case_three_fwd G hG b a (fun i => (R i).reverse) K F f f₁ fn
    (PrismSymmetry.formPrism_swap hprism) hKr hFK hf hfF hn
    (fun w hw h => hFmaj w hw (PrismSymmetry.majorForPrism_swap.mp h))
    (fun h => hFloc (PrismSymmetry.localForPrism_swap.mp h)) hX1 hX2 with h | h
  · exact Or.inl (concl_swap_rev G a b R K f f₁ fn h)
  · exact Or.inr (concl_swap_rev G a b R K f.reverse fn f₁ h)

/-- The closing paragraph of the printed proof, after relabelling the three paths by `σ`. -/
private theorem case_endgame (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V) (σ : Equiv.Perm (Fin 3))
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length) (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ {v : V | v ∈ R (σ 1)})
    (hX2 : attachments G (F \ {fn}) K ⊆ {v : V | v ∈ R (σ 0)}) :
    Thm101Assembly.Concl G a b R K f f₁ fn := by
  refine Thm101Assembly.concl_perm σ ?_
  refine Thm101Endgame.endgame G hG (fun i => a (σ i)) (fun i => b (σ i))
    (fun i => R (σ i)) K F f f₁ fn (PrismSymmetry.formPrism_perm hprism σ) ?_ hFK hf hfF hn
    (fun w hw h => hFmaj w hw ((PrismSymmetry.majorForPrism_perm σ).mp h))
    (fun h => hFloc ((PrismSymmetry.localForPrism_perm σ).mp h)) hX1 hX2
  · rw [hK]; exact (PrismSymmetry.prismVertices_perm R σ).symm

/-! ### *"From (2), since both `X₁` and `X₂` are local, we may assume …"* -/

/-- The five-by-five case analysis on the local types of `X₁` and `X₂`, using claims (2), (3)
and the endgame.  Six of the twenty-five cases need the path traversed the other way round;
that is why the disjunction on the right is there. -/
private theorem step (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length) (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hXu : attachments G F K ⊆
      attachments G (F \ {f₁}) K ∪ attachments G (F \ {fn}) K)
    (h1 : LocalForPrism a b (R 0) (R 1) (R 2) (attachments G (F \ {f₁}) K))
    (h2 : LocalForPrism a b (R 0) (R 1) (R 2) (attachments G (F \ {fn}) K)) :
    Thm101Assembly.Concl G a b R K f f₁ fn ∨
      Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  have hfr : IsPathFrom G f.reverse fn f₁ := PathBasics.isPathFrom_reverse hf
  have hfFr : F = {x : V | x ∈ f.reverse} := by
    rw [hfF]; ext x; simp
  have hnr : 2 ≤ f.reverse.length := by simpa using hn
  -- Claims (2) and (3) deliver the conclusion for the *reversed* path, so feeding them the
  -- reversed path `f.reverse` (with ends `fn`, `f₁`) delivers it for `f` itself.
  have unrev : Thm101Assembly.Concl G a b R K f.reverse.reverse f₁ fn →
      Thm101Assembly.Concl G a b R K f f₁ fn := fun h => by
    rwa [List.reverse_reverse] at h
  have contra : ∀ S : Set V, attachments G (F \ {f₁}) K ⊆ S →
      attachments G (F \ {fn}) K ⊆ S → LocalForPrism a b (R 0) (R 1) (R 2) S → False :=
    fun S s1 s2 hS => hFloc (local_mono hS (hXu.trans (Set.union_subset s1 s2)))
  rcases h1 with q1 | q1 | q1 | q1 | q1
  · -- X₁ ⊆ V(R 0)
    rcases h2 with q2 | q2 | q2 | q2 | q2
    · exact (contra _ q1 q2 (Or.inl subset_rfl)).elim
    · refine Or.inl (case_endgame G hG a b R K F f f₁ fn (Equiv.swap 0 1) hprism hK hFK hf hfF
        hn hFmaj hFloc ?_ ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 1) 1 = 0 from by decide]; exact q1
      · rw [show (Equiv.swap (0 : Fin 3) 1) 0 = 1 from by decide]; exact q2
    · refine Or.inl (case_endgame G hG a b R K F f f₁ fn
        (Equiv.swap 0 1 * Equiv.swap 0 2) hprism hK hFK hf hfF hn hFmaj hFloc ?_ ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) 1 = 0 from by decide]
        exact q1
      · rw [show (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide]
        exact q2
    · exact Or.inl (unrev (case_two_fwd G hG a b R K F f.reverse fn f₁ (Equiv.refl (Fin 3))
        hprism hK hFK hfr hfFr hnr hFmaj hFloc q2 q1))
    · exact Or.inl (unrev (case_two_swap G hG a b R K F f.reverse fn f₁ (Equiv.refl (Fin 3))
        hprism hK hFK hfr hfFr hnr hFmaj hFloc q2 q1))
  · -- X₁ ⊆ V(R 1)
    rcases h2 with q2 | q2 | q2 | q2 | q2
    · exact Or.inl (case_endgame G hG a b R K F f f₁ fn (Equiv.refl (Fin 3)) hprism hK hFK hf
        hfF hn hFmaj hFloc q1 q2)
    · exact (contra _ q1 q2 (Or.inr (Or.inl subset_rfl))).elim
    · refine Or.inl (case_endgame G hG a b R K F f f₁ fn (Equiv.swap 0 2) hprism hK hFK hf hfF
        hn hFmaj hFloc ?_ ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 2) 1 = 1 from by decide]; exact q1
      · rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide]; exact q2
    · refine Or.inl (unrev (case_two_fwd G hG a b R K F f.reverse fn f₁ (Equiv.swap 0 1) hprism
        hK hFK hfr hfFr hnr hFmaj hFloc q2 ?_))
      · rw [show (Equiv.swap (0 : Fin 3) 1) 0 = 1 from by decide]; exact q1
    · refine Or.inl (unrev (case_two_swap G hG a b R K F f.reverse fn f₁ (Equiv.swap 0 1) hprism
        hK hFK hfr hfFr hnr hFmaj hFloc q2 ?_))
      · rw [show (Equiv.swap (0 : Fin 3) 1) 0 = 1 from by decide]; exact q1
  · -- X₁ ⊆ V(R 2)
    rcases h2 with q2 | q2 | q2 | q2 | q2
    · refine Or.inl (case_endgame G hG a b R K F f f₁ fn (Equiv.swap 1 2) hprism hK hFK hf hfF
        hn hFmaj hFloc ?_ ?_)
      · rw [show (Equiv.swap (1 : Fin 3) 2) 1 = 2 from by decide]; exact q1
      · rw [show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide]; exact q2
    · refine Or.inl (case_endgame G hG a b R K F f f₁ fn
        (Equiv.swap 0 1 * Equiv.swap 1 2) hprism hK hFK hf hfF hn hFmaj hFloc ?_ ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 1 = 2 from by decide]
        exact q1
      · rw [show (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 0 = 1 from by decide]
        exact q2
    · exact (contra _ q1 q2 (Or.inr (Or.inr (Or.inl subset_rfl)))).elim
    · refine Or.inl (unrev (case_two_fwd G hG a b R K F f.reverse fn f₁ (Equiv.swap 0 2) hprism
        hK hFK hfr hfFr hnr hFmaj hFloc q2 ?_))
      · rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide]; exact q1
    · refine Or.inl (unrev (case_two_swap G hG a b R K F f.reverse fn f₁ (Equiv.swap 0 2) hprism
        hK hFK hfr hfFr hnr hFmaj hFloc q2 ?_))
      · rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide]; exact q1
  · -- X₁ ⊆ A
    rcases h2 with q2 | q2 | q2 | q2 | q2
    · exact Or.inr (case_two_fwd G hG a b R K F f f₁ fn (Equiv.refl (Fin 3)) hprism hK hFK hf
        hfF hn hFmaj hFloc q1 q2)
    · refine Or.inr (case_two_fwd G hG a b R K F f f₁ fn (Equiv.swap 0 1) hprism hK hFK hf
        hfF hn hFmaj hFloc q1 ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 1) 0 = 1 from by decide]; exact q2
    · refine Or.inr (case_two_fwd G hG a b R K F f f₁ fn (Equiv.swap 0 2) hprism hK hFK hf
        hfF hn hFmaj hFloc q1 ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide]; exact q2
    · exact (contra _ q1 q2 (Or.inr (Or.inr (Or.inr (Or.inl subset_rfl))))).elim
    · exact case_three_fwd G hG a b R K F f f₁ fn hprism hK hFK hf hfF hn hFmaj hFloc q1 q2
  · -- X₁ ⊆ B
    rcases h2 with q2 | q2 | q2 | q2 | q2
    · exact Or.inr (case_two_swap G hG a b R K F f f₁ fn (Equiv.refl (Fin 3)) hprism hK hFK hf
        hfF hn hFmaj hFloc q1 q2)
    · refine Or.inr (case_two_swap G hG a b R K F f f₁ fn (Equiv.swap 0 1) hprism hK hFK hf
        hfF hn hFmaj hFloc q1 ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 1) 0 = 1 from by decide]; exact q2
    · refine Or.inr (case_two_swap G hG a b R K F f f₁ fn (Equiv.swap 0 2) hprism hK hFK hf
        hfF hn hFmaj hFloc q1 ?_)
      · rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide]; exact q2
    · exact case_three_swap G hG a b R K F f f₁ fn hprism hK hFK hf hfF hn hFmaj hFloc q1 q2
    · exact (contra _ q1 q2 (Or.inr (Or.inr (Or.inr (Or.inr subset_rfl))))).elim

/-! ### 10.1 -/

theorem thm_10_1 (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hFmaj : ∀ v ∈ F, ¬ MajorForPrism G a b v) :
    ∃ (f : List V) (f₁ fn : V), IsPathFrom G f f₁ fn ∧ (∀ v ∈ f, v ∈ F) ∧ 1 ≤ f.length ∧
      ∃ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (σ : Equiv.Perm (Fin 3)),
        (R' = fun i => R (σ i)) ∧
        (((a' = fun i => a (σ i)) ∧ (b' = fun i => b (σ i))) ∨
          ((a' = fun i => b (σ i)) ∧ (b' = fun i => a (σ i)))) ∧
        -- 10.1.1
        ((∃ u u' : V, u ∈ R' 0 ∧ u' ∈ R' 0 ∧ G.Adj u u' ∧ G.Adj f₁ u ∧ G.Adj f₁ u' ∧
            ∃ w w' : V, w ∈ R' 1 ∧ w' ∈ R' 1 ∧ G.Adj w w' ∧ G.Adj fn w ∧ G.Adj fn w' ∧
              (∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
                (x = f₁ ∧ (k = u ∨ k = u')) ∨ (x = fn ∧ (k = w ∨ k = w'))) ∧
              Appears G (⊤ : SimpleGraph (Fin 4))) ∨
        -- 10.1.2
          (2 ≤ f.length ∧ (∀ i : Fin 3, G.Adj f₁ (a' i)) ∧ (∀ i : Fin 3, G.Adj fn (b' i)) ∧
            (∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
              (x = f₁ ∧ ∃ i : Fin 3, k = a' i) ∨ (x = fn ∧ ∃ i : Fin 3, k = b' i))) ∨
        -- 10.1.3
          (2 ≤ f.length ∧ G.Adj f₁ (a' 0) ∧ G.Adj f₁ (a' 1) ∧
            G.Adj fn (b' 0) ∧ G.Adj fn (b' 1) ∧
            (∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
              (x = f₁ ∧ (k = a' 0 ∨ k = a' 1)) ∨ (x = fn ∧ (k = b' 0 ∨ k = b' 1)))) ∨
        -- 10.1.4
          (G.Adj f₁ (a' 0) ∧ G.Adj f₁ (a' 1) ∧ (∃ y ∈ R' 2, y ≠ a' 2 ∧ G.Adj fn y) ∧
            (∀ x ∈ f, ∀ k ∈ K, k ≠ a' 2 → G.Adj x k →
              (x = f₁ ∧ (k = a' 0 ∨ k = a' 1)) ∨ (x = fn ∧ k ∈ R' 2)))) := by
  classical
  -- "We may assume that F is minimal such that it is connected and its set of attachments
  -- in K is not local."
  obtain ⟨F₀, hF₀F, hF₀conn, hF₀loc, hF₀min⟩ :=
    exists_minimal_nonlocal G a b R K F hFconn hFloc
  have hF₀K : F₀ ⊆ Kᶜ := hF₀F.trans hFK
  have hF₀maj : ∀ w ∈ F₀, ¬ MajorForPrism G a b w := fun w hw => hFmaj w (hF₀F hw)
  -- "We claim that some two-element subset of X is not local. … Consequently x₁, x₂ are not
  -- adjacent."
  have hXK : attachments G F₀ K ⊆ K := fun v hv => hv.1
  obtain ⟨x₁, hx₁X, x₂, hx₂X, hx12, hnadj, hpairloc⟩ :=
    Thm101NonlocalPair.exists_nonlocal_pair G a b R K (attachments G F₀ K) hprism hK hXK hF₀loc
  obtain ⟨hx₁K, w₁, hw₁F, hadj₁⟩ := hx₁X
  obtain ⟨hx₂K, w₂, hw₂F, hadj₂⟩ := hx₂X
  have hx₁F : x₁ ∉ F₀ := fun hc => (hF₀K hc) hx₁K
  have hx₂F : x₂ ∉ F₀ := fun hc => (hF₀K hc) hx₂K
  -- "From the minimality of F, there is a path with vertices x₁, f₁, …, fₙ, x₂ such that
  -- F = {f₁, …, fₙ}."
  obtain ⟨p, hp, hp3, hpint, hpconn, ⟨d₁, hd₁, hxd₁⟩, ⟨d₂, hd₂, hxd₂⟩⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hF₀conn hx12 hnadj hx₁F hx₂F
      ⟨w₁, hw₁F, hadj₁⟩ ⟨w₂, hw₂F, hadj₂⟩
  have hInl : ¬ LocalForPrism a b (R 0) (R 1) (R 2)
      (attachments G {z : V | z ∈ SPGT.interior p} K) := by
    intro hloc
    refine hpairloc (local_mono hloc ?_)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨hx₁K, d₁, hd₁, hxd₁⟩
    · exact ⟨hx₂K, d₂, hd₂, hxd₂⟩
  have hIeq : {z : V | z ∈ SPGT.interior p} = F₀ :=
    hF₀min _ (fun z hz => hpint z hz) hpconn hInl
  obtain ⟨g, g₁, gn, hgpath, hgI⟩ :
      ∃ (g : List V) (g₁ gn : V), IsPathFrom G g g₁ gn ∧ g = SPGT.interior p :=
    ⟨SPGT.interior p, _, _, PathGlue.isPathFrom_interior hp.1 hp3, rfl⟩
  have hgF : F₀ = {x : V | x ∈ g} := by rw [hgI]; exact hIeq.symm
  have hglen : 1 ≤ g.length := by
    rw [hgI, PathBasics.interior_length]; omega
  have hgmemF : ∀ v ∈ g, v ∈ F := fun v hv => hF₀F (by rw [hgF]; exact hv)
  rcases (show g.length = 1 ∨ 2 ≤ g.length by omega) with hlen1 | hlen2
  · -- (1) If n = 1 then the theorem holds.
    obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlen1
    have hFsingle : F₀ = {y} := by
      rw [hgF, hy]; ext z; simp
    have hyF₀ : y ∈ F₀ := by rw [hFsingle]; rfl
    have hconcl :=
      Thm101ClaimOne.claim_one G hG a b R K F₀ y hprism hK hF₀K hF₀loc hF₀maj hFsingle
    refine ⟨[y], y, y, ⟨PathBasics.isPathList_singleton G y, by simp, by simp⟩, ?_, by simp,
      hconcl⟩
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    exact hF₀F hyF₀
  · -- "We may therefore assume that n ≥ 2."
    have hg₁gn : g₁ ≠ gn :=
      PathBasics.isPathFrom_ends_ne hgpath (by change 1 ≤ g.length - 1; omega)
    have hgnd : g.Nodup := PathBasics.path_nodup hgpath.1
    have hgne : g ≠ [] := hgpath.1.1
    obtain ⟨y, t, hyt⟩ := List.exists_cons_of_ne_nil hgne
    have hy : y = g₁ := by
      have h := hgpath.2.1
      rw [hyt] at h
      simpa using h
    rw [hy] at hyt
    have hg₁notin : g₁ ∉ t := by
      have h := hgnd; rw [hyt] at h; exact (List.nodup_cons.mp h).1
    have hmemt : ∀ x : V, x ∈ t ↔ (x ∈ g ∧ x ≠ g₁) := by
      intro x
      constructor
      · intro hx
        refine ⟨by rw [hyt]; exact List.mem_cons_of_mem _ hx, ?_⟩
        rintro rfl; exact hg₁notin hx
      · rintro ⟨hx, hne⟩
        rw [hyt] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h hne
        · exact h
    have hdiff1 : F₀ \ {g₁} = {x : V | x ∈ t} := by
      rw [hgF]; ext x
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact (hmemt x).symm
    have hconn1 : ConnectedSet G (F₀ \ {g₁}) := by
      rw [hdiff1]
      refine InducedPathExtraction.connectedSet_setOf_mem_of_isPathList ?_
      have hd := PathBasics.isPathList_drop hgpath.1 (k := 1) (by omega)
      rw [hyt] at hd
      simpa using hd
    have hg₁F₀ : g₁ ∈ F₀ := by rw [hgF, hyt]; exact List.mem_cons_self ..
    have hloc1 : LocalForPrism a b (R 0) (R 1) (R 2) (attachments G (F₀ \ {g₁}) K) := by
      by_contra hc
      have heq := hF₀min _ Set.diff_subset hconn1 hc
      have hmem : g₁ ∈ F₀ \ {g₁} := by rw [heq]; exact hg₁F₀
      exact hmem.2 rfl
    have hgl : g.getLast hgne = gn := by
      have h := hgpath.2.2
      rw [List.getLast?_eq_some_getLast hgne] at h
      exact Option.some_inj.mp h
    have hmemdl : ∀ x : V, x ∈ g.dropLast ↔ (x ∈ g ∧ x ≠ gn) := by
      intro x
      rw [PathBasics.mem_dropLast_iff hgnd hgne, hgl]
    have hdiff2 : F₀ \ {gn} = {x : V | x ∈ g.dropLast} := by
      rw [hgF]; ext x
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact (hmemdl x).symm
    have hconn2 : ConnectedSet G (F₀ \ {gn}) := by
      rw [hdiff2]
      refine InducedPathExtraction.connectedSet_setOf_mem_of_isPathList ?_
      have hd := PathBasics.isPathList_take hgpath.1 (k := g.length - 1) (by omega)
      rwa [← List.dropLast_eq_take] at hd
    have hgnF₀ : gn ∈ F₀ := by
      rw [hgF]; exact PathBasics.getLast_mem hgpath.2.2
    have hloc2 : LocalForPrism a b (R 0) (R 1) (R 2) (attachments G (F₀ \ {gn}) K) := by
      by_contra hc
      have heq := hF₀min _ Set.diff_subset hconn2 hc
      have hmem : gn ∈ F₀ \ {gn} := by rw [heq]; exact hgnF₀
      exact hmem.2 rfl
    have hXu : attachments G F₀ K ⊆
        attachments G (F₀ \ {g₁}) K ∪ attachments G (F₀ \ {gn}) K := by
      rintro v ⟨hvK, w, hwF, hadj⟩
      by_cases hw : w = g₁
      · refine Or.inr ⟨hvK, w, ⟨hwF, ?_⟩, hadj⟩
        simp only [Set.mem_singleton_iff]
        rw [hw]; exact hg₁gn
      · exact Or.inl ⟨hvK, w, ⟨hwF, by simpa using hw⟩, hadj⟩
    rcases step G hG a b R K F₀ g g₁ gn hprism hK hF₀K hgpath hgF hlen2 hF₀maj hF₀loc hXu
      hloc1 hloc2 with hc | hc
    · exact ⟨g, g₁, gn, hgpath, hgmemF, hglen, hc⟩
    · refine ⟨g.reverse, gn, g₁, PathBasics.isPathFrom_reverse hgpath, ?_, ?_, hc⟩
      · intro v hv; exact hgmemF v (List.mem_reverse.mp hv)
      · rw [List.length_reverse]; exact hglen

end SPGT

end Workspace.Statements.S10
