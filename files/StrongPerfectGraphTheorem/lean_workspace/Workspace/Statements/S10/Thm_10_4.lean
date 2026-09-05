import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm104NoMajor
import Workspace.ProofLemmas.Thm104AttachmentsSubset
import Workspace.ProofLemmas.Thm104Superset

/-!
# Section 10 — The even prism

The six numbered statements 10.1–10.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 56–63),
transcribed from `paper/pdf/S10_The_even_prism.md`.

All the defined terms used here are imported and never restated: *prism* / *form a prism*,
*even prism*, *saturates*, *major*, *local* (with respect to a prism) come from
`Workspace.Types.Prisms`; *attachment* / *appearance* / *(non)degenerate appearance* from
`Workspace.Types.Appearances`; *Berge*, *connected set*, *path*, *length*, *interior* from
`Workspace.Types.Core`; *proper 2-join* and *balanced skew partition* from
`Workspace.Types.Decompositions`.

Encoding conventions (see `paper/spec/CONVENTIONS.md`):

* the paper's indices `1,2,3` are `0,1,2 : Fin 3`, so `R₁,R₂,R₃` is a family
  `R : Fin 3 → List V` and `a₁,a₂,a₃` is `a : Fin 3 → V` (this matches `Prisms`);
* a path is the list of its vertices in order, and `V(P)` for such a list `P` is
  `{v | v ∈ P}`; "a path in `F`" is a path of `G` all of whose vertices lie in `F`;
* `K` is the vertex set of the prism, i.e. `V(R₁) ∪ V(R₂) ∪ V(R₃)`, and
  `F ⊆ V(G) \ V(K)` is `F ⊆ Kᶜ`;
* "there is a nondegenerate appearance of `K₄` in `G`" is spelled out at each use as
  `∃ n (H : SimpleGraph (Fin n)) (K' : Set V), IsAppearance G K₄ H K' ∧
   NondegenerateAppearance K₄ H`, where `K₄` is `(⊤ : SimpleGraph (Fin 4))`;
* "the only edges between `X` and `Y` are …" is rendered as: every edge between `X` and `Y`
  is one of the listed ones (the listed ones being asserted separately as conjuncts).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S10

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **10.4** (printed p. 59), introduced by *"Another useful corollary of 10.1 is the
following."*

PAPER: *"Let `G` be Berge, such that there is no nondegenerate appearance of `K₄` in `G`.
Let `R₁, R₂, R₃` form a prism `K` in a Berge graph `G`, with triangles `{a₁, a₂, a₃}` and
`{b₁, b₂, b₃}`, where each `Rᵢ` has ends `aᵢ` and `bᵢ`.  Let `F ⊆ V(G) \ V(K)` be connected,
such that if the prism is even then no vertex in `F` is major with respect to `K`.  Assume
that the set of attachments of `F` in `K` is not local, but none are in `V(R₃)`.  Then
`|F| ≥ 2`, and the set of attachments of `F` in `K` is precisely `{a₁, b₁, a₂, b₂}`."*

*"if the prism is even then no vertex in `F` is major"* is transcribed as the implication it
is.  `|F| ≥ 2` is `F.Nontrivial` (`∃ x ∈ F, ∃ y ∈ F, x ≠ y`), and *"none are in `V(R₃)`"*
says that no attachment of `F` in `K` lies on `R₃`. -/
theorem thm_10_4 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFmaj : IsEvenPrism G a b (R 0) (R 1) (R 2) → ∀ v ∈ F, ¬ MajorForPrism G a b v)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hR₃ : ∀ v ∈ attachments G F K, v ∉ R 2) :
    F.Nontrivial ∧ attachments G F K = ({a 0, b 0, a 1, b 1} : Set V) := by
  -- PAPER: *"If there is a major vertex `v ∈ F`, then since it has no neighbours in `R₃`, it
  -- is adjacent to `a₁` and `b₂`, and since `v-a₁-a₃-R₃-b₃-b₂-v` is a hole, it follows that
  -- the prism is even, contrary to the hypothesis.  So there is no major vertex in `F`."*
  have hnomaj : ∀ v ∈ F, ¬ MajorForPrism G a b v :=
    Workspace.ProofLemmas.Thm104NoMajor.thm104_no_major G hG a b R K F hprism hK hFK hFmaj hR₃
  -- PAPER: *"By 10.3 no internal vertex of `R₁` or `R₂` is an attachment of `F`."*
  have hsubset :=
    Workspace.ProofLemmas.Thm104AttachmentsSubset.thm104_attachments_subset G hG hK4 a b R K F
      hprism hK hFK hFconn hnomaj hFloc hR₃
  -- PAPER: *"By 10.1, there is a path in `F` satisfying one of 10.1.1-4; and since it has no
  -- attachments in `R₃`, it must satisfy 10.1.1 or 10.1.3, and in either case `a₁, b₁, a₂, b₂`
  -- are all attachments of `F`."*
  have hsup :=
    Workspace.ProofLemmas.Thm104Superset.thm104_superset G hG a b R K F hprism hK hFK hFconn
      hnomaj hFloc hR₃ hsubset.2.2
  have hatt : attachments G F K = ({a 0, b 0, a 1, b 1} : Set V) := by
    refine Set.Subset.antisymm ?_ hsup
    intro x hx
    rcases hsubset.2.2 x hx with rfl | rfl | rfl | rfl <;> simp
  refine ⟨?_, hatt⟩
  -- PAPER: *"Since no vertex in `F` is major it follows that `|F| ≥ 2`."*
  by_contra hnt
  rw [Set.not_nontrivial_iff] at hnt
  obtain ⟨htA, htB, hab, hP0, hP1, hP2, h01, h02, h12⟩ := id hprism
  obtain ⟨-, f0, hf0F, hadja0⟩ : IsAttachment G F K (a 0) := hsup (by simp)
  -- every attachment has its unique `F`-neighbour equal to `f0`
  have getf : ∀ x : V, x ∈ attachments G F K → G.Adj x f0 := by
    intro x hx
    obtain ⟨-, g, hgF, hadj⟩ := hx
    rw [hnt hgF hf0F] at hadj
    exact hadj
  have hA0 : G.Adj (a 0) f0 := getf (a 0) (hsup (by simp))
  have hB0 : G.Adj (b 0) f0 := getf (b 0) (hsup (by simp))
  have hA1 : G.Adj (a 1) f0 := getf (a 1) (hsup (by simp))
  have hB1 : G.Adj (b 1) f0 := getf (b 1) (hsup (by simp))
  -- so `f0` is adjacent to two vertices of each triangle, i.e. `f0` is major
  refine hnomaj f0 hf0F ⟨?_, ?_⟩
  · have hsub : ({a 0, a 1} : Set V) ⊆ (({a 0, a 1, a 2} : Set V) ∩ G.neighborSet f0) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨by simp, hA0.symm⟩
      · exact ⟨by simp, hA1.symm⟩
    have h2 : ({a 0, a 1} : Set V).ncard = 2 := Set.ncard_pair (htA 0 1 (by decide)).ne
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · have hsub : ({b 0, b 1} : Set V) ⊆ (({b 0, b 1, b 2} : Set V) ∩ G.neighborSet f0) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨by simp, hB0.symm⟩
      · exact ⟨by simp, hB1.symm⟩
    have h2 : ({b 0, b 1} : Set V).ncard = 2 := Set.ncard_pair (htB 0 1 (by decide)).ne
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega


end SPGT

end Workspace.Statements.S10
