import Workspace.ProofLemmas.Thm93Infrastructure
import Workspace.ProofLemmas.KnotLabels
import Workspace.ProofLemmas.KnotCompl
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S09.Thm_9_2

/-! The common neighbours and the paths used in case (2) of 9.3. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoCommon

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

variable {V : Type*}

/-- PAPER (9.3, p. 49): "Let `X` be the set of vertices of `K` which, in `G`, have no
neighbours in `F`." -/
def common (G : SimpleGraph V) (K F : Set V) : Set V :=
  {v ∈ K | VertexComplete Gᶜ v F}

/-- Outside `F`, being complete to `F` in the complement means having no neighbour in `F`. -/
theorem mem_common_iff {G : SimpleGraph V} {K F : Set V} (hF : F ⊆ Kᶜ) {v : V} :
    v ∈ common G K F ↔ v ∈ K ∧ ∀ f ∈ F, ¬ G.Adj v f := by
  constructor
  · rintro ⟨hv, hc⟩
    exact ⟨hv, fun f hf => (hc f hf).2⟩
  · rintro ⟨hv, hc⟩
    refine ⟨hv, fun f hf => ⟨?_, hc f hf⟩⟩
    rintro rfl
    exact hF hf hv

/-- PAPER (9.3, p. 49): "By hypothesis, `V(K) \\ X` is not local." -/
theorem diff_common_eq_attachments {G : SimpleGraph V} {K F : Set V} (hF : F ⊆ Kᶜ) :
    K \ common G K F = attachments G F K := by
  ext v
  rw [Set.mem_diff, mem_common_iff hF]
  change (v ∈ K ∧ ¬ (v ∈ K ∧ ∀ f ∈ F, ¬ G.Adj v f)) ↔
    (v ∈ K ∧ ∃ f ∈ F, G.Adj v f)
  simp only [not_and, not_forall, not_not]
  tauto

/-- PAPER (9.3, p. 49): "and hence `X` does not resolve the knot ... in `G̅`." -/
theorem common_not_resolves {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂) {K F : Set V}
    (hK : KnotInduces P₁ P₂ Q₁ Q₂ K) (hF : F ⊆ Kᶜ)
    (hlocal : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K)) :
    ¬ ResolvesKnot Gᶜ Q₁ Q₂ P₁.reverse P₂.reverse (common G K F) := by
  intro hres
  have h := (KnotCompl.resolvesKnot_iff_localForKnot_compl
    (KnotCompl.isKnot_compl hknot) (KnotCompl.knotInduces_compl hK)).mp hres
  apply hlocal
  simpa only [compl_compl, LocalForKnot, List.mem_reverse,
    diff_common_eq_attachments hF] using h

/-- Pulling the common neighbours back through an appearance gives exactly 6.1's set. -/
theorem edge_common_eq {n : ℕ} {G : SimpleGraph V} {H : SimpleGraph (Fin n)} {K F : Set V}
    (phi : H.lineGraph ≃g Gᶜ.induce K) :
    {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      (↑(phi ⟨e, he⟩) : V) ∈ common G K F} =
    {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F} := by
  ext e
  constructor
  · rintro ⟨he, _, hc⟩
    exact ⟨he, hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨he, (phi ⟨e, he⟩).property, hc⟩

/-- The set form of the saturation condition, at a prescribed branch vertex. -/
theorem common_triangle {n : ℕ} {G : SimpleGraph V} {H : SimpleGraph (Fin n)} {K F : Set V}
    (phi : H.lineGraph ≃g Gᶜ.induce K) (N : Fin n → Set V)
    (hN : ∀ c, N c = {v : V | ∃ e, ∃ he : e ∈ H.edgeSet,
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (hsat : SaturatesLineGraph H {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F})
    {c : Fin n} (hc : c ∈ branchVertices H) :
    (N c \ common G K F).Subsingleton := by
  rintro u ⟨hu, huX⟩ v ⟨hv, hvX⟩
  rw [hN c] at hu hv
  obtain ⟨e, he, hec, rfl⟩ := hu
  obtain ⟨e', he', hec', rfl⟩ := hv
  have heX : e ∉ {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F} := by
    rintro ⟨_, h⟩
    exact huX ⟨(phi ⟨e, he⟩).property, h⟩
  have heX' : e' ∉ {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F} := by
    rintro ⟨_, h⟩
    exact hvX ⟨(phi ⟨e', he'⟩).property, h⟩
  have heq := hsat c hc ⟨hec, heX⟩ ⟨hec', heX'⟩
  subst e'
  rfl

/-- An edge of a path of length at least two has an internal end. Thus it cannot be
complete to `F` when every internal vertex fails to be complete to `F`. -/
theorem no_complete_edge {G : SimpleGraph V} {p : List V} {a b : V} {F : Set V}
    (hp : IsPathFrom G p a b) (hlen : 2 ≤ pathLength p)
    (hinterior : ∀ w ∈ SPGT.interior p, ¬ VertexComplete G w F) :
    ¬ ∃ u ∈ p, ∃ v ∈ p, EdgeComplete G F u v := by
  rintro ⟨u, hu, v, hv, hadj, huc, hvc⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
  have hc := (PathBasics.path_adj_iff hp.1 hi hj).mp hadj
  have hl := PathBasics.length_eq_pathLength_add_one hp.1
  rcases (show (1 ≤ i ∧ i + 2 ≤ p.length) ∨ (1 ≤ j ∧ j + 2 ≤ p.length) by omega) with h | h
  · exact hinterior _ (PathBasics.getElem_mem_interior hp.1 hi h.1 h.2) huc
  · exact hinterior _ (PathBasics.getElem_mem_interior hp.1 hj h.1 h.2) hvc

variable [Fintype V] [DecidableEq V]

/-- PAPER (9.3, p. 49): "By 9.2, `X` is disjoint from one of `V(Q₁), V(Q₂)`." -/
theorem common_misses_one {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂) {K F : Set V}
    (hK : KnotInduces P₁ P₂ Q₁ Q₂ K) (hF : F ⊆ Kᶜ)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (hlocal : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K))
    {n : ℕ} {H : SimpleGraph (Fin n)} (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (hsat : SaturatesLineGraph H {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F}) :
    Disjoint (common G K F) {v | v ∈ Q₁} ∨ Disjoint (common G K F) {v | v ∈ Q₂} := by
  have hnres := common_not_resolves hknot hK hF hlocal
  have h92 := (Workspace.Statements.S09.SPGT.thm_9_2 Gᶜ Q₁ Q₂ P₁.reverse P₂.reverse
    (KnotCompl.isKnot_compl hknot) K (KnotCompl.knotInduces_compl hK)
    (by simpa [PathBasics.pathLength_reverse] using hP₁len)
    (by simpa [PathBasics.pathLength_reverse] using hP₂len)
    n H phi happ (common G K F) (fun _ hv => hv.1)).2
  rw [edge_common_eq phi] at h92
  by_contra h
  have hn : ¬ Disjoint (common G K F) {v | v ∈ Q₁} ∧
      ¬ Disjoint (common G K F) {v | v ∈ Q₂} := not_or.mp h
  exact hnres (h92.mpr ⟨hsat, Set.not_disjoint_iff.mp hn.1, Set.not_disjoint_iff.mp hn.2⟩)

end Workspace.ProofLemmas.Thm93CaseTwoCommon
