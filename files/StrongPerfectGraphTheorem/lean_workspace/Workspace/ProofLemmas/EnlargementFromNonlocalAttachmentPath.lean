import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
import Workspace.ProofLemmas.EnlargementFromNonlocalStructure
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Building a `J`-enlargement out of a non-local attachment path

## What this is

The hypotheses below are *literally* outcome 1 of 5.8: a path `P` of `G` with ends `p₁, p₂`,
disjoint from the appearance `K = V(L(H))`, having no attachments in `K` other than
`N_H(c₁) ⊆ N(p₁)` and `N_H(c₂) ⊆ N(p₂)` for two vertices `c₁, c₂` of `H` that do **not** lie on
a common branch.  (`Nc c` is the set of vertices of `G` carried by the edges of `H` at `c`, i.e.
the clique of `L(H)` attached to `c`; `hN` pins that down through the isomorphism `φ`.)

The conclusion is the printed sentence that follows:

> *"Then there is an appearance `L(H')` in `G` of some `J`-enlargement `J'`, with `L(H)` an
> induced subgraph of `L(H')`.  Moreover, if `J' = K₃,₃` then `J = K₄`, and so `L(H)` is
> nondegenerate and therefore so is `L(H')`."*

The degeneracy tail of that sentence is carried by the hypothesis `hnd` (*if `J` is `K₄` then
the appearance is nondegenerate*) and by the `NondegenerateAppearance J' H'` conjunct of the
conclusion.

## No printed proof exists

**The paper prints no proof of this construction anywhere.**  It makes exactly the same
unjustified move three times:

* in the proof of 5.4 — `paper/perfect_pdf.txt` line 1755;
* again at `paper/perfect_pdf.txt` line 2056;
* and in §9 — `paper/perfect_pdf.txt` line 2344.

Each time the enlargement `J'` and the subdivision `H'` are simply asserted to exist.

Consequently, per `PROVER_TASK.md` §1 (*"If the paper says 'the proof is clear' / 'we omit it',
there is no printed argument, so **any correct proof is acceptable** — say so explicitly in your
report"*), whoever proves this lemma is **under the "any correct proof is acceptable"
allowance**: the usual project rule *reproduce the paper's own proof, never invent one* cannot
bind here, because there is no paper proof to reproduce.  The prover must still say so
explicitly in its report.

## Why it matters

This construction is the common bottleneck of the §8.5 lane: claims (2), (3) and (4) of the
printed proof of 8.5 all stall on it, as do `Thm75Claim2`, the `Thm84*` nodes, claim (1) of 8.6
and `Thm83MixedRungs`.  `PROVING_NOTES.md` already records it as the project bottleneck.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

private theorem nondegenerateAppearance_map {A B X : Type*} {J : SimpleGraph X}
    {H : SimpleGraph A} {H' : SimpleGraph B} (ψ : H ≃g H')
    (h : NondegenerateAppearance J H) : NondegenerateAppearance J H' := by
  intro hdeg
  apply h
  rcases hdeg with ⟨hk4, hd⟩ | ⟨hnk4, hk33, ⟨iso⟩⟩
  · exact Or.inl ⟨hk4,
      Workspace.ProofLemmas.SubdivisionCounting.degenerateK4Appearance_of_iso ψ.symm hd⟩
  · exact Or.inr ⟨hnk4, hk33, ⟨ψ.trans iso⟩⟩

/-- **Outcome 1 of 5.8 produces a `J`-enlargement with a nondegenerate appearance.**

`P` is a path of `G` off the appearance `K`, whose only attachments in `K` are the cliques
`Nc c₁` (complete to the end `p₁`) and `Nc c₂` (complete to the end `p₂`), for two vertices
`c₁, c₂` of `H` lying on no common branch.  Then `G` contains an appearance of some
`J`-enlargement `J'`, and that appearance is nondegenerate. -/
theorem enlargementFromNonlocalAttachmentPath {V : Type*} [Fintype V] [DecidableEq V]
    {U : Type*} [Fintype U] (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (happ : IsAppearance G J H K) (φ : H.lineGraph ≃g G.induce K)
    (Nc : Fin n → Set V)
    (hN : ∀ c : Fin n, Nc c = {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPK : ∀ x ∈ P, x ∉ K)
    (c₁ c₂ : Fin n) (hnb : ¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (h₁ : ∀ x ∈ Nc c₁, G.Adj p₁ x) (h₂ : ∀ x ∈ Nc c₂, G.Adj p₂ x)
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ Nc c₁) ∨ (x = p₂ ∧ y ∈ Nc c₂))
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H) :
    ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H' := by
  classical
  have hc :=
    Workspace.ProofLemmas.EnlargementFromNonlocalStructure.ne_and_not_adj_of_no_common_branch
      J hJ H happ.1.1 c₁ c₂ hnb
  have h₁' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₁ ∈ e →
      G.Adj p₁ (↑(φ ⟨e, he⟩) : V) := by
    intro e he hce
    apply h₁
    rw [hN c₁]
    exact ⟨e, he, ⟨he, hce⟩, rfl⟩
  have h₂' : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₂ ∈ e →
      G.Adj p₂ (↑(φ ⟨e, he⟩) : V) := by
    intro e he hce
    apply h₂
    rw [hN c₂]
    exact ⟨e, he, ⟨he, hce⟩, rfl⟩
  have hno' : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₁ ∈ e ∧
        y = (↑(φ ⟨e, he⟩) : V)) ∨
      (x = p₂ ∧ ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), c₂ ∈ e ∧
        y = (↑(φ ⟨e, he⟩) : V)) := by
    intro x hx y hy hxy
    rcases hno x hx y hy hxy with h | h
    · left
      refine ⟨h.1, ?_⟩
      rw [hN c₁] at h
      obtain ⟨e, he, hinc, hval⟩ := h.2
      exact ⟨e, he, hinc.2, hval⟩
    · right
      refine ⟨h.1, ?_⟩
      rw [hN c₂] at h
      obtain ⟨e, he, hinc, hval⟩ := h.2
      exact ⟨e, he, hinc.2, hval⟩
  obtain ⟨D, q, ψ, hext, hqlen⟩ :=
    Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack.addTrack
      G H K φ P p₁ p₂ hP hPK c₁ c₂ hc.1 hc.2 h₁' h₂' hno'
  obtain ⟨m, J', henl, hDsub, hclass⟩ :=
    Workspace.ProofLemmas.EnlargementFromNonlocalStructure.promotedChordEnlargement
      J hJ H happ.1.1 c₁ c₂ hnb D Sum.inl q hext
  have hbip : D.IsBipartite :=
    Workspace.ProofLemmas.EnlargementFromNonlocalStructure.branchExtensionBipartite
      G hG J hJ H happ.1 c₁ c₂ hnb D Sum.inl q hext
        (K ∪ {x : V | x ∈ P}) ψ
  have hnondeg : NondegenerateAppearance J' D :=
    Workspace.ProofLemmas.EnlargementFromNonlocalStructure.branchExtensionNondegenerate
      J hJ H happ.1.1 c₁ c₂ hnb D Sum.inl q hext J' henl hDsub hclass hnd
  let e := Fintype.equivFin (Fin n ⊕ Fin (P.length - 1))
  let H' : SimpleGraph (Fin (Fintype.card (Fin n ⊕ Fin (P.length - 1)))) :=
    D.map e.toEmbedding
  let θ : D ≃g H' := SimpleGraph.Iso.map e D
  refine ⟨m, J', henl, Fintype.card (Fin n ⊕ Fin (P.length - 1)), H',
    K ∪ {x : V | x ∈ P}, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Workspace.ProofLemmas.SubdivisionCounting.isSubdivision_of_iso θ hDsub
    · exact SimpleGraph.Colorable.of_hom θ.symm.toHom hbip
    · exact ⟨θ.lineGraph.symm.trans ψ⟩
  · exact nondegenerateAppearance_map θ hnondeg

end Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath
