import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed

/-!
# The five-bullet conclusion of 6.1, as a single predicate

The printed proof of 6.1 (Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph
Theorem*, printed pp. 28–33) says "the theorem holds" thirteen times, in thirteen different
places.  To be able to state the intermediate claims of that proof — each of which ends in
"the theorem holds" — we give the disjunction of the five printed outcomes a name.

`Thm61Concl G m J n H K φ Y` is **byte-for-byte the conclusion of `thm_6_1`**
(`Workspace.Statements.S06.SPGT.thm_6_1`); the only difference is that the parameters have been
abstracted, so it can be used as the conclusion of the auxiliary lemmas of §6.

The one lemma proved here is the monotonicity of the conclusion in `Y`: only the fifth outcome
mentions `Y` at all, and it mentions it positively (*"there exist nonadjacent `y, y' ∈ Y`"*), so
enlarging `Y` preserves the conclusion.  This is exactly what licenses the paper's opening
reduction *"we may assume that `Y` is minimal such that it is anticonnected and its common
neighbours do not saturate `L(H)`"*: the argument is run with a minimal `Y₀ ⊆ Y` and the
conclusion is then transported back up to the given `Y`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61Conclusion

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT

/-- The conclusion of 6.1: the disjunction of the five printed outcomes.

*• `J = K₃,₃` or `K₄`, and there is an overshadowed appearance of `J` in `G`, or*

*• `J = K₃,₃` or `K₄`, `L(H)` is degenerate, and there is an overshadowed appearance of `J` in
`Ḡ`, or*

*• `J = K₃,₃`, `L(H)` is degenerate, and there is a `J`-enlargement that appears in `Ḡ`, or*

*• `J = K₄` and `|V(H)| = 6`, or*

*• `J = K₄` and `L(H)` is degenerate, and there exist nonadjacent `y, y' ∈ Y` with the
[printed] property.* -/
def Thm61Concl {V : Type*} (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) : Prop :=
  ((Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
      Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4)))) ∧
    (∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
        (φ' : H'.lineGraph ≃g G.induce K'),
      IsAppearance G J H' K' ∧ IsOvershadowedAppearance G H' K' φ')) ∨
  ((Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
      Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4)))) ∧
    DegenerateAppearance J H ∧
    (∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
        (φ' : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ J H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' φ')) ∨
  (Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
    DegenerateAppearance J H ∧
    (∃ (m' : ℕ) (J' : SimpleGraph (Fin m')), IsJEnlargement J J' ∧ Appears Gᶜ J')) ∨
  (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ Fintype.card (Fin n) = 6) ∨
  (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ DegenerateAppearance J H ∧
    ∃ y ∈ Y, ∃ y' ∈ Y, ¬ G.Adj y y' ∧
      ∃ (v₁ v₂ v₃ v₄ : Fin n) (a b c d p q r s : Sym2 (Fin n)),
        [v₁, v₂, v₃, v₄].Nodup ∧
        branchVertices H = ({v₁, v₂, v₃, v₄} : Set (Fin n)) ∧
        H.Adj v₁ v₂ ∧ H.Adj v₂ v₃ ∧ H.Adj v₃ v₄ ∧ H.Adj v₄ v₁ ∧
        a = s(v₁, v₂) ∧ b = s(v₂, v₃) ∧ c = s(v₃, v₄) ∧ d = s(v₄, v₁) ∧
        p ∈ incidentEdges H v₂ ∧ p ≠ a ∧ p ≠ b ∧
        q ∈ incidentEdges H v₃ ∧ q ≠ b ∧ q ≠ c ∧
        r ∈ incidentEdges H v₄ ∧ r ≠ c ∧ r ≠ d ∧
        s ∈ incidentEdges H v₁ ∧ s ≠ d ∧ s ≠ a ∧
        ({a, b, d, q, r} : Set (Sym2 (Fin n))) ⊆
          {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj y (↑(φ ⟨e, he⟩) : V)} ∧
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj y (↑(φ ⟨e, he⟩) : V)} ⊆
          ({a, b, c, d, q, r} : Set (Sym2 (Fin n))) ∧
        ({b, c, d, p, s} : Set (Sym2 (Fin n))) ⊆
          {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj y' (↑(φ ⟨e, he⟩) : V)} ∧
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj y' (↑(φ ⟨e, he⟩) : V)} ⊆
          ({a, b, c, d, p, s} : Set (Sym2 (Fin n))))

/-- **The conclusion of 6.1 is monotone in `Y`.**

Only the fifth outcome mentions `Y`, and only through *"there exist nonadjacent `y, y' ∈ Y`"*.
Hence a proof of the conclusion for a subset `Y₀ ⊆ Y` is a proof of the conclusion for `Y`.

This is what makes the paper's first sentence — *"We may assume that `Y` is minimal such that it
is anticonnected and its common neighbours do not saturate `L(H)`"* — a legitimate reduction. -/
theorem Thm61Concl_mono {V : Type*} (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y₀ Y : Set V) (hsub : Y₀ ⊆ Y)
    (h : Thm61Concl G m J n H K φ Y₀) : Thm61Concl G m J n H K φ Y := by
  rcases h with h | h | h | h | ⟨hJ, hdeg, y, hy, y', hy', hrest⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hJ, hdeg, y, hsub hy, y', hsub hy', hrest⟩)))

end Workspace.ProofLemmas.Thm61Conclusion
