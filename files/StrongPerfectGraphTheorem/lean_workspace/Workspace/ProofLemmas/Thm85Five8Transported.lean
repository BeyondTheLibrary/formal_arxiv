import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.Statements.S05.Thm_5_8

/-!
# 5.8 for a graph `J` on an arbitrary finite vertex type

Statement 5.8 is transcribed with `J : SimpleGraph (Fin m)`, following the project convention
that *"there is a graph `X` such that …"* is `∃ (n : ℕ) (X : SimpleGraph (Fin n)), …`.  The
proof of 8.5, however, applies 5.8 three times (inside claims (2), (3) and (4)) to the graph `J`
of the ambient `J`-strip system, which lives on an arbitrary finite vertex type `U`.

The gap is purely bureaucratic: `J` occurs in 5.8 **only in the hypotheses** — through
`IsKConnected J 3` and `IsBipartiteSubdivision J H` — and not at all in the conclusion, which
speaks about `H`, `K`, `N`, `F` and `G` alone.  So it is enough to transport those two
hypotheses along an isomorphism `J ≃g J'` with `J'` on `Fin (Fintype.card U)`.

`k`-connectivity already transports (`SubdivisionCounting.isKConnected_of_iso`); being a
subdivision does not, so `isSubdivision_of_iso` below supplies it: re-index the embedding `ι`
and the family of tracks `T` of `Tracks.IsSubdivision` along `e.symm`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85Five8Transported

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- **Being a subdivision transports along an isomorphism of the subdivided graph.**

If `H` is a subdivision of `J` and `J ≃g J'`, then `H` is a subdivision of `J'`: re-index the
embedding `ι : V(J) → V(H)` and the family of tracks `T` along `e.symm`. -/
theorem isSubdivision_of_iso {U U' W : Type*} {J : SimpleGraph U} {J' : SimpleGraph U'}
    {H : SimpleGraph W} (e : J ≃g J') (h : IsSubdivision J H) : IsSubdivision J' H := by
  obtain ⟨ι, T, hinj, htrack, hlen, hrev, hdisj, hnotrange, hcover, hedges⟩ := h
  have hadj : ∀ a b : U', J'.Adj a b → J.Adj (e.symm a) (e.symm b) := by
    intro a b hab
    exact e.symm.map_rel_iff.mpr hab
  have hsymminj : Function.Injective (fun a : U' => e.symm a) := EquivLike.injective e.symm
  have hsym2 : ∀ a b c d : U', s(a, b) ≠ s(c, d) →
      s(e.symm a, e.symm b) ≠ s(e.symm c, e.symm d) := by
    intro a b c d hne heq
    refine hne ?_
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hsymminj h1, hsymminj h2]
    · rw [Sym2.eq_swap, hsymminj h1, hsymminj h2]
  refine ⟨fun a => ι (e.symm a), fun a b => T (e.symm a) (e.symm b), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact fun a b hab => hsymminj (hinj hab)
  · exact fun a b hab => htrack _ _ (hadj a b hab)
  · exact fun a b hab => hlen _ _ (hadj a b hab)
  · exact fun a b hab => hrev _ _ (hadj a b hab)
  · exact fun a b c d hab hcd hne =>
      hdisj _ _ _ _ (hadj a b hab) (hadj c d hcd) (hsym2 a b c d hne)
  · intro a b hab w hw
    intro hmem
    refine hnotrange _ _ (hadj a b hab) w hw ?_
    obtain ⟨a', ha'⟩ := hmem
    exact ⟨e.symm a', ha'⟩
  · intro w
    rcases hcover w with ⟨u, hu⟩ | ⟨u, v, huv, hw⟩
    · exact Or.inl ⟨e u, by simpa using hu⟩
    · exact Or.inr ⟨e u, e v, by simpa using e.map_rel_iff.mpr huv, by simpa using hw⟩
  · rw [hedges]
    ext f
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, v, huv, hf⟩
      exact ⟨e u, e v, e.map_rel_iff.mpr huv, by simpa using hf⟩
    · rintro ⟨a, b, hab, hf⟩
      exact ⟨e.symm a, e.symm b, hadj a b hab, hf⟩

/-- **5.8 for `J` on an arbitrary finite vertex type.**

The statement is that of `Workspace.Statements.S05.SPGT.thm_5_8` verbatim — only the vertex
type of `J` has been relaxed from `Fin m` to an arbitrary `U` with `[Fintype U]`. -/
theorem thm85Five8Transported {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (F : Set V) (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hnotlocal : ¬ LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K})
    (hnomajor : ∀ x ∈ F, ¬ MajorForLineGraph G H K φ x) :
    ∃ (P : List V) (p₁ p₂ : V), IsPathFrom G P p₁ p₂ ∧ (∀ x ∈ P, x ∈ F) ∧
      ((∃ c₁ c₂ : Fin n,
          (¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
          (∀ x ∈ N c₁, G.Adj p₁ x) ∧ (∀ x ∈ N c₂, G.Adj p₂ x) ∧
          (∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ N c₁) ∨ (x = p₂ ∧ y ∈ N c₂))) ∨
       (∃ (b₁ b₂ : Fin n) (q : List (Fin n)) (R : List V) (r₁ r₂ : V),
          b₁ ∈ branchVertices H ∧ b₂ ∈ branchVertices H ∧
          IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
          IsPathList G R ∧
          {x : V | x ∈ R} =
            {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
              e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)} ∧
          N b₁ ∩ {x : V | x ∈ R} = {r₁} ∧ N b₂ ∩ {x : V | x ∈ R} = {r₂} ∧
          (((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧
            (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
           ((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂}) ∨
              (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
            (Even (pathLength P) ↔ Even (pathLength R))) ∨
           (p₁ = p₂ ∧ (∀ x ∈ (N b₁ ∪ N b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
            (∀ y ∈ K, G.Adj p₁ y → y ∈ N b₁ ∪ N b₂ ∪ {z : V | z ∈ R}) ∧
            Even (pathLength R)) ∨
           (r₁ = r₂ ∧ (∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂})) ∧
            Even (pathLength P))))) := by
  obtain ⟨J', ⟨e⟩⟩ := IsoTransport.exists_iso_fin J
  exact Workspace.Statements.S05.SPGT.thm_5_8 G hG (Fintype.card U) J'
    (SubdivisionCounting.isKConnected_of_iso e hJ) n H K
    ⟨isSubdivision_of_iso e hsub.1, hsub.2⟩ φ N hN F hFK hFconn hnotlocal hnomajor

end Workspace.ProofLemmas.Thm85Five8Transported
