import Workspace.ProofLemmas.Thm93CaseOneLong
import Workspace.ProofLemmas.Thm93CaseOneShort
import Workspace.ProofLemmas.Thm93CaseOneClassify
import Workspace.ProofLemmas.Thm93CaseOneEnlarge
import Workspace.ProofLemmas.Thm93CaseOneOvershadow
import Workspace.Types.Overshadowed

/-! The branch dictionary needed to read 5.8 in a degenerate knot appearance. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm93CaseOneBranches
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure
open Workspace.ProofLemmas.Thm93CaseOneLong
open Workspace.ProofLemmas.Thm93CaseOneShort

/-- One of the two path branches, with either orientation. -/
abbrev LongBranchCase {V : Type*} (G : SimpleGraph V)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ : V) (K N₁ N₂ : Set V)
    (R : List V) (r₁ r₂ : V) : Prop :=
  ∃ (a b : V) (P P' : List V),
    ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
      (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
    LongSide G P a b K ({v | v ∈ P'} ∪ {v | v ∈ Q₁} ∪ {v | v ∈ Q₂}) N₁ N₂ ∧
    {v | v ∈ R} = {v | v ∈ P} ∧ r₁ = a ∧ r₂ = b

/-- One of the four cross edges, whose line-graph path has one vertex. -/
abbrev ShortBranchCase {V : Type*} (G : SimpleGraph V)
    (P₁ P₂ Q₁ Q₂ : List V) (x₁ y₁ x₂ y₂ : V) (K N₁ N₂ : Set V)
    (R : List V) (r₁ r₂ : V) : Prop :=
  ∃ (x y : V) (Q' : List V),
    ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
      (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)) ∧
    ShortSide G x y K ({v | v ∈ P₁} ∪ {v | v ∈ P₂} ∪ {v | v ∈ Q'}) N₁ N₂ ∧
    {v | v ∈ R} = {x} ∧ r₁ = x ∧ r₂ = x

/-- **Remaining branch identification gap.**
PAPER (9.3, printed pp. 48--49): *"In the notation of 5.8.2, the edge `b₁b₂` of `J` is of
one of two types; either `N_b₁` meets `N_b₂` or it does not."*

The six branches are the four edges of the named four-cycle and the two path branches.
The conclusion records their supports, end labels, and the neighbours in the other lists.
It contains no attachment path and no conclusion of 9.3. -/
theorem classify_branch_gap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hlen₁ : pathLength Q₁ = 1) (hlen₂ : pathLength Q₂ = 1)
    (hodd₁ : Odd (pathLength P₁)) (hodd₂ : Odd (pathLength P₂))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary G H K phi P₁ P₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
      c₁ c₂ c₃ c₄ N)
    (d₁ d₂ : Fin n) (q : List (Fin n)) (R : List V) (r₁ r₂ : V)
    (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H)
    (hq : IsBranch H q) (hqt : IsTrackFrom H q d₁ d₂) (hR : IsPathList G R)
    (hRset : {x | x ∈ R} = {x | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges q ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (hR₁ : N d₁ ∩ {x | x ∈ R} = {r₁}) (hR₂ : N d₂ ∩ {x | x ∈ R} = {r₂}) :
    LongBranchCase G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ K (N d₁) (N d₂) R r₁ r₂ ∨
    ShortBranchCase G P₁ P₂ Q₁ Q₂ x₁ y₁ x₂ y₂ K (N d₁) (N d₂) R r₁ r₂ :=
  Thm93CaseOneClassify.classify G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂
    hlen₁ hlen₂ hodd₁ hodd₂ K hK H phi happ c₁ c₂ c₃ c₄ N hdict d₁ d₂ q R r₁ r₂ hd₁ hd₂ hq hqt
    hR hRset hR₁ hR₂

/-- **Remaining enlargement construction gap.**
PAPER (9.3, printed p. 48): *"If 5.8.1 holds then there is an appearance in `G` of some
`K₄`-enlargement, a contradiction."*

Unlike the existing general enlargement helper, this statement concerns a degenerate
appearance. The attachment pattern is precisely 5.8.1. -/
theorem nonlocal_enlargement_gap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) {n : ℕ}
    (H : SimpleGraph (Fin n)) (K : Set V) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (hdeg : DegenerateK4Appearance H) (N : Fin n → Set V)
    (hN : ∀ c, N c = {v | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂)
    (d₁ d₂ : Fin n)
    (hnb : ¬ ∃ q, IsBranch H q ∧ d₁ ∈ q ∧ d₂ ∈ q)
    (h₁ : ∀ x ∈ N d₁, G.Adj p₁ x) (h₂ : ∀ x ∈ N d₂, G.Adj p₂ x)
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ y ∈ N d₁) ∨ (x = p₂ ∧ y ∈ N d₂)) :
    ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ Appears G J' :=
  Thm93CaseOneEnlarge.enlargement G hG H K phi happ N hN P p₁ p₂ hP d₁ d₂ hnb h₁ h₂ hno

/-- **Remaining even-path construction gap.**
PAPER (9.3, printed p. 49): *"there is a path `R` of `G` with `V(R) ⊆ F` and with ends
`r₁` and `r₂`, such that `r₁` is adjacent to `a₁,x₂`, and `r₂` is adjacent to `a₂,y₂`,
and there are no other edges between `V(R)` and `K\x₁` ... while if `R` has length > 0 then
it is even and there is an overshadowed appearance of `K₄` in `G`."*

Only the construction remains: all alternatives of 5.8 have already been reduced to this
single attachment pattern, and the path has positive even length. -/
theorem even_short_path_overshadowed_gap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) {n : ℕ}
    (H : SimpleGraph (Fin n)) (K : Set V) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (hdeg : DegenerateK4Appearance H) (N : Fin n → Set V)
    (hN : ∀ c, N c = {v | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (d₁ d₂ : Fin n) (q : List (Fin n)) (R : List V) (x : V)
    (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H)
    (hq : IsBranch H q) (hqt : IsTrackFrom H q d₁ d₂) (hR : IsPathList G R)
    (hRset : {v | v ∈ R} = {v | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges q ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (hR₁ : N d₁ ∩ {v | v ∈ R} = {x}) (hR₂ : N d₂ ∩ {v | v ∈ R} = {x})
    (hshort : {v | v ∈ R} = {x})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hne : p₁ ≠ p₂)
    (hfirst : ∀ v ∈ N d₁ \ {x}, G.Adj p₁ v)
    (hlast : ∀ v ∈ N d₂ \ {x}, G.Adj p₂ v)
    (hno : ∀ u ∈ P, ∀ v ∈ K, v ≠ x → G.Adj u v →
      (u = p₁ ∧ v ∈ N d₁ \ {x}) ∨ (u = p₂ ∧ v ∈ N d₂ \ {x}))
    (heven : Even (pathLength P)) :
    ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi :=
  Thm93CaseOneOvershadow.overshadowed G H K phi happ N hN d₁ d₂ q R x hd₁ hd₂ hqt hRset
    hR₁ hR₂ P p₁ p₂ hP hne hfirst hlast hno heven

/-- **Reduction of the positive-length short-branch case.**
PAPER (9.3, printed p. 49): *"while if `R` has length > 0 then it is even and there is an
overshadowed appearance of `K₄` in `G`, a contradiction."*

The branch has one line-graph vertex and the path supplied by 5.8 has distinct ends.
The zero-length case is proved in `singleton_endgame`; the two long branches are handled
by `long_branch`. -/
theorem positive_short_branch_overshadowed_gap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) {n : ℕ}
    (H : SimpleGraph (Fin n)) (K : Set V) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (hdeg : DegenerateK4Appearance H) (N : Fin n → Set V)
    (hN : ∀ c, N c = {v | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (d₁ d₂ : Fin n) (q : List (Fin n)) (R : List V) (x : V)
    (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H)
    (hq : IsBranch H q) (hqt : IsTrackFrom H q d₁ d₂) (hR : IsPathList G R)
    (hRset : {v | v ∈ R} = {v | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ trackEdges q ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (hR₁ : N d₁ ∩ {v | v ∈ R} = {x}) (hR₂ : N d₂ ∩ {v | v ∈ R} = {x})
    (hshort : {v | v ∈ R} = {x})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hne : p₁ ≠ p₂)
    (halt : BranchAlternatives G K (N d₁) (N d₂) R x x P p₁ p₂) :
    ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi  := by
  have hlenR : pathLength R = 0 := by
    have h := pathLength_eq_of_support (PathBasics.isPathList_singleton G x) hR
      (show {v | v ∈ R} = {v | v ∈ [x]} by simpa using hshort)
    exact h
  have heR : Even (pathLength R) := by simp [hlenR]
  have finish := even_short_path_overshadowed_gap G hG H K phi happ hdeg N hN
    d₁ d₂ q R x hd₁ hd₂ hq hqt hR hRset hR₁ hR₂ hshort P p₁ p₂ hP hne
  rcases halt with ⟨_, hhit, _⟩ | ⟨hfirst, hlast, hno, hpar⟩ | ⟨heq, _⟩ | ⟨_, hfirst, hlast, hno, heven⟩
  · obtain ⟨v, hv, _⟩ := hhit
    rw [hshort] at hv
    exact (hv.2 hv.1).elim
  · refine finish hfirst hlast ?_ (hpar.mpr heR)
    intro u hu v hv hvx hadj
    rcases hno u hu v hv hadj with h | h | h | h
    exacts [Or.inl h, Or.inr h, (hvx h.2).elim, (hvx h.2).elim]
  · exact (hne heq).elim
  · exact finish hfirst hlast hno heven

end Workspace.ProofLemmas.Thm93CaseOneBranches
