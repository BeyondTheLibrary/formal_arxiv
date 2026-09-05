import Workspace.ProofLemmas.Thm93CaseOneLong
import Workspace.ProofLemmas.Thm93CaseOneShort
import Workspace.ProofLemmas.Thm93CaseOneBranchPair
import Workspace.ProofLemmas.Thm93CaseOneKnotFacts
import Workspace.ProofLemmas.BranchClassification

/-!
# The six branches of the degenerate appearance carried by a knot

PAPER (9.3, printed p. 48): *"In the notation of 5.8.2, the edge `b₁b₂` of `J` is of one of two
types; either `N_b₁` meets `N_b₂` or it does not."*

`H` is a bipartite subdivision of `K₄`, so it has exactly six branches, one for each edge of
`K₄`.  The dictionary supplied by `Thm93Infrastructure.KnotAppearanceDictionary` names the four
branch-vertices `c₁, c₂, c₃, c₄`, says that `c₁c₂, c₂c₃, c₃c₄, c₄c₁` are edges of `H` carrying
the four cross vertices `x₁, y₂, y₁, x₂` of the knot, and identifies the two remaining branches
— those joining `c₁` to `c₃` and `c₂` to `c₄` — with the two paths `P₁` and `P₂`.

So a branch is determined by its pair of ends, and this module reads off, for each of the six
pairs, the vertex set of the corresponding path of `G`, the two ends named by 5.8.2, and the
neighbours of those ends in the rest of the knot.  The four one-edge branches produce
`Thm93CaseOneShort.ShortSide`, the two long ones `Thm93CaseOneLong.LongSide`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93CaseOneClassify

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure
open Workspace.ProofLemmas.Thm93CaseOneLong
open Workspace.ProofLemmas.Thm93CaseOneShort
open Workspace.ProofLemmas.Thm93CaseOneKnotFacts

/-- A track with two distinct ends has at least two vertices. -/
theorem two_le_length_of_ends_ne {W : Type*} {H : SimpleGraph W} {q : List W} {u v : W}
    (h : IsTrackFrom H q u v) (huv : u ≠ v) : 2 ≤ q.length := by
  by_contra hc
  have h0 : 0 < q.length := by
    rcases q with _ | ⟨a, l⟩
    · exact absurd rfl h.1.1
    · simp
  have h1 : q.length = 1 := by omega
  have e0 : q[0]'h0 = u := SubdivisionCounting.track_head h h0
  have e1 : q[q.length - 1]'(by omega) = v :=
    Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast h h0
  apply huv
  rw [← e0, ← e1]
  exact (SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _).symm

/-- The ends of a track with at least two vertices are distinct. -/
theorem ends_ne_of_two_le_length {W : Type*} {H : SimpleGraph W} {q : List W} {u v : W}
    (h : IsTrackFrom H q u v) (hlen : 2 ≤ q.length) : u ≠ v := by
  have h0 : 0 < q.length := by omega
  have e0 : q[0]'h0 = u := SubdivisionCounting.track_head h h0
  have e1 : q[q.length - 1]'(by omega) = v :=
    Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast h h0
  rw [← e0, ← e1]
  intro hc
  have := (List.Nodup.getElem_inj_iff h.1.2.1).mp hc
  omega


/-- **The branch dictionary of case (1) of 9.3.**

PAPER (9.3, printed p. 48): *"In the notation of 5.8.2, the edge `b₁b₂` of `J` is of one of two
types."*  The six branches of `H` are the four edges of the four-cycle `c₁c₂c₃c₄` and the two
tracks carrying `P₁` and `P₂`; the conclusion records, for the branch supplied by 5.8.2, which
of the six it is, its support in `G`, and the neighbours of its two ends. -/
theorem classify {V : Type*} [Fintype V] [DecidableEq V]
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
    (∃ (a b : V) (P P' : List V),
      ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
        (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
      LongSide G P a b K ({v | v ∈ P'} ∪ {v | v ∈ Q₁} ∪ {v | v ∈ Q₂}) (N d₁) (N d₂) ∧
      {v | v ∈ R} = {v | v ∈ P} ∧ r₁ = a ∧ r₂ = b) ∨
    (∃ (x y : V) (Q' : List V),
      ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
        (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)) ∧
      ShortSide G x y K ({v | v ∈ P₁} ∪ {v | v ∈ P₂} ∪ {v | v ∈ Q'}) (N d₁) (N d₂) ∧
      {v | v ∈ R} = {x} ∧ r₁ = x ∧ r₂ = x) := by
  classical
  obtain ⟨hN, hnodup, h12, h23, h34, h41, hbv, hex12, hex23, hex34, hex41,
    hNc₁, hNc₂, hNc₃, hNc₄, hbrA, hbrB⟩ := hdict
  have hs : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ :=
    ⟨hknot, hP₁, hP₂, hQ₁, hQ₂, hlen₁, hlen₂⟩
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisjint, hnew, hcover, hedges⟩ := happ.1.1
  have hdegJ := SubdivisionCounting.three_le_degree_of_three_connected
    (⊤ : SimpleGraph (Fin 4)) SubdivisionCounting.k4_three_connected
  -- two branches with the same ends have the same edges
  have hsame : ∀ (qa q' : List (Fin n)) (e₁ e₂ f₁ f₂ : Fin n),
      IsBranch H qa → IsTrackFrom H qa e₁ e₂ → IsBranch H q' → IsTrackFrom H q' f₁ f₂ →
      e₁ ∈ branchVertices H → e₂ ∈ branchVertices H → e₁ ≠ e₂ →
      ((f₁ = e₁ ∧ f₂ = e₂) ∨ (f₁ = e₂ ∧ f₂ = e₁)) →
      trackEdges qa = trackEdges q' := by
    intro qa q' e₁ e₂ f₁ f₂ hba hta hbq htq he₁ he₂ hne hmatch
    have hfne : f₁ ≠ f₂ := by rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hne, hne.symm]
    exact BranchClassification.trackEdges_eq_of_same_ends hι htrack hlenT hrev hdisjint hnew
      hcover hedges hdegJ hba (two_le_length_of_ends_ne hta hne) hta hbq
      (two_le_length_of_ends_ne htq hfne) htq he₁ he₂ hmatch
  -- the vertex set of `R` only depends on the edge set of the branch
  have himg : ∀ q' : List (Fin n), trackEdges q = trackEdges q' →
      {v : V | v ∈ R} = {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q' ∧ v = (↑(phi ⟨e, he⟩) : V)} := by
    intro q' h
    rw [hRset, h]
  -- a one-edge branch carries a single vertex of `G`
  have himgPair : ∀ (u v : Fin n) (huv : H.Adj u v) (w : V),
      (∃ he : s(u, v) ∈ H.edgeSet, (↑(phi ⟨s(u, v), he⟩) : V) = w) →
      {v' : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges [u, v] ∧ v' = (↑(phi ⟨e, he⟩) : V)} = {w} := by
    intro u v huv w hw
    obtain ⟨he, hval⟩ := hw
    rw [Thm93CaseOneBranchPair.trackEdges_pair]
    ext v'
    constructor
    · rintro ⟨e, he', hmem, rfl⟩
      simp only [Set.mem_singleton_iff] at hmem
      subst hmem
      exact hval
    · rintro rfl
      exact ⟨s(u, v), he, rfl, hval.symm⟩
  -- the branch has at least one edge, so its ends are distinct
  have hqlen : 2 ≤ q.length := by
    obtain ⟨v, hv⟩ : ∃ v, v ∈ R := List.exists_mem_of_ne_nil R hR.1
    have : v ∈ {v : V | v ∈ R} := hv
    rw [hRset] at this
    obtain ⟨e, -, ⟨i, hi, -⟩, -⟩ := this
    omega
  have hdne : d₁ ≠ d₂ := ends_ne_of_two_le_length hqt hqlen
  -- the four branch-vertices
  have hcmem : ∀ z : Fin n, z ∈ branchVertices H → c₁ = z ∨ c₂ = z ∨ c₃ = z ∨ c₄ = z := by
    intro z hz
    rw [hbv] at hz
    have : z = c₁ ∨ z = c₂ ∨ z = c₃ ∨ z = c₄ := by simpa using hz
    rcases this with h | h | h | h
    exacts [Or.inl h.symm, Or.inr (Or.inl h.symm), Or.inr (Or.inr (Or.inl h.symm)),
      Or.inr (Or.inr (Or.inr h.symm))]
  have hb₁ : c₁ ∈ branchVertices H := by rw [hbv]; simp
  have hb₂ : c₂ ∈ branchVertices H := by rw [hbv]; simp
  have hb₃ : c₃ ∈ branchVertices H := by rw [hbv]; simp
  have hb₄ : c₄ ∈ branchVertices H := by rw [hbv]; simp
  -- reading the support of `R` off a one-edge branch
  have hRshort : ∀ (u v : Fin n) (huv : H.Adj u v) (w : V),
      (∃ he : s(u, v) ∈ H.edgeSet, (↑(phi ⟨s(u, v), he⟩) : V) = w) →
      u ∈ branchVertices H → v ∈ branchVertices H →
      ((d₁ = u ∧ d₂ = v) ∨ (d₁ = v ∧ d₂ = u)) → {v' : V | v' ∈ R} = {w} := by
    intro u v huv w hw hu hv hmatch
    have hmatch' : (u = d₁ ∧ v = d₂) ∨ (u = d₂ ∧ v = d₁) := by
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      exacts [Or.inl ⟨h1.symm, h2.symm⟩, Or.inr ⟨h2.symm, h1.symm⟩]
    have heq := hsame q [u, v] d₁ d₂ u v hq hqt
      (Thm93CaseOneBranchPair.isBranch_pair huv hu hv)
      (Thm93CaseOneBranchPair.isTrackFrom_pair huv) hd₁ hd₂ hdne hmatch'
    rw [himg [u, v] heq]
    exact himgPair u v huv w hw
  -- reading the support of `R` off a long branch
  have hRlong : ∀ (qa : List (Fin n)) (u v : Fin n) (Pl : List V),
      IsBranch H qa → IsTrackFrom H qa u v →
      {v' : V | v' ∈ Pl} = {v' : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges qa ∧ v' = (↑(phi ⟨e, he⟩) : V)} →
      ((d₁ = u ∧ d₂ = v) ∨ (d₁ = v ∧ d₂ = u)) → {v' : V | v' ∈ R} = {v' : V | v' ∈ Pl} := by
    intro qa u v Pl hba hta hPl hmatch
    have hmatch' : (u = d₁ ∧ v = d₂) ∨ (u = d₂ ∧ v = d₁) := by
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      exacts [Or.inl ⟨h1.symm, h2.symm⟩, Or.inr ⟨h2.symm, h1.symm⟩]
    have heq := hsame q qa d₁ d₂ u v hq hqt hba hta hd₁ hd₂ hdne hmatch'
    rw [himg qa heq, hPl]
  -- naming the end of `R` in a neighbourhood
  have hsingle : ∀ (u : Fin n) (w z : V), N u ∩ {v : V | v ∈ R} = {z} →
      {v : V | v ∈ R} = {w} → w ∈ N u → z = w := by
    intro u w z h1 h2 hw
    have h3 : N u ∩ {v : V | v ∈ R} = {w} := by
      rw [h2]
      ext t
      exact ⟨fun ht => ht.2, fun ht => ⟨by rw [show t = w from ht]; exact hw, ht⟩⟩
    exact Set.singleton_eq_singleton_iff.mp (h1.symm.trans h3)
  have hsingleP : ∀ (u : Fin n) (w z : V) (Pl : List V), N u ∩ {v : V | v ∈ R} = {z} →
      {v : V | v ∈ R} = {v : V | v ∈ Pl} → N u ∩ {v : V | v ∈ Pl} = {w} → z = w := by
    intro u w z Pl h1 h2 h3
    rw [h2] at h1
    exact Set.singleton_eq_singleton_iff.mp (h1.symm.trans h3)
  -- the knot's disjointness, membership and distinctness facts
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hs.disj
  have nax₁ : a₁ ≠ x₁ := hs.ne_p_q (Or.inl hs.a₁_mem) (Or.inl hs.x₁_mem)
  have nay₁ : a₁ ≠ y₁ := hs.ne_p_q (Or.inl hs.a₁_mem) (Or.inl hs.y₁_mem)
  have nax₂ : a₁ ≠ x₂ := hs.ne_p_q (Or.inl hs.a₁_mem) (Or.inr hs.x₂_mem)
  have nay₂ : a₁ ≠ y₂ := hs.ne_p_q (Or.inl hs.a₁_mem) (Or.inr hs.y₂_mem)
  have nbx₁ : b₁ ≠ x₁ := hs.ne_p_q (Or.inl hs.b₁_mem) (Or.inl hs.x₁_mem)
  have nby₁ : b₁ ≠ y₁ := hs.ne_p_q (Or.inl hs.b₁_mem) (Or.inl hs.y₁_mem)
  have nbx₂ : b₁ ≠ x₂ := hs.ne_p_q (Or.inl hs.b₁_mem) (Or.inr hs.x₂_mem)
  have nby₂ : b₁ ≠ y₂ := hs.ne_p_q (Or.inl hs.b₁_mem) (Or.inr hs.y₂_mem)
  have ncx₁ : a₂ ≠ x₁ := hs.ne_p_q (Or.inr hs.a₂_mem) (Or.inl hs.x₁_mem)
  have ncy₁ : a₂ ≠ y₁ := hs.ne_p_q (Or.inr hs.a₂_mem) (Or.inl hs.y₁_mem)
  have ncx₂ : a₂ ≠ x₂ := hs.ne_p_q (Or.inr hs.a₂_mem) (Or.inr hs.x₂_mem)
  have ncy₂ : a₂ ≠ y₂ := hs.ne_p_q (Or.inr hs.a₂_mem) (Or.inr hs.y₂_mem)
  have ndx₁ : b₂ ≠ x₁ := hs.ne_p_q (Or.inr hs.b₂_mem) (Or.inl hs.x₁_mem)
  have ndy₁ : b₂ ≠ y₁ := hs.ne_p_q (Or.inr hs.b₂_mem) (Or.inl hs.y₁_mem)
  have ndx₂ : b₂ ≠ x₂ := hs.ne_p_q (Or.inr hs.b₂_mem) (Or.inr hs.x₂_mem)
  have ndy₂ : b₂ ≠ y₂ := hs.ne_p_q (Or.inr hs.b₂_mem) (Or.inr hs.y₂_mem)
  have nqx : x₁ ≠ x₂ := hs.ne_q₁_q₂ hs.x₁_mem hs.x₂_mem
  have nqy : x₁ ≠ y₂ := hs.ne_q₁_q₂ hs.x₁_mem hs.y₂_mem
  have nyx : y₁ ≠ x₂ := hs.ne_q₁_q₂ hs.y₁_mem hs.x₂_mem
  have nyy : y₁ ≠ y₂ := hs.ne_q₁_q₂ hs.y₁_mem hs.y₂_mem
  have nxy₁ : x₁ ≠ y₁ := hs.x₁_ne_y₁
  have nxy₂ : x₂ ≠ y₂ := hs.x₂_ne_y₂
  have nab₁ : a₁ ≠ b₁ := hs.a₁_ne_b₁
  have nab₂ : a₂ ≠ b₂ := hs.a₂_ne_b₂
  -- memberships in `K`
  have hmemK : ∀ v : V, (v ∈ P₁ ∨ v ∈ P₂ ∨ v ∈ Q₁ ∨ v ∈ Q₂) → v ∈ K := by
    intro v hv
    rw [hK]
    rcases hv with h | h | h | h
    exacts [Or.inl (Or.inl (Or.inl h)), Or.inl (Or.inl (Or.inr h)), Or.inl (Or.inr h), Or.inr h]
  have hSAsub : (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂}) : Set V) ⊆ K := by
    rintro v ((h | h) | h)
    exacts [hmemK v (Or.inl h), hmemK v (Or.inr (Or.inl h)),
      hmemK v (Or.inr (Or.inr (Or.inr h)))]
  have hSBsub : (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁}) : Set V) ⊆ K := by
    rintro v ((h | h) | h)
    exacts [hmemK v (Or.inl h), hmemK v (Or.inr (Or.inl h)),
      hmemK v (Or.inr (Or.inr (Or.inl h)))]
  have hx₁SA : x₁ ∉ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂}) : Set V) := by
    rintro ((h | h) | h)
    exacts [d2 x₁ h hs.x₁_mem, d4 x₁ h hs.x₁_mem, d6 x₁ hs.x₁_mem h]
  have hy₁SA : y₁ ∉ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂}) : Set V) := by
    rintro ((h | h) | h)
    exacts [d2 y₁ h hs.y₁_mem, d4 y₁ h hs.y₁_mem, d6 y₁ hs.y₁_mem h]
  have hx₂SB : x₂ ∉ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁}) : Set V) := by
    rintro ((h | h) | h)
    exacts [d3 x₂ h hs.x₂_mem, d5 x₂ h hs.x₂_mem, d6 x₂ h hs.x₂_mem]
  have hy₂SB : y₂ ∉ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁}) : Set V) := by
    rintro ((h | h) | h)
    exacts [d3 y₂ h hs.y₂_mem, d5 y₂ h hs.y₂_mem, d6 y₂ h hs.y₂_mem]
  -- the two covers and the two disjointness statements for the long branches
  have hcov₁ : K = {v : V | v ∈ P₁} ∪
      (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) := by
    rw [hK]; ext v; simp only [Set.mem_union]; tauto
  have hcov₂ : K = {v : V | v ∈ P₂} ∪
      (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) := by
    rw [hK]; ext v; simp only [Set.mem_union]; tauto
  have hdis₁ : Disjoint ({v : V | v ∈ P₁} : Set V)
      (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) := by
    rw [Set.disjoint_left]
    rintro v hv ((h | h) | h)
    exacts [d1 v hv h, d2 v hv h, d3 v hv h]
  have hdis₂ : Disjoint ({v : V | v ∈ P₂} : Set V)
      (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) := by
    rw [Set.disjoint_left]
    rintro v hv ((h | h) | h)
    exacts [d1 v h hv, d4 v hv h, d5 v hv h]
  -- the four `LongSide` packages
  have hfa₁ : N c₁ \ {a₁} = {w ∈ (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) | G.Adj a₁ w} := by
    rw [hNc₁, hs.nbrs_a₁]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hne⟩
      exacts [Or.inl rfl, Or.inr rfl, absurd rfl hne]
    · rintro (rfl | rfl)
      exacts [⟨Or.inl rfl, fun h => nax₁ (by simpa using h.symm)⟩,
        ⟨Or.inr (Or.inl rfl), fun h => nax₂ (by simpa using h.symm)⟩]
  have hfb₁ : N c₃ \ {b₁} = {w ∈ (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) | G.Adj b₁ w} := by
    rw [hNc₃, hs.nbrs_b₁]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hne⟩
      exacts [Or.inl rfl, Or.inr rfl, absurd rfl hne]
    · rintro (rfl | rfl)
      exacts [⟨Or.inl rfl, fun h => nby₁ (by simpa using h.symm)⟩,
        ⟨Or.inr (Or.inl rfl), fun h => nby₂ (by simpa using h.symm)⟩]
  have hfa₂ : N c₂ \ {a₂} = {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) | G.Adj a₂ w} := by
    rw [hNc₂, hs.nbrs_a₂]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hne⟩
      exacts [Or.inl rfl, Or.inr rfl, absurd rfl hne]
    · rintro (rfl | rfl)
      exacts [⟨Or.inl rfl, fun h => ncx₁ (by simpa using h.symm)⟩,
        ⟨Or.inr (Or.inl rfl), fun h => ncy₂ (by simpa using h.symm)⟩]
  have hfb₂ : N c₄ \ {b₂} = {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) | G.Adj b₂ w} := by
    rw [hNc₄, hs.nbrs_b₂]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hne⟩
      exacts [Or.inl rfl, Or.inr rfl, absurd rfl hne]
    · rintro (rfl | rfl)
      exacts [⟨Or.inl rfl, fun h => ndy₁ (by simpa using h.symm)⟩,
        ⟨Or.inr (Or.inl rfl), fun h => ndx₂ (by simpa using h.symm)⟩]
  have LS1 : LongSide G P₁ a₁ b₁ K (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₁) (N c₃) :=
    ⟨hP₁.1, hodd₁, hs.a₁_mem, hs.b₁_mem, nab₁, hcov₁, hdis₁, hfa₁, hfb₁⟩
  have LS2 : LongSide G P₁ b₁ a₁ K (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₃) (N c₁) :=
    ⟨hP₁.1, hodd₁, hs.b₁_mem, hs.a₁_mem, nab₁.symm, hcov₁, hdis₁, hfb₁, hfa₁⟩
  have LS3 : LongSide G P₂ a₂ b₂ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₂) (N c₄) :=
    ⟨hP₂.1, hodd₂, hs.a₂_mem, hs.b₂_mem, nab₂, hcov₂, hdis₂, hfa₂, hfb₂⟩
  have LS4 : LongSide G P₂ b₂ a₂ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₄) (N c₂) :=
    ⟨hP₂.1, hodd₂, hs.b₂_mem, hs.a₂_mem, nab₂.symm, hcov₂, hdis₂, hfb₂, hfa₂⟩
  -- the four `ShortSide` packages
  have hn12 : (N c₁ ∪ N c₂) \ {x₁} = {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₂}) : Set V) | G.Adj x₁ w} := by
    rw [hNc₁, hNc₂, hs.nbrs_x₁]
    ext w
    constructor
    · rintro ⟨((rfl | rfl | rfl) | (rfl | rfl | rfl)), hne⟩
      exacts [absurd rfl hne, Or.inr (Or.inr (Or.inl rfl)), Or.inl rfl, absurd rfl hne,
        Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inl rfl)]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨Or.inl (Or.inr (Or.inr rfl)), fun h => nax₁ (by simpa using h)⟩,
        ⟨Or.inr (Or.inr (Or.inr rfl)), fun h => ncx₁ (by simpa using h)⟩,
        ⟨Or.inl (Or.inr (Or.inl rfl)), fun h => nqx (by simpa using h.symm)⟩,
        ⟨Or.inr (Or.inr (Or.inl rfl)), fun h => nqy (by simpa using h.symm)⟩]
  have hn23 : (N c₂ ∪ N c₃) \ {y₂} = {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₁}) : Set V) | G.Adj y₂ w} := by
    rw [hNc₂, hNc₃, hs.nbrs_y₂]
    ext w
    constructor
    · rintro ⟨((rfl | rfl | rfl) | (rfl | rfl | rfl)), hne⟩
      exacts [Or.inr (Or.inr (Or.inl rfl)), absurd rfl hne, Or.inr (Or.inl rfl),
        Or.inr (Or.inr (Or.inr rfl)), absurd rfl hne, Or.inl rfl]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨Or.inr (Or.inr (Or.inr rfl)), fun h => nby₂ (by simpa using h)⟩,
        ⟨Or.inl (Or.inr (Or.inr rfl)), fun h => ncy₂ (by simpa using h)⟩,
        ⟨Or.inl (Or.inl rfl), fun h => nqy (by simpa using h)⟩,
        ⟨Or.inr (Or.inl rfl), fun h => nyy (by simpa using h)⟩]
  have hn34 : (N c₃ ∪ N c₄) \ {y₁} = {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₂}) : Set V) | G.Adj y₁ w} := by
    rw [hNc₃, hNc₄, hs.nbrs_y₁]
    ext w
    constructor
    · rintro ⟨((rfl | rfl | rfl) | (rfl | rfl | rfl)), hne⟩
      exacts [absurd rfl hne, Or.inr (Or.inr (Or.inr rfl)), Or.inl rfl, absurd rfl hne,
        Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inl rfl)]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨Or.inl (Or.inr (Or.inr rfl)), fun h => nby₁ (by simpa using h)⟩,
        ⟨Or.inr (Or.inr (Or.inr rfl)), fun h => ndy₁ (by simpa using h)⟩,
        ⟨Or.inr (Or.inr (Or.inl rfl)), fun h => nyx (by simpa using h.symm)⟩,
        ⟨Or.inl (Or.inr (Or.inl rfl)), fun h => nyy (by simpa using h.symm)⟩]
  have hn41 : (N c₄ ∪ N c₁) \ {x₂} = {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₁}) : Set V) | G.Adj x₂ w} := by
    rw [hNc₄, hNc₁, hs.nbrs_x₂]
    ext w
    constructor
    · rintro ⟨((rfl | rfl | rfl) | (rfl | rfl | rfl)), hne⟩
      exacts [Or.inr (Or.inr (Or.inr rfl)), absurd rfl hne, Or.inr (Or.inl rfl),
        Or.inr (Or.inr (Or.inl rfl)), absurd rfl hne, Or.inl rfl]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨Or.inr (Or.inr (Or.inr rfl)), fun h => nax₂ (by simpa using h)⟩,
        ⟨Or.inl (Or.inr (Or.inr rfl)), fun h => ndx₂ (by simpa using h)⟩,
        ⟨Or.inr (Or.inl rfl), fun h => nqx (by simpa using h)⟩,
        ⟨Or.inl (Or.inl rfl), fun h => nyx (by simpa using h)⟩]
  have SS12 : ShortSide G x₁ y₁ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₁) (N c₂) :=
    ⟨nxy₁, hx₁SA, hy₁SA, hmemK y₁ (Or.inr (Or.inr (Or.inl hs.y₁_mem))), hSAsub, hn12⟩
  have SS21 : ShortSide G x₁ y₁ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₂) (N c₁) :=
    ⟨nxy₁, hx₁SA, hy₁SA, hmemK y₁ (Or.inr (Or.inr (Or.inl hs.y₁_mem))), hSAsub,
      by rw [Set.union_comm]; exact hn12⟩
  have SS23 : ShortSide G y₂ x₂ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₁}) : Set V) (N c₂) (N c₃) :=
    ⟨nxy₂.symm, hy₂SB, hx₂SB, hmemK x₂ (Or.inr (Or.inr (Or.inr hs.x₂_mem))), hSBsub, hn23⟩
  have SS32 : ShortSide G y₂ x₂ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₁}) : Set V) (N c₃) (N c₂) :=
    ⟨nxy₂.symm, hy₂SB, hx₂SB, hmemK x₂ (Or.inr (Or.inr (Or.inr hs.x₂_mem))), hSBsub,
      by rw [Set.union_comm]; exact hn23⟩
  have SS34 : ShortSide G y₁ x₁ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₃) (N c₄) :=
    ⟨nxy₁.symm, hy₁SA, hx₁SA, hmemK x₁ (Or.inr (Or.inr (Or.inl hs.x₁_mem))), hSAsub, hn34⟩
  have SS43 : ShortSide G y₁ x₁ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₂}) : Set V) (N c₄) (N c₃) :=
    ⟨nxy₁.symm, hy₁SA, hx₁SA, hmemK x₁ (Or.inr (Or.inr (Or.inl hs.x₁_mem))), hSAsub,
      by rw [Set.union_comm]; exact hn34⟩
  have SS41 : ShortSide G x₂ y₂ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₁}) : Set V) (N c₄) (N c₁) :=
    ⟨nxy₂, hx₂SB, hy₂SB, hmemK y₂ (Or.inr (Or.inr (Or.inr hs.y₂_mem))), hSBsub, hn41⟩
  have SS14 : ShortSide G x₂ y₂ K (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪
      {v : V | v ∈ Q₁}) : Set V) (N c₁) (N c₄) :=
    ⟨nxy₂, hx₂SB, hy₂SB, hmemK y₂ (Or.inr (Or.inr (Or.inr hs.y₂_mem))), hSBsub,
      by rw [Set.union_comm]; exact hn41⟩
  -- the two long branches, with their supports
  obtain ⟨qA, hqA, hqAt, hPA⟩ := hbrA
  obtain ⟨qB, hqB, hqBt, hPB⟩ := hbrB
  -- the intersections of the four triangles with the two long supports
  have hiP₁a : N c₁ ∩ {v : V | v ∈ P₁} = {a₁} := by
    rw [hNc₁]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hw⟩
      exacts [absurd hs.x₁_mem (d2 w hw), absurd hs.x₂_mem (d3 w hw), rfl]
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), hs.a₁_mem⟩
  have hiP₁b : N c₃ ∩ {v : V | v ∈ P₁} = {b₁} := by
    rw [hNc₃]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hw⟩
      exacts [absurd hs.y₁_mem (d2 w hw), absurd hs.y₂_mem (d3 w hw), rfl]
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), hs.b₁_mem⟩
  have hiP₂a : N c₂ ∩ {v : V | v ∈ P₂} = {a₂} := by
    rw [hNc₂]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hw⟩
      exacts [absurd hs.x₁_mem (d4 w hw), absurd hs.y₂_mem (d5 w hw), rfl]
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), hs.a₂_mem⟩
  have hiP₂b : N c₄ ∩ {v : V | v ∈ P₂} = {b₂} := by
    rw [hNc₄]
    ext w
    constructor
    · rintro ⟨(rfl | rfl | rfl), hw⟩
      exacts [absurd hs.y₁_mem (d4 w hw), absurd hs.x₂_mem (d5 w hw), rfl]
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), hs.b₂_mem⟩
  -- membership of the four cross vertices in the four triangles
  have hx₁c₁ : x₁ ∈ N c₁ := by rw [hNc₁]; exact Or.inl rfl
  have hx₁c₂ : x₁ ∈ N c₂ := by rw [hNc₂]; exact Or.inl rfl
  have hy₂c₂ : y₂ ∈ N c₂ := by rw [hNc₂]; exact Or.inr (Or.inl rfl)
  have hy₂c₃ : y₂ ∈ N c₃ := by rw [hNc₃]; exact Or.inr (Or.inl rfl)
  have hy₁c₃ : y₁ ∈ N c₃ := by rw [hNc₃]; exact Or.inl rfl
  have hy₁c₄ : y₁ ∈ N c₄ := by rw [hNc₄]; exact Or.inl rfl
  have hx₂c₄ : x₂ ∈ N c₄ := by rw [hNc₄]; exact Or.inr (Or.inl rfl)
  have hx₂c₁ : x₂ ∈ N c₁ := by rw [hNc₁]; exact Or.inr (Or.inl rfl)
  -- finally, the twelve cases
  rcases hcmem d₁ hd₁ with rfl | rfl | rfl | rfl <;>
    rcases hcmem d₂ hd₂ with rfl | rfl | rfl | rfl
  · exact absurd rfl hdne
  · -- `c₁c₂`: the edge carrying `x₁`
    have hRs := hRshort c₁ c₂ h12 x₁ hex12 hb₁ hb₂ (Or.inl ⟨rfl, rfl⟩)
    exact Or.inr ⟨x₁, y₁, Q₂, Or.inl rfl, SS12, hRs,
      hsingle c₁ x₁ r₁ hR₁ hRs hx₁c₁, hsingle c₂ x₁ r₂ hR₂ hRs hx₁c₂⟩
  · -- `c₁c₃`: the branch carrying `P₁`
    have hRs := hRlong qA c₁ c₃ P₁ hqA hqAt hPA (Or.inl ⟨rfl, rfl⟩)
    exact Or.inl ⟨a₁, b₁, P₁, P₂, Or.inl rfl, LS1, hRs,
      hsingleP c₁ a₁ r₁ P₁ hR₁ hRs hiP₁a, hsingleP c₃ b₁ r₂ P₁ hR₂ hRs hiP₁b⟩
  · -- `c₁c₄`: the edge carrying `x₂`
    have hRs := hRshort c₄ c₁ h41 x₂ hex41 hb₄ hb₁ (Or.inr ⟨rfl, rfl⟩)
    exact Or.inr ⟨x₂, y₂, Q₁, Or.inr (Or.inr (Or.inl rfl)), SS14, hRs,
      hsingle c₁ x₂ r₁ hR₁ hRs hx₂c₁, hsingle c₄ x₂ r₂ hR₂ hRs hx₂c₄⟩
  · -- `c₂c₁`
    have hRs := hRshort c₁ c₂ h12 x₁ hex12 hb₁ hb₂ (Or.inr ⟨rfl, rfl⟩)
    exact Or.inr ⟨x₁, y₁, Q₂, Or.inl rfl, SS21, hRs,
      hsingle c₂ x₁ r₁ hR₁ hRs hx₁c₂, hsingle c₁ x₁ r₂ hR₂ hRs hx₁c₁⟩
  · exact absurd rfl hdne
  · -- `c₂c₃`: the edge carrying `y₂`
    have hRs := hRshort c₂ c₃ h23 y₂ hex23 hb₂ hb₃ (Or.inl ⟨rfl, rfl⟩)
    exact Or.inr ⟨y₂, x₂, Q₁, Or.inr (Or.inr (Or.inr rfl)), SS23, hRs,
      hsingle c₂ y₂ r₁ hR₁ hRs hy₂c₂, hsingle c₃ y₂ r₂ hR₂ hRs hy₂c₃⟩
  · -- `c₂c₄`: the branch carrying `P₂`
    have hRs := hRlong qB c₂ c₄ P₂ hqB hqBt hPB (Or.inl ⟨rfl, rfl⟩)
    exact Or.inl ⟨a₂, b₂, P₂, P₁, Or.inr (Or.inr (Or.inl rfl)), LS3, hRs,
      hsingleP c₂ a₂ r₁ P₂ hR₁ hRs hiP₂a, hsingleP c₄ b₂ r₂ P₂ hR₂ hRs hiP₂b⟩
  · -- `c₃c₁`
    have hRs := hRlong qA c₁ c₃ P₁ hqA hqAt hPA (Or.inr ⟨rfl, rfl⟩)
    exact Or.inl ⟨b₁, a₁, P₁, P₂, Or.inr (Or.inl rfl), LS2, hRs,
      hsingleP c₃ b₁ r₁ P₁ hR₁ hRs hiP₁b, hsingleP c₁ a₁ r₂ P₁ hR₂ hRs hiP₁a⟩
  · -- `c₃c₂`
    have hRs := hRshort c₂ c₃ h23 y₂ hex23 hb₂ hb₃ (Or.inr ⟨rfl, rfl⟩)
    exact Or.inr ⟨y₂, x₂, Q₁, Or.inr (Or.inr (Or.inr rfl)), SS32, hRs,
      hsingle c₃ y₂ r₁ hR₁ hRs hy₂c₃, hsingle c₂ y₂ r₂ hR₂ hRs hy₂c₂⟩
  · exact absurd rfl hdne
  · -- `c₃c₄`: the edge carrying `y₁`
    have hRs := hRshort c₃ c₄ h34 y₁ hex34 hb₃ hb₄ (Or.inl ⟨rfl, rfl⟩)
    exact Or.inr ⟨y₁, x₁, Q₂, Or.inr (Or.inl rfl), SS34, hRs,
      hsingle c₃ y₁ r₁ hR₁ hRs hy₁c₃, hsingle c₄ y₁ r₂ hR₂ hRs hy₁c₄⟩
  · -- `c₄c₁`
    have hRs := hRshort c₄ c₁ h41 x₂ hex41 hb₄ hb₁ (Or.inl ⟨rfl, rfl⟩)
    exact Or.inr ⟨x₂, y₂, Q₁, Or.inr (Or.inr (Or.inl rfl)), SS41, hRs,
      hsingle c₄ x₂ r₁ hR₁ hRs hx₂c₄, hsingle c₁ x₂ r₂ hR₂ hRs hx₂c₁⟩
  · -- `c₄c₂`
    have hRs := hRlong qB c₂ c₄ P₂ hqB hqBt hPB (Or.inr ⟨rfl, rfl⟩)
    exact Or.inl ⟨b₂, a₂, P₂, P₁, Or.inr (Or.inr (Or.inr rfl)), LS4, hRs,
      hsingleP c₄ b₂ r₁ P₂ hR₁ hRs hiP₂b, hsingleP c₂ a₂ r₂ P₂ hR₂ hRs hiP₂a⟩
  · -- `c₄c₃`
    have hRs := hRshort c₃ c₄ h34 y₁ hex34 hb₃ hb₄ (Or.inr ⟨rfl, rfl⟩)
    exact Or.inr ⟨y₁, x₁, Q₂, Or.inr (Or.inl rfl), SS43, hRs,
      hsingle c₄ y₁ r₁ hR₁ hRs hy₁c₄, hsingle c₃ y₁ r₂ hR₂ hRs hy₁c₃⟩
  · exact absurd rfl hdne

end Workspace.ProofLemmas.Thm93CaseOneClassify
