import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.StriationCompl
import Workspace.Statements.S09.Thm_9_1
import Workspace.Statements.S09.Thm_9_3
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.Thm94ClosingCopy
import Workspace.ProofLemmas.Thm94ClosingContradiction

/-!
# The body of 9.4 — its claims (1), (2) and the closing paragraph
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm94Body

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The hypothesis package of 9.4 -/

/-- The standing hypotheses of 9.4: `G` Berge, no appearance of a `K₄`-enlargement and no
overshadowed appearance of `K₄` in either orientation, `L = (S, T)` a **maximal** striation, and
a vertex `f` off `V(L)`. -/
def Setup (Gx : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (f : V) : Prop :=
  Berge Gx ∧
  (¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
    IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J')) ∧
  (¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V) (φ : H.lineGraph ≃g Gx.induce K'),
    IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ) ∧
  (¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V) (φ : H.lineGraph ≃g Gxᶜ.induce K'),
    IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ) ∧
  MaximalStriation Gx S T ∧
  f ∉ striationVertices S T

/-- **The complement of 9.4's configuration.**  PAPER: *"taking complements if necessary"*. -/
theorem setup_compl {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {f : V}
    (h : Setup Gx S T f) : Setup Gxᶜ T S f := by
  obtain ⟨hB, henl, hov, hovc, hmax, hf⟩ := h
  have hcc : Gxᶜᶜ = Gx := compl_compl Gx
  refine ⟨HoleBasics.berge_compl.mpr hB, ?_, hovc, ?_,
    StriationCompl.maximalStriation_compl hmax, ?_⟩
  · rintro ⟨k, J', hJ, hA⟩
    refine henl ⟨k, J', hJ, ?_⟩
    rcases hA with h | h
    · exact Or.inr h
    · exact Or.inl (hcc ▸ h)
  · rw [hcc]; exact hov
  · rwa [StriationCompl.striationVertices_swap S T]

/-! ### Small pieces used by the claims -/

section Helpers

variable {V' : Type*}

/-- Membership does not see a reversal. -/
private theorem mem_iff_of_rev {l l' : List V'} (h : l' = l ∨ l' = l.reverse) (v : V') :
    v ∈ l' ↔ v ∈ l := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact List.mem_reverse

/-- PAPER (printed p. 50): *"every vertex of `A ∪ B ∪ C` belongs to a [rung]"*. -/
private theorem exists_rung_through {G : SimpleGraph V'} {S : Set V' × Set V' × Set V'}
    (h : IsStrip G S) {v : V'} (hv : v ∈ stripVertices S) :
    ∃ p : List V', IsSRung G S p ∧ v ∈ p := by
  obtain ⟨A, C, B⟩ := S
  exact h.2.2.2.2.2 v hv

/-- A strip has at least one rung: its set `A` is nonempty. -/
private theorem exists_rung {G : SimpleGraph V'} {S : Set V' × Set V' × Set V'}
    (h : IsStrip G S) : ∃ p : List V', IsSRung G S p := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨a, ha⟩ := h.2.2.2.1
  obtain ⟨p, hp, -⟩ := h.2.2.2.2.2 a (Set.mem_union_left _ (Set.mem_union_left _ ha))
  exact ⟨p, hp⟩

/-- PAPER (printed p. 50): *"Note that if `(S₁, S₂, T₁, T₂)` is a twist, then so is
`(S₁', S₂, T₁, T₂)`"* — in particular being a twist does not see the order of the two strips. -/
private theorem isTwist_swap {G : SimpleGraph V'} {S₁ S₂ T₁ T₂ : Set V' × Set V' × Set V'}
    (h : IsTwist G S₁ S₂ T₁ T₂) : IsTwist G S₂ S₁ T₁ T₂ := by
  simp only [IsTwist, AgreeOn] at h ⊢
  tauto

/-- The striation axiom *"for `1 ≤ i < i' ≤ m` there exist distinct `j, j'` such that
`(Sᵢ, Sᵢ', Tⱼ, Tⱼ')` is a twist"*, freed of the ordering of `i, i'`. -/
private theorem exists_twist_of_ne {G : SimpleGraph V'} {m n : ℕ}
    {S : Fin m → Set V' × Set V' × Set V'} {T : Fin n → Set V' × Set V' × Set V'}
    (hL : IsStriation G S T) {i i' : Fin m} (hii : i ≠ i') :
    ∃ j j' : Fin n, j ≠ j' ∧ IsTwist G (S i) (S i') (T j) (T j') := by
  rcases lt_trichotomy i i' with h | h | h
  · exact hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' h
  · exact absurd h hii
  · obtain ⟨j, j', hjj, ht⟩ := hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i' i h
    exact ⟨j, j', hjj, isTwist_swap ht⟩

/-- The bookkeeping behind *"By reversing `S₂` we may assume that `S₁` and `S₂` agree on `T₁`;
and we may assume they disagree on `T₂`"*: once **some** pair of indices carries a twist, and
every index is either an agreement or a disagreement, **every** index has a twist partner. -/
private theorem twist_partner_abstract {n : ℕ} (Ag Ds : Fin n → Prop)
    (hcover : ∀ k, Ag k ∨ Ds k) {c d : Fin n} (hcd : c ≠ d)
    (htw : (Ag c ∧ Ds d) ∨ (Ag d ∧ Ds c)) (j : Fin n) :
    ∃ j' : Fin n, j ≠ j' ∧ ((Ag j ∧ Ds j') ∨ (Ag j' ∧ Ds j)) := by
  have main : ∀ c d : Fin n, c ≠ d → Ag c → Ds d →
      ∃ j' : Fin n, j ≠ j' ∧ ((Ag j ∧ Ds j') ∨ (Ag j' ∧ Ds j)) := by
    intro c d hcd hc hd
    by_cases hjd : j = d
    · refine ⟨c, ?_, Or.inr ⟨hc, by rw [hjd]; exact hd⟩⟩
      rw [hjd]; exact hcd.symm
    · rcases hcover j with hj | hj
      · exact ⟨d, hjd, Or.inl ⟨hj, hd⟩⟩
      · by_cases hjc : j = c
        · exact ⟨d, hjd, Or.inl ⟨by rw [hjc]; exact hc, hd⟩⟩
        · exact ⟨c, hjc, Or.inr ⟨hc, hj⟩⟩
  rcases htw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact main c d hcd h1 h2
  · exact main d c hcd.symm h1 h2

/-- A path of length `1` is the two-element list of its ends. -/
private theorem eq_pair_of_pathLength_one {G : SimpleGraph V'} {p : List V'} {u v : V'}
    (h : IsPathFrom G p u v) (hl : pathLength p = 1) : p = [u, v] := by
  have hpos : 0 < p.length := PathBasics.path_length_pos h.1
  have h2 : p.length = 2 := by
    simp only [pathLength] at hl; omega
  obtain ⟨s, t, rfl⟩ := PrismBasics.length_eq_two h2
  have hs : s = u := by simpa using h.2.1
  have ht : t = v := by simpa using h.2.2
  rw [hs, ht]

/-- **PAPER (9.4, printed p. 51):** *"But then `f-x₁-a₁-P₁-b₁-y₁-f` is an odd hole, a
contradiction."*

`P` is the path `a-P-b`, of odd length; `Q = [x, y]` is the length-1 antipath, whose only edges
to `P` are `ax` and `by`; and `g` (the paper's `f`) is adjacent to both `x, y` and to no vertex
of `P`.  Then `g-x-a-P-b-y-g` is a hole of length `pathLength P + 4`, which is odd. -/
private theorem odd_hole_contradiction {G : SimpleGraph V'} (hG : Berge G)
    {P Q : List V'} {a b x y g : V'}
    (hP : IsPathFrom G P a b) (hPodd : Odd (pathLength P)) (hPlen : 1 ≤ pathLength P)
    (hQeq : Q = [x, y]) (hxy : ¬ G.Adj x y) (hxyne : x ≠ y)
    (hE : ∀ u ∈ P, ∀ w ∈ ({x, y} : Set V'), (G.Adj u w ↔ ((u = a ∧ w = x) ∨ (u = b ∧ w = y))))
    (hPQ : ∀ v ∈ P, v ∉ Q)
    (hgP : ∀ v ∈ P, ¬ G.Adj g v) (hgQ : ∀ v ∈ Q, G.Adj g v) (hgnP : g ∉ P) : False := by
  have haP : a ∈ P := (PathBasics.isPathFrom_ends_mem hP).1
  have hbP : b ∈ P := (PathBasics.isPathFrom_ends_mem hP).2
  have hxQ : x ∈ Q := by rw [hQeq]; simp
  have hyQ : y ∈ Q := by rw [hQeq]; simp
  have hxP : x ∉ P := fun h => hPQ x h hxQ
  have hyP : y ∉ P := fun h => hPQ y h hyQ
  have hax : G.Adj a x := (hE a haP x (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
  have hby : G.Adj b y := (hE b hbP y (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)
  have hxother : ∀ z ∈ P, z ≠ a → ¬ G.Adj x z := by
    intro z hz hza hadj
    rcases (hE z hz x (by simp)).mp hadj.symm with ⟨h, -⟩ | ⟨-, h⟩
    · exact hza h
    · exact hxyne h
  have hyother : ∀ z ∈ P, z ≠ b → ¬ G.Adj y z := by
    intro z hz hzb hadj
    rcases (hE z hz y (by simp)).mp hadj.symm with ⟨-, h⟩ | ⟨h, -⟩
    · exact hxyne h.symm
    · exact hzb h
  have hq : IsPathFrom G (x :: (P ++ [y])) x y :=
    PathAttach.isPathFrom_cons_concat hP hax.symm hby.symm hxy hxyne hxP hyP hxother hyother
  have hPl : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hP.1
  have hglen : 2 ≤ pathLength (x :: (P ++ [y])) := by
    rw [PathAttach.pathLength_cons_append_singleton]; omega
  have hgx : G.Adj g x := hgQ x hxQ
  have hgy : G.Adj g y := hgQ y hyQ
  have hgnq : g ∉ (x :: (P ++ [y])) := by
    intro hmem
    have h' : g = x ∨ g ∈ P ∨ g = y := by simpa using hmem
    rcases h' with h | h | h
    · rw [h] at hgx; exact G.irrefl hgx
    · exact hgnP h
    · rw [h] at hgy; exact G.irrefl hgy
  have hint : ∀ z ∈ SPGT.interior (x :: (P ++ [y])), ¬ G.Adj g z := by
    intro z hz
    have hzP : z ∈ P := by
      simp only [SPGT.interior, List.tail_cons] at hz
      rwa [List.dropLast_concat] at hz
    exact hgP z hzP
  have hhole : IsHoleList G (g :: (x :: (P ++ [y]))) :=
    PrismBasics.isHoleList_of_path_add_vertex hq hglen hgx hgy hgnq hint
  have hev := hG.1 _ hhole
  rw [PrismBasics.holeLength_cons g (by simp),
    PathAttach.pathLength_cons_append_singleton] at hev
  obtain ⟨t, ht⟩ := hev
  obtain ⟨k, hk⟩ := hPodd
  omega

end Helpers

/-! ### Claim (1) -/

/-- **PAPER (9.4, printed p. 51), claim (1).**

*"(1) Let `1 ≤ i ≤ m`, and `1 ≤ j ≤ n`; let `aᵢ-Pᵢ-bᵢ` be an `Sᵢ`-rung, and `xⱼ-Qⱼ-yⱼ` a
`Tⱼ`-antirung.  Then either `X ∩ V(Pᵢ) ≠ ∅`, or `V(Qⱼ) ⊄ X`.*

*For suppose that `X` includes `V(Q₁)` and is disjoint from `V(P₁)` say.  By reversing `S₂` we
may assume that `S₁` and `S₂` agree on `T₁`; and we may assume they disagree on `T₂`.  Let
`a₂-P₂-b₂` be any `S₂`-rung, and `x₂-Q₂-y₂` any `T₂`-antirung.  Then `(P₁, P₂, Q₁, Q₂)` is a
knot, so by 9.1, we may assume (taking complements if necessary) that `Q₁` has length 1.  But
then `f-x₁-a₁-P₁-b₁-y₁-f` is an odd hole, a contradiction.  This proves (1)."* -/
theorem claim1 {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {f : V}
    (hs : Setup Gx S T f) (i : Fin m) (j : Fin n) (P Q : List V)
    (hP : IsSRung Gx (S i) P) (hQ : IsSRung Gxᶜ (T j) Q) :
    (∃ v ∈ P, v ∈ Gx.neighborSet f ∩ striationVertices S T) ∨
      (∃ v ∈ Q, v ∉ Gx.neighborSet f ∩ striationVertices S T) := by
  obtain ⟨hB, henl, hov, hovc, hmax, hf⟩ := hs
  have hL : IsStriation Gx S T := hmax.1
  -- PAPER: *"For suppose that `X` includes `V(Q₁)` and is disjoint from `V(P₁)` say."*
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  push_neg at hc1 hc2
  have hfP : ∀ v ∈ P, ¬ Gx.Adj f v := by
    intro v hv hadj
    exact hc1 v hv ⟨hadj, StriationCompl.mem_striationVertices_of_isSRung (T := T) hP hv⟩
  have hfQ : ∀ v ∈ Q, Gx.Adj f v := fun v hv => (hc2 v hv).1
  -- PAPER: *"By reversing `S₂` we may assume that `S₁` and `S₂` agree on `T₁`; and we may
  -- assume they disagree on `T₂`."*
  have hm2 : 2 ≤ m := hL.2.2.2.2.2.2.2.1
  obtain ⟨i', hii'⟩ : ∃ i' : Fin m, i ≠ i' := by
    by_cases h : (i : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun hc => ?_⟩
      have h1 : (i : ℕ) = 1 := by rw [hc]
      omega
    · refine ⟨⟨0, by omega⟩, fun hc => ?_⟩
      have h1 : (i : ℕ) = 0 := by rw [hc]
      omega
  have hpar : ∀ (i₀ : Fin m) (j₀ : Fin n),
      ParallelStripAntistrip Gx (S i₀) (T j₀) ∨ CoParallel Gx (S i₀) (T j₀) :=
    hL.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨c, d, hcd, htwcd⟩ := exists_twist_of_ne hL hii'
  have hcover : ∀ k : Fin n, AgreeOn Gx (S i) (S i') (T k) ∨
      ((ParallelStripAntistrip Gx (S i) (T k) ∧ CoParallel Gx (S i') (T k)) ∨
        (CoParallel Gx (S i) (T k) ∧ ParallelStripAntistrip Gx (S i') (T k))) := by
    intro k
    rcases hpar i k with h | h <;> rcases hpar i' k with h' | h' <;>
      simp only [AgreeOn] <;> tauto
  obtain ⟨j', hjj', htw⟩ :=
    twist_partner_abstract (fun k => AgreeOn Gx (S i) (S i') (T k))
      (fun k => (ParallelStripAntistrip Gx (S i) (T k) ∧ CoParallel Gx (S i') (T k)) ∨
        (CoParallel Gx (S i) (T k) ∧ ParallelStripAntistrip Gx (S i') (T k)))
      hcover hcd htwcd j
  -- PAPER: *"Let `a₂-P₂-b₂` be any `S₂`-rung, and `x₂-Q₂-y₂` any `T₂`-antirung."*
  obtain ⟨P₂, hP₂⟩ := exists_rung (hL.1 i')
  obtain ⟨Q₂, hQ₂⟩ := exists_rung (hL.2.1 j')
  -- PAPER: *"Then `(P₁, P₂, Q₁, Q₂)` is a knot"*
  obtain ⟨P₁', P₂', Q₁', Q₂', rP₁, rP₂, rQ₁, rQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hii' hjj' htw hP hP₂ hQ hQ₂
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hpa₁, hpa₂, hqa₁, hqa₂,
    d12, d1q1, d1q2, d2q1, d2q2, dq12, lP1, lP2, lQ1, lQ2, hantiPP, hcompQQ,
    hE11, hE12, hE21, hE22, hN11, hN12, hN31, hN42⟩ := id hknot
  -- PAPER: *"so by 9.1, we may assume (taking complements if necessary) that `Q₁` has length 1"*
  obtain ⟨⟨oP1, oP2, oQ1, oQ2⟩, hdich⟩ :=
    Workspace.Statements.S09.SPGT.thm_9_1 Gx hB P₁' P₂' Q₁' Q₂' hknot
  have hfP' : ∀ v ∈ P₁', ¬ Gx.Adj f v := fun v hv => hfP v ((mem_iff_of_rev rP₁ v).mp hv)
  have hfQ' : ∀ v ∈ Q₁', Gx.Adj f v := fun v hv => hfQ v ((mem_iff_of_rev rQ₁ v).mp hv)
  have hfnP : f ∉ P₁' := fun h =>
    hf (StriationCompl.mem_striationVertices_of_isSRung (T := T) hP
      ((mem_iff_of_rev rP₁ f).mp h))
  have hfnQ : f ∉ Q₁' := fun h =>
    hf (StriationCompl.mem_striationVertices_of_isSRung' (S := S) hQ
      ((mem_iff_of_rev rQ₁ f).mp h))
  have ha₁P : a₁ ∈ P₁' := (PathBasics.isPathFrom_ends_mem hpa₁).1
  have hb₁P : b₁ ∈ P₁' := (PathBasics.isPathFrom_ends_mem hpa₁).2
  rcases hdich with ⟨hp1, -⟩ | ⟨hq1, -⟩
  · -- PAPER: *"taking complements if necessary"* — here `P₁` is the short one, so the same
    -- hole is read in `Ḡ`: `f-a₁-y₁-Q₁-x₁-b₁-f` is an odd antihole.
    have hBc : Berge Gxᶜ := HoleBasics.berge_compl.mpr hB
    have hQrev : IsPathFrom Gxᶜ Q₁'.reverse y₁ x₁ := PathBasics.isPathFrom_reverse hqa₁
    have hPeq : P₁' = [a₁, b₁] := eq_pair_of_pathLength_one hpa₁ hp1
    have habadj : Gx.Adj a₁ b₁ := PathBasics.isPathFrom_ends_adj_of_length_one hpa₁ hp1
    refine odd_hole_contradiction (g := f) hBc hQrev ?_ ?_ hPeq ?_ habadj.ne ?_ ?_ ?_ ?_ ?_
    · rw [PathBasics.pathLength_reverse]; exact oQ1
    · rw [PathBasics.pathLength_reverse]; exact lQ1
    · exact fun h => ((SimpleGraph.compl_adj Gx a₁ b₁).mp h).2 habadj
    · intro u hu w hw
      have huQ : u ∈ Q₁' := List.mem_reverse.mp hu
      have hwP : w ∈ P₁' := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact ha₁P
        · exact hb₁P
      have hne : u ≠ w := fun h => d1q1 w hwP (by rw [← h]; exact huQ)
      constructor
      · intro h
        rcases (hN11 u huQ w hw).mp ((SimpleGraph.compl_adj Gx u w).mp h).2 with
          ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h2, h1⟩
        · exact Or.inr ⟨h2, h1⟩
      · intro h
        refine (SimpleGraph.compl_adj Gx u w).mpr ⟨hne, (hN11 u huQ w hw).mpr ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h2, h1⟩
        · exact Or.inr ⟨h2, h1⟩
    · exact fun v hv hv' => d1q1 v hv' (List.mem_reverse.mp hv)
    · exact fun v hv h =>
        ((SimpleGraph.compl_adj Gx f v).mp h).2 (hfQ' v (List.mem_reverse.mp hv))
    · exact fun v hv => (SimpleGraph.compl_adj Gx f v).mpr
        ⟨fun h => hfnP (by rw [h]; exact hv), hfP' v hv⟩
    · exact fun h => hfnQ (List.mem_reverse.mp h)
  · -- PAPER: *"But then `f-x₁-a₁-P₁-b₁-y₁-f` is an odd hole, a contradiction."*
    have hQeq : Q₁' = [x₁, y₁] := eq_pair_of_pathLength_one hqa₁ hq1
    have hxyadj : Gxᶜ.Adj x₁ y₁ := PathBasics.isPathFrom_ends_adj_of_length_one hqa₁ hq1
    exact odd_hole_contradiction hB hpa₁ oP1 lP1 hQeq
      (fun h => ((SimpleGraph.compl_adj Gx x₁ y₁).mp hxyadj).2 h)
      ((SimpleGraph.compl_adj Gx x₁ y₁).mp hxyadj).1
      hE11 d1q1 hfP' hfQ' hfnP

/-! ### Claim (2) -/

/-- **PAPER (9.4, printed p. 51), claim (2).**

*"(2) `X` meets at most one of `V(S₁), …, V(S_m)`.*

*For suppose that `X` meets both `S₁` and `S₂` say.  We may assume that `(S₁, S₂, T₁, T₂)` is a
twist.  For `i = 1, 2` choose an `Sᵢ`-rung `Pᵢ` such that `X ∩ V(Pᵢ) ≠ ∅`, and for `j = 1, 2`
choose any `Tⱼ`-antirung `Qⱼ`.  By our assumption above, `f` has nonneighbours in both
`Q₁, Q₂`.  But then `(P₁, P₂, Q₁, Q₂)` is a knot, and setting `F = {f}` violates 9.3, a
contradiction.  This proves (2)."*

The hypothesis `hanti` is the paper's *"our assumption above"*: *"we may assume that for all
`1 ≤ j ≤ n`, and for all `Tⱼ`-antirungs `Qⱼ`, `V(Qⱼ) ⊄ X`"*. -/
theorem claim2 {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {f : V}
    (hs : Setup Gx S T f)
    (hanti : ∀ (j : Fin n) (Q : List V), IsSRung Gxᶜ (T j) Q →
      ∃ v ∈ Q, v ∉ Gx.neighborSet f ∩ striationVertices S T)
    (i i' : Fin m)
    (hi : ((Gx.neighborSet f ∩ striationVertices S T) ∩ stripVertices (S i)).Nonempty)
    (hi' : ((Gx.neighborSet f ∩ striationVertices S T) ∩ stripVertices (S i')).Nonempty) :
    i = i' := by
  obtain ⟨hB, henl, hov, hovc, hmax, hf⟩ := hs
  have hL : IsStriation Gx S T := hmax.1
  by_contra hne
  -- PAPER: *"For `i = 1, 2` choose an `Sᵢ`-rung `Pᵢ` such that `X ∩ V(Pᵢ) ≠ ∅`"*
  obtain ⟨u, huX, huS⟩ := hi
  obtain ⟨u', hu'X, hu'S⟩ := hi'
  obtain ⟨P₁, hP₁, huP⟩ := exists_rung_through (hL.1 i) huS
  obtain ⟨P₂, hP₂, hu'P⟩ := exists_rung_through (hL.1 i') hu'S
  -- PAPER: *"We may assume that `(S₁, S₂, T₁, T₂)` is a twist."*
  obtain ⟨j, j', hjj, htw⟩ := exists_twist_of_ne hL hne
  -- PAPER: *"and for `j = 1, 2` choose any `Tⱼ`-antirung `Qⱼ`"*
  obtain ⟨Q₁, hQ₁⟩ := exists_rung (hL.2.1 j)
  obtain ⟨Q₂, hQ₂⟩ := exists_rung (hL.2.1 j')
  -- PAPER: *"But then `(P₁, P₂, Q₁, Q₂)` is a knot"*
  obtain ⟨P₁', P₂', Q₁', Q₂', rP₁, rP₂, rQ₁, rQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hne hjj htw hP₁ hP₂ hQ₁ hQ₂
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hpa₁, hpa₂, hqa₁, hqa₂,
    d12, d1q1, d1q2, d2q1, d2q2, dq12, lP1, lP2, lQ1, lQ2, hantiPP, hcompQQ,
    hE11, hE12, hE21, hE22, hN11, hN12, hN31, hN42⟩ := id hknot
  -- the knot's vertex set, and `f` outside it
  have hmemL : ∀ v : V, (v ∈ P₁' ∨ v ∈ P₂' ∨ v ∈ Q₁' ∨ v ∈ Q₂') →
      v ∈ striationVertices S T := by
    rintro v (hv | hv | hv | hv)
    · exact StriationCompl.mem_striationVertices_of_isSRung (T := T) hP₁
        ((mem_iff_of_rev rP₁ v).mp hv)
    · exact StriationCompl.mem_striationVertices_of_isSRung (T := T) hP₂
        ((mem_iff_of_rev rP₂ v).mp hv)
    · exact StriationCompl.mem_striationVertices_of_isSRung' (S := S) hQ₁
        ((mem_iff_of_rev rQ₁ v).mp hv)
    · exact StriationCompl.mem_striationVertices_of_isSRung' (S := S) hQ₂
        ((mem_iff_of_rev rQ₂ v).mp hv)
  have hK : KnotInduces P₁' P₂' Q₁' Q₂'
      ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) := rfl
  have hfnot : f ∉ ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪
      {v : V | v ∈ Q₂'} : Set V) := by
    rintro (((h | h) | h) | h)
    · exact hf (hmemL f (Or.inl h))
    · exact hf (hmemL f (Or.inr (Or.inl h)))
    · exact hf (hmemL f (Or.inr (Or.inr (Or.inl h))))
    · exact hf (hmemL f (Or.inr (Or.inr (Or.inr h))))
  -- the two vertices of `X` on `P₁'`, `P₂'`
  have huP' : u ∈ P₁' := (mem_iff_of_rev rP₁ u).mpr huP
  have hu'P' : u' ∈ P₂' := (mem_iff_of_rev rP₂ u').mpr hu'P
  have huadj : Gx.Adj f u := huX.1
  have hu'adj : Gx.Adj f u' := hu'X.1
  -- PAPER: *"By our assumption above, `f` has nonneighbours in both `Q₁, Q₂`."*
  obtain ⟨v₁, hv₁Q, hv₁X⟩ := hanti j Q₁ hQ₁
  obtain ⟨v₂, hv₂Q, hv₂X⟩ := hanti j' Q₂ hQ₂
  have hv₁Q' : v₁ ∈ Q₁' := (mem_iff_of_rev rQ₁ v₁).mpr hv₁Q
  have hv₂Q' : v₂ ∈ Q₂' := (mem_iff_of_rev rQ₂ v₂).mpr hv₂Q
  have hv₁n : ¬ Gx.Adj f v₁ := fun h => hv₁X ⟨h, hmemL v₁ (Or.inr (Or.inr (Or.inl hv₁Q')))⟩
  have hv₂n : ¬ Gx.Adj f v₂ := fun h => hv₂X ⟨h, hmemL v₂ (Or.inr (Or.inr (Or.inr hv₂Q')))⟩
  -- PAPER: *"setting `F = {f}` violates 9.3"*
  have hFsub : ({f} : Set V) ⊆ ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪
      {v : V | v ∈ Q₂'} : Set V)ᶜ := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hfnot
  have hFconn : ConnectedSet Gx ({f} : Set V) := by
    intro z w
    have hzw : z = w :=
      Subtype.ext ((Set.mem_singleton_iff.mp z.2).trans (Set.mem_singleton_iff.mp w.2).symm)
    subst hzw
    exact SimpleGraph.Reachable.refl z
  have huatt : u ∈ attachments Gx ({f} : Set V)
      ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) :=
    ⟨Or.inl (Or.inl (Or.inl huP')), f, rfl, huadj.symm⟩
  have hu'att : u' ∈ attachments Gx ({f} : Set V)
      ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) :=
    ⟨Or.inl (Or.inl (Or.inr hu'P')), f, rfl, hu'adj.symm⟩
  have hFattach : ¬ LocalForKnot Gx P₁' P₂' Q₁' Q₂'
      (attachments Gx ({f} : Set V)
        ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'})) := by
    rintro ⟨hd | hd, -, -, -⟩
    · exact Set.disjoint_left.mp hd huatt huP'
    · exact Set.disjoint_left.mp hd hu'att hu'P'
  have h93 := Workspace.Statements.S09.SPGT.thm_9_3 Gx hB P₁' P₂' Q₁' Q₂'
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hpa₁ hpa₂ hqa₁ hqa₂ _ hK henl hov hovc
    ({f} : Set V) hFsub hFconn hFattach
  -- ends of the four lists, as members
  have ha₁P : a₁ ∈ P₁' := (PathBasics.isPathFrom_ends_mem hpa₁).1
  have hb₁P : b₁ ∈ P₁' := (PathBasics.isPathFrom_ends_mem hpa₁).2
  have ha₂P : a₂ ∈ P₂' := (PathBasics.isPathFrom_ends_mem hpa₂).1
  have hb₂P : b₂ ∈ P₂' := (PathBasics.isPathFrom_ends_mem hpa₂).2
  have hx₁Q : x₁ ∈ Q₁' := (PathBasics.isPathFrom_ends_mem hqa₁).1
  have hy₁Q : y₁ ∈ Q₁' := (PathBasics.isPathFrom_ends_mem hqa₁).2
  have hx₂Q : x₂ ∈ Q₂' := (PathBasics.isPathFrom_ends_mem hqa₂).1
  have hy₂Q : y₂ ∈ Q₂' := (PathBasics.isPathFrom_ends_mem hqa₂).2
  rcases h93 with h1 | h2 | h3 | h4
  · -- 9.3.1 is impossible: `f` has a nonneighbour in each of `Q₁, Q₂`
    obtain ⟨g, hg, hres⟩ := h1
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hres.1 with hsub | hsub
    · exact hv₁n (hsub hv₁Q').1
    · exact hv₂n (hsub hv₂Q').1
  · -- 9.3.2 is impossible: `a` is anticomplete to the *other* path, which `f` meets
    obtain ⟨a, P, P', hcase, R, r₁, r₂, hR, hRF, hsame, -, -, -⟩ := h2
    have hr₁ : r₁ = f := by
      have : r₁ ∈ ({f} : Set V) := hRF r₁ (PathBasics.head_mem hR.2.1)
      exact Set.mem_singleton_iff.mp this
    subst hr₁
    rcases hcase with hc | hc | hc | hc <;>
      simp only [Prod.mk.injEq] at hc <;> obtain ⟨rfl, rfl, rfl⟩ := hc
    · exact hantiPP a ha₁P u' hu'P'
        ((hsame u' (Set.mem_union_left _ (Set.mem_union_left _ hu'P'))).mp hu'adj)
    · exact hantiPP a hb₁P u' hu'P'
        ((hsame u' (Set.mem_union_left _ (Set.mem_union_left _ hu'P'))).mp hu'adj)
    · exact hantiPP u huP' a ha₂P
        (((hsame u (Set.mem_union_left _ (Set.mem_union_left _ huP'))).mp huadj).symm)
    · exact hantiPP u huP' a hb₂P
        (((hsame u (Set.mem_union_left _ (Set.mem_union_left _ huP'))).mp huadj).symm)
  · -- 9.3.3 is impossible: a path inside `{f}` is the single vertex `f`, of even length `0`
    obtain ⟨a, b, P, P', -, R, r₁, r₂, hR, hRF, hodd, -, -, -, -⟩ := h3
    have hlen : R.length ≤ 1 := by
      by_contra hc
      push_neg at hc
      have h0 : R[0]'(by omega) = f :=
        Set.mem_singleton_iff.mp (hRF _ (List.getElem_mem (by omega)))
      have h1 : R[1]'(by omega) = f :=
        Set.mem_singleton_iff.mp (hRF _ (List.getElem_mem (by omega)))
      exact PathBasics.path_ne_of_ne_index hR.1 (by omega) (by omega)
        (by omega : (0 : ℕ) ≠ 1) (h0.trans h1.symm)
    have : pathLength R = 0 := by
      simp only [pathLength]; omega
    rw [this] at hodd
    simp at hodd
  · -- 9.3.4 is impossible: the copied vertex is complete to the other antipath
    obtain ⟨x, y, Q', hcase, g, hg, hsame, -⟩ := h4
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hcase with hc | hc | hc | hc <;>
      simp only [Prod.mk.injEq] at hc <;> obtain ⟨rfl, rfl, rfl⟩ := hc
    · exact hv₂n ((hsame v₂ (Set.mem_union_right _ hv₂Q')).mpr (hcompQQ x hx₁Q v₂ hv₂Q'))
    · exact hv₂n ((hsame v₂ (Set.mem_union_right _ hv₂Q')).mpr (hcompQQ x hy₁Q v₂ hv₂Q'))
    · exact hv₁n ((hsame v₁ (Set.mem_union_right _ hv₁Q')).mpr
        (hcompQQ v₁ hv₁Q' x hx₂Q).symm)
    · exact hv₁n ((hsame v₁ (Set.mem_union_right _ hv₁Q')).mpr
        (hcompQQ v₁ hv₁Q' x hy₂Q).symm)

/-! ### The closing paragraph -/

/-- **PAPER (9.4, printed p. 51), the closing paragraph.** -/
theorem closing {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {f : V}
    (hs : Setup Gx S T f)
    (hanti : ∀ (j : Fin n) (Q : List V), IsSRung Gxᶜ (T j) Q →
      ∃ v ∈ Q, v ∉ Gx.neighborSet f ∩ striationVertices S T)
    (hone : ∀ i i' : Fin m,
      ((Gx.neighborSet f ∩ striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      ((Gx.neighborSet f ∩ striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i') :
    Complete Gx
      ((Gx.neighborSet f ∩ striationVertices S T) ∩ (⋃ i : Fin m, stripVertices (S i)))
      ((Gx.neighborSet f ∩ striationVertices S T) ∩
        (⋃ j : Fin n, stripVertices (T j))) := by
  classical
  obtain ⟨hG, hnoenl, hnoover, hnoovercompl, hmax, hfL⟩ := hs
  intro u hu w hw
  obtain ⟨i, hui⟩ := Set.mem_iUnion.mp hu.2
  obtain ⟨j, hwj⟩ := Set.mem_iUnion.mp hw.2
  obtain ⟨P, hP, huP⟩ := exists_rung_through (hmax.1.1 i) hui
  obtain ⟨Q, hQ, hwQ⟩ := exists_rung_through (hmax.1.2.1 j) hwj
  obtain ⟨a, b, hPab, ha, hb, -, -, -⟩ := id hP
  by_contra huw
  have hcopy := Thm94ClosingCopy.copy_one_end_on_all_antistrips hG hnoenl hnoover
    hnoovercompl hmax.1 hfL hanti hone hP hPab hQ huP hwQ hu.1.1 hw.1.1 huw
  rcases hcopy with ⟨hnear, hcopy⟩ | ⟨hnear, hcopy⟩
  · have hXi : ((Gx.neighborSet f ∩ striationVertices S T) ∩
        stripVertices (S i)).Nonempty := by
      obtain ⟨p, hpP, hfp⟩ := hnear
      have hpS := KnotFromTwist.mem_stripVertices_of_isSRung hP hpP.1
      exact ⟨p, ⟨hfp, Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, hpS⟩)⟩, hpS⟩
    have hfanti : ∀ k : Fin m, i ≠ k → VertexAnticomplete Gx f (stripVertices (S k)) := by
      intro k hik z hz hfz
      have hXk : ((Gx.neighborSet f ∩ striationVertices S T) ∩
          stripVertices (S k)).Nonempty :=
        ⟨z, ⟨hfz, Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨k, hz⟩)⟩, hz⟩
      exact hik (hone i k hXi hXk)
    rcases hSi : S i with ⟨A, C, B⟩
    have haA : a ∈ A := by simpa [hSi] using ha
    exact Thm94ClosingContradiction.adjoin_left_contradiction hG hmax hfL i hSi hP hPab
      haA hnear hcopy hfanti
  · have hXi : ((Gx.neighborSet f ∩ striationVertices S T) ∩
        stripVertices (S i)).Nonempty := by
      obtain ⟨p, hpP, hfp⟩ := hnear
      have hpS := KnotFromTwist.mem_stripVertices_of_isSRung hP hpP.1
      exact ⟨p, ⟨hfp, Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, hpS⟩)⟩, hpS⟩
    have hfanti : ∀ k : Fin m, i ≠ k → VertexAnticomplete Gx f (stripVertices (S k)) := by
      intro k hik z hz hfz
      have hXk : ((Gx.neighborSet f ∩ striationVertices S T) ∩
          stripVertices (S k)).Nonempty :=
        ⟨z, ⟨hfz, Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨k, hz⟩)⟩, hz⟩
      exact hik (hone i k hXi hXk)
    rcases hSi : S i with ⟨A, C, B⟩
    have hbB : b ∈ B := by simpa [hSi] using hb
    exact Thm94ClosingContradiction.adjoin_right_contradiction hG hmax hfL i hSi hP hPab
      hbB hnear hcopy hfanti

/-! ### The *local* half of 9.4 -/

/-- **Everything the printed proof does after its running assumption** -/
theorem localForStriation_of_antirungs {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {f : V}
    (hs : Setup Gx S T f)
    (hanti : ∀ (j : Fin n) (Q : List V), IsSRung Gxᶜ (T j) Q →
      ∃ v ∈ Q, v ∉ Gx.neighborSet f ∩ striationVertices S T) :
    LocalForStriation Gx S T (Gx.neighborSet f ∩ striationVertices S T) :=
  ⟨fun i i' hi hi' => claim2 hs hanti i i' hi hi', hanti,
    closing hs hanti (fun i i' hi hi' => claim2 hs hanti i i' hi hi')⟩

end Workspace.ProofLemmas.Thm94Body
