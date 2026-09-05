/-  Proof attempt for statement 24.7 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 146).

    THE PAPER'S PROOF (paper/proofs/24_7.md, verbatim):

      "Proof.  Assume not, and choose a counterexample with X1 u X2 u X3 u F minimal.
       Suppose F contains an Xi-complete vertex for two values of i in {1,2,3}, say
       i = 1,2; and choose a path p1-...-pn of F such that p1 is X1-complete and pn is
       X2-complete, with n minimum.  So n >= 2.  From the minimality of F, F = V(P),
       and there is a vertex x1 in X1 such that p1 is its only neighbour in F, and
       there exists x2 in X2 such that pn is its only neighbour in F.  By 24.6 applied
       to the hole x2-x1-p1-...-pn-x2 and any x3 in X3, it follows that n = 2.  Let Q
       be an antipath between p1, p2 with interior in X3; since p1 has a nonneighbour
       x2 in X2, and p2 has a nonneighbour x1 in X1, it follows that x1-p2-Q-p1-x2 is
       an antipath of length >= 5, contrary to 24.5.
         So there is at most one i such that F contains Xi-complete vertices, and from
       the symmetry we may assume that F contains no X1- or X2-complete vertices.  We
       may also assume that all members of X1 have neighbours in F, and therefore
       |X1| >= 2; choose distinct x1, x1' in X1 such that X1 \ {x1}, X1 \ {x1'} are
       both anticonnected.  From the minimality of X1, there is a vertex f of F
       complete to two of X1 \ {x1}, X2, X3, and therefore complete to X1 \ {x1} and
       X3, and similarly a vertex f' of F complete to X1 \ {x1'} and X3.  Let P be a
       path in F between f, f'.  Since all vertices of X1 u X3 have neighbours in
       V(P), the minimality of F implies that F = V(P); and moreover, since all
       vertices of (X1 \ {x1}) u X3 are adjacent to f, the minimality of F implies
       that f' is the unique neighbour of x1 in F.  Similarly f is the unique
       neighbour of x1' in F.  Let Q be an antipath in X1 joining x1, x1'.  Since f
       has a nonneighbour x in X2, x-f-x1-Q-x1' is an antipath, and so Q has length 1,
       and hence x1, x1' are nonadjacent.  From the minimality of F, there exists x2
       in X2 with no neighbour in F \ {f}.  If x2 is also nonadjacent to f, then
       x2-x1-f'-P-f-x1'-x2 is a hole of length >= 6, and any member of X3 has three
       consecutive neighbours on it, contrary to G in F11.  But then x1 has two
       consecutive neighbours on the hole x1'-f-P-f'-x1-x2-x1', and this hole has
       length > 4, contrary to 24.6.  This proves 24.7."

    HOW IT MAPS ONTO THE LEAN PROOF.

    * "Assume not, and choose a counterexample with X1 u X2 u X3 u F minimal" is
      `by_contra` + `ExtremalChoice.exists_min_nat` over `Set V x Set V x Set V x Set V`
      with measure `(X1 u X2 u X3 u F).ncard`.  `Hyp` and `Concl` package the
      hypotheses and the conclusion; `hyp_swap12`, `hyp_swap23`, `concl_swap12`,
      `concl_swap23` implement the paper's repeated "from the symmetry we may assume",
      since both `Hyp` and `Concl` are symmetric in the three indices.
    * The first paragraph is `case_A`, reached when two of the three indices carry an
      Xi-complete vertex of F; the second is `case_B` (via `case_B_dispatch`, which
      supplies "we may also assume that all members of X1 have neighbours in F").
    * "choose a path of F ... with n minimum" and "let P be a path in F between f, f'"
      are `InducedPathExtraction.exists_isPathFrom_of_connected` (a *path* of the paper
      is an induced subgraph, so this is a real theorem, proved by minimising a chain
      list); "let Q be an antipath ... with interior in X3" is
      `InducedPathExtraction.exists_antipath_interior_in`; "let Q be an antipath in X1
      joining x1, x1'" is `exists_isAntipathFrom_of_anticonnected`.
    * "choose distinct x1, x1' in X1 such that X1 \ {x1}, X1 \ {x1'} are both
      anticonnected" is `NonCutVertices.exists_two_nonanticut` (two non-cut vertices of
      a connected graph, proved via a maximiser of the distance from a root).
    * Every "the minimality of F implies ..." is `shrink_F`; "from the minimality of
      X1" is `shrink_X1`; "there is a vertex x1 in X1 such that p1 is its only
      neighbour in F" is `front_end`, applied at each end of the path.
    * The three holes are built with `PrismBasics.isHoleList_of_path_add_two_vertices`
      (x2-x1-p1-...-pn-x2) and `PrismBasics.isHoleList_of_path_add_vertex` (the two
      holes of the second paragraph); the antipaths with `PathAttach.isPathFrom_cons`
      and `PathAttach.isPathFrom_cons_concat`, applied at `Gᶜ`.

    TWO DEVIATIONS FROM THE PRINTED TEXT, FORCED BY THE PRINTED TEXT.  Both are
    documented in full in `FIXES.md` §F5 and `AMBIGUITIES.md` §A25.

    (a) "x1-p2-Q-p1-x2 is an antipath of length >= 5, contrary to 24.5".  24.5 is a
        statement about a *path of G* plus an external vertex; the object built here is
        an antipath with no external vertex, and a 24.5 application needs a hole (as
        the paper's own derivation of 24.6 from 24.5 shows).  This proof instead uses
        the closing sentence of 24.6 -- "In particular, G has no antipath of length 4"
        -- together with the fact that a block of consecutive vertices of an induced
        path is an induced path (`exists_antipath_length_four`).  Note also that
        "length >= 5" is the vertex count; under the paper's convention the antipath
        has length >= 4.
    (b) "x1 has two consecutive neighbours on the hole x1'-f-P-f'-x1-x2-x1', and this
        hole has length > 4, contrary to 24.6".  In that branch x2 IS adjacent to f, so
        f x2 is a chord of that cycle and it is not a hole; and x1 lies ON the cycle, so
        it cannot be 24.6's external vertex z.  This proof uses the chord-free hole
        x2-f-P-f'-x1-x2 with external vertex x1' (whose neighbours f and x2 ARE
        consecutive on it), and takes its contradiction from the *second* conclusion of
        24.6 ("z has a third neighbour in C"), which x1' does not have.

    In both cases the case split, the objects and the cited result are the paper's; only
    the cycle / the packaged form of the citation is corrected.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.NonCutVertices
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.Statements.S24.Thm_24_6

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S24

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

/-! ### The hypothesis and conclusion of 24.7, packaged -/

variable {V : Type*}

/-- *"every member of `X` has a neighbour in `F`"*. -/
private def Nbrs (G : SimpleGraph V) (X F : Set V) : Prop := ∀ x ∈ X, ∃ f ∈ F, G.Adj x f

/-- *"for at least two values of `i ∈ {1,2,3}`, every member of `Xᵢ` has a neighbour in `F`"*. -/
private def TwoOf (G : SimpleGraph V) (X₁ X₂ X₃ F : Set V) : Prop :=
  (Nbrs G X₁ F ∧ Nbrs G X₂ F) ∨ (Nbrs G X₁ F ∧ Nbrs G X₃ F) ∨ (Nbrs G X₂ F ∧ Nbrs G X₃ F)

/-- All the hypotheses of 24.7 that mention `X₁, X₂, X₃, F`. -/
private def Hyp (G : SimpleGraph V) (X₁ X₂ X₃ F : Set V) : Prop :=
  Disjoint X₁ X₂ ∧ Disjoint X₁ X₃ ∧ Disjoint X₂ X₃ ∧
  X₁.Nonempty ∧ X₂.Nonempty ∧ X₃.Nonempty ∧
  AnticonnectedSet G X₁ ∧ AnticonnectedSet G X₂ ∧ AnticonnectedSet G X₃ ∧
  Complete G X₁ X₂ ∧ Complete G X₁ X₃ ∧ Complete G X₂ X₃ ∧
  F ⊆ (X₁ ∪ X₂ ∪ X₃)ᶜ ∧ ConnectedSet G F ∧ TwoOf G X₁ X₂ X₃ F

/-- The conclusion of 24.7. -/
private def Concl (G : SimpleGraph V) (X₁ X₂ X₃ F : Set V) : Prop :=
  ∃ f ∈ F, (VertexComplete G f X₁ ∧ VertexComplete G f X₂) ∨
    (VertexComplete G f X₁ ∧ VertexComplete G f X₃) ∨
    (VertexComplete G f X₂ ∧ VertexComplete G f X₃)

/-! ### The symmetry of `Hyp` and `Concl` in the three indices -/

private theorem complete_symm {G : SimpleGraph V} {X Y : Set V} (h : Complete G X Y) :
    Complete G Y X := fun y hy x hx => (h x hx y hy).symm

private theorem union3_swap12 (A B C : Set V) : B ∪ A ∪ C = A ∪ B ∪ C := by
  ext z; simp only [Set.mem_union]; tauto

private theorem union3_swap23 (A B C : Set V) : A ∪ C ∪ B = A ∪ B ∪ C := by
  ext z; simp only [Set.mem_union]; tauto

private theorem union4_swap12 (A B C D : Set V) : B ∪ A ∪ C ∪ D = A ∪ B ∪ C ∪ D := by
  ext z; simp only [Set.mem_union]; tauto

private theorem union4_swap23 (A B C D : Set V) : A ∪ C ∪ B ∪ D = A ∪ B ∪ C ∪ D := by
  ext z; simp only [Set.mem_union]; tauto

private theorem hyp_swap12 {G : SimpleGraph V} {A B C D : Set V} (h : Hyp G A B C D) :
    Hyp G B A C D := by
  obtain ⟨d12, d13, d23, n1, n2, n3, a1, a2, a3, c12, c13, c23, hsub, hconn, htwo⟩ := h
  refine ⟨d12.symm, d23, d13, n2, n1, n3, a2, a1, a3, complete_symm c12, c23, c13, ?_, hconn, ?_⟩
  · rw [union3_swap12]; exact hsub
  · rcases htwo with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inr ⟨h1, h3⟩)
    · exact Or.inr (Or.inl ⟨h2, h3⟩)

private theorem hyp_swap23 {G : SimpleGraph V} {A B C D : Set V} (h : Hyp G A B C D) :
    Hyp G A C B D := by
  obtain ⟨d12, d13, d23, n1, n2, n3, a1, a2, a3, c12, c13, c23, hsub, hconn, htwo⟩ := h
  refine ⟨d13, d12, d23.symm, n1, n3, n2, a1, a3, a2, c13, c12, complete_symm c23, ?_, hconn, ?_⟩
  · rw [union3_swap23]; exact hsub
  · rcases htwo with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr (Or.inr ⟨h3, h2⟩)

private theorem concl_swap12 {G : SimpleGraph V} {A B C D : Set V} (h : Concl G A B C D) :
    Concl G B A C D := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, by tauto⟩

private theorem concl_swap23 {G : SimpleGraph V} {A B C D : Set V} (h : Concl G A B C D) :
    Concl G A C B D := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, by tauto⟩

/-! ### Small list / antipath utilities -/

private theorem mem_tail_iff {l : List V} (hnd : l.Nodup) {x : V} (hx : l.head? = some x)
    {z : V} : z ∈ l.tail ↔ (z ∈ l ∧ z ≠ x) := by
  cases l with
  | nil => simp at hx
  | cons y t =>
      have hyx : y = x := by simpa using hx
      subst hyx
      have hnd' := List.nodup_cons.mp hnd
      simp only [List.tail_cons]
      constructor
      · intro h
        refine ⟨List.mem_cons_of_mem _ h, ?_⟩
        rintro rfl
        exact hnd'.1 h
      · rintro ⟨h, hne⟩
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hne
        · exact h

/-- An antipath on at least five vertices contains an antipath of length exactly `4`, which
24.6 forbids.  (A block of consecutive vertices of an induced path is an induced path.) -/
private theorem exists_antipath_length_four {G : SimpleGraph V} {R : List V}
    (hR : IsAntipathList G R) (hlen : 5 ≤ R.length) :
    ∃ q : List V, IsAntipathList G q ∧ pathLength q = 4 := by
  refine ⟨List.take (4 - 0 + 1) (List.drop 0 R),
    PathBasics.isPathList_slice hR (by omega) (by omega), ?_⟩
  rw [PathBasics.pathLength_eq,
    PathBasics.length_slice R (i := 0) (j := 4) (by omega) (by omega)]

/-- A path whose two ends differ has at least two vertices. -/
private theorem two_le_length_of_ends_ne {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (huv : u ≠ v) : 2 ≤ p.length := by
  by_contra hlt
  have h1 : p.length = 1 := by
    have := PathBasics.path_length_pos hp.1
    omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
  rw [hx] at hp
  have h2 : x = u := by simpa using hp.2.1
  have h3 : x = v := by simpa using hp.2.2
  exact huv (h2.symm.trans h3)

/-! ### The two halves of the printed proof -/

variable [Fintype V] [DecidableEq V]

/-- *"there is a vertex `x₁ ∈ X₁` such that `p₁` is its only neighbour in `F`"* — for a
counterexample whose `F` is exactly the vertex set of the path `q` from `a` to `b`, with `a`
being `A`-complete and `b` being `B`-complete.  Applied once at each end of the path (the second
time to `q.reverse`, with `A` and `B` interchanged). -/
private theorem front_end {G : SimpleGraph V} {A B C D : Set V}
    (hH : Hyp G A B C D) (hNo : ¬ Concl G A B C D)
    (hmin : ∀ Z₁ Z₂ Z₃ E : Set V, Hyp G Z₁ Z₂ Z₃ E → ¬ Concl G Z₁ Z₂ Z₃ E →
        (A ∪ B ∪ C ∪ D).ncard ≤ (Z₁ ∪ Z₂ ∪ Z₃ ∪ E).ncard)
    {q : List V} {a b : V} (hq : IsPathFrom G q a b) (hab : a ≠ b)
    (hDeq : D = {z : V | z ∈ q})
    (haA : VertexComplete G a A) (hbB : VertexComplete G b B) :
    ∃ x ∈ A, ∀ f ∈ D, G.Adj x f → f = a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23, hDsub, hDconn, htwo⟩ := hH
  have hnd : q.Nodup := PathBasics.path_nodup hq.1
  have hmemtail : ∀ z : V, z ∈ q.tail ↔ (z ∈ q ∧ z ≠ a) := fun z => mem_tail_iff hnd hq.2.1
  have hD'D : {z : V | z ∈ q.tail} ⊆ D := by
    intro z hz
    rw [hDeq]
    exact ((hmemtail z).mp hz).1
  have haD : a ∈ D := by rw [hDeq]; exact (PathBasics.isPathFrom_ends_mem hq).1
  have hbD : b ∈ D := by rw [hDeq]; exact (PathBasics.isPathFrom_ends_mem hq).2
  have haD' : a ∉ {z : V | z ∈ q.tail} := fun hz => ((hmemtail a).mp hz).2 rfl
  have hinD' : ∀ z ∈ D, z ≠ a → z ∈ {z : V | z ∈ q.tail} := by
    intro z hz hza
    rw [hDeq] at hz
    exact (hmemtail z).mpr ⟨hz, hza⟩
  have hqlen : 2 ≤ q.length := by
    by_contra hlt
    have h1 : q.length = 1 := by
      have := PathBasics.path_length_pos hq.1
      omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
    rw [hx] at hq
    have h2 : x = a := by simpa using hq.2.1
    have h3 : x = b := by simpa using hq.2.2
    exact hab (h2.symm.trans h3)
  have htailpath : IsPathList G q.tail := by
    have h := PathBasics.isPathList_drop hq.1 (k := 1) (by omega)
    rwa [List.drop_one] at h
  have hbD' : b ∈ {z : V | z ∈ q.tail} := hinD' b hbD hab.symm
  have hHyp' : Hyp G A B C {z : V | z ∈ q.tail} := by
    refine ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23,
      fun z hz => hDsub (hD'D hz),
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList htailpath, Or.inl ⟨?_, ?_⟩⟩
    · intro x hx
      obtain ⟨f, hfD, hadj, hfa⟩ := hcon x hx
      exact ⟨f, hinD' f hfD hfa, hadj⟩
    · intro x hx
      exact ⟨b, hbD', (hbB x hx).symm⟩
  have hNo' : ¬ Concl G A B C {z : V | z ∈ q.tail} := by
    rintro ⟨f, hf, hrest⟩
    exact hNo ⟨f, hD'D hf, hrest⟩
  have hle := hmin A B C {z : V | z ∈ q.tail} hHyp' hNo'
  have hstrict : (A ∪ B ∪ C ∪ {z : V | z ∈ q.tail}).ncard < (A ∪ B ∪ C ∪ D).ncard := by
    refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (Set.toFinite _)
    · intro w hw
      rcases hw with h | h
      · exact Or.inl h
      · exact Or.inr (hD'D h)
    · intro hsub
      rcases hsub (Or.inr haD) with h | h
      · exact hDsub haD h
      · exact haD' h
  omega

/-- The vertex set of a path minus one of its ends: `q.tail` is a path, and its vertices are
those of `q` other than the head. -/
private theorem tail_data {G : SimpleGraph V} {q : List V} {u v : V} (hq : IsPathFrom G q u v)
    (huv : u ≠ v) :
    IsPathList G q.tail ∧ (∀ z : V, z ∈ q.tail ↔ (z ∈ q ∧ z ≠ u)) := by
  have hnd : q.Nodup := PathBasics.path_nodup hq.1
  have hqlen : 2 ≤ q.length := two_le_length_of_ends_ne hq huv
  refine ⟨?_, fun z => mem_tail_iff hnd hq.2.1⟩
  have h := PathBasics.isPathList_drop hq.1 (k := 1) (by omega)
  rwa [List.drop_one] at h

/-- *"the minimality of `F` implies …"*: a proper connected subset `D'` of `F` that still has
two of the three `Xᵢ` with all their vertices having neighbours in it contradicts minimality. -/
private theorem shrink_F {G : SimpleGraph V} {A B C D : Set V}
    (hH : Hyp G A B C D) (hNo : ¬ Concl G A B C D)
    (hmin : ∀ Z₁ Z₂ Z₃ E : Set V, Hyp G Z₁ Z₂ Z₃ E → ¬ Concl G Z₁ Z₂ Z₃ E →
        (A ∪ B ∪ C ∪ D).ncard ≤ (Z₁ ∪ Z₂ ∪ Z₃ ∪ E).ncard)
    {D' : Set V} (hD'D : D' ⊆ D) {w : V} (hwD : w ∈ D) (hwD' : w ∉ D')
    (hconn : ConnectedSet G D') (htwo' : TwoOf G A B C D') : False := by
  obtain ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23, hDsub, hDconn, htwo⟩ := hH
  have hHyp' : Hyp G A B C D' :=
    ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23,
      fun z hz => hDsub (hD'D hz), hconn, htwo'⟩
  have hNo' : ¬ Concl G A B C D' := by
    rintro ⟨g, hg, hrest⟩
    exact hNo ⟨g, hD'D hg, hrest⟩
  have hle := hmin A B C D' hHyp' hNo'
  have hstrict : (A ∪ B ∪ C ∪ D').ncard < (A ∪ B ∪ C ∪ D).ncard := by
    refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (Set.toFinite _)
    · intro z hz
      rcases hz with h | h
      · exact Or.inl h
      · exact Or.inr (hD'D h)
    · intro hsub
      rcases hsub (Or.inr hwD) with h | h
      · exact hDsub hwD h
      · exact hwD' h
  omega

/-- *"From the minimality of `X₁`, there is a vertex `f` of `F` complete to two of
`X₁ \ {x₁}`, `X₂`, `X₃`"*: shrinking `X₁` gives a strictly smaller instance, which by minimality
is not a counterexample. -/
private theorem shrink_X1 {G : SimpleGraph V} {A B C D : Set V} (hH : Hyp G A B C D)
    (hmin : ∀ Z₁ Z₂ Z₃ E : Set V, Hyp G Z₁ Z₂ Z₃ E → ¬ Concl G Z₁ Z₂ Z₃ E →
        (A ∪ B ∪ C ∪ D).ncard ≤ (Z₁ ∪ Z₂ ∪ Z₃ ∪ E).ncard)
    {A' : Set V} (hA'A : A' ⊆ A) {w : V} (hwA : w ∈ A) (hwA' : w ∉ A')
    (hne' : A'.Nonempty) (hanti' : AnticonnectedSet G A') (hnbr' : Nbrs G A' D) :
    Concl G A' B C D := by
  by_contra hcon
  obtain ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23, hDsub, hDconn, htwo⟩ := hH
  have hBC : Nbrs G B D ∨ Nbrs G C D := by
    rcases htwo with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  have hHyp' : Hyp G A' B C D := by
    refine ⟨d12.mono_left hA'A, d13.mono_left hA'A, d23, hne', n2, n3, hanti', ac2, ac3,
      fun x hx => c12 x (hA'A hx), fun x hx => c13 x (hA'A hx), c23, ?_, hDconn, ?_⟩
    · intro z hz hmem
      refine hDsub hz ?_
      rcases hmem with h | h
      · rcases h with h | h
        · exact Or.inl (Or.inl (hA'A h))
        · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rcases hBC with h | h
      · exact Or.inl ⟨hnbr', h⟩
      · exact Or.inr (Or.inl ⟨hnbr', h⟩)
  have hle := hmin A' B C D hHyp' hcon
  have hstrict : (A' ∪ B ∪ C ∪ D).ncard < (A ∪ B ∪ C ∪ D).ncard := by
    refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (Set.toFinite _)
    · intro z hz
      rcases hz with h | h
      · rcases h with h | h
        · rcases h with h | h
          · exact Or.inl (Or.inl (Or.inl (hA'A h)))
          · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · intro hsub
      have hw : w ∈ A' ∪ B ∪ C ∪ D := hsub (Or.inl (Or.inl (Or.inl hwA)))
      rcases hw with h | h
      · rcases h with h | h
        · rcases h with h | h
          · exact hwA' h
          · exact Set.disjoint_left.mp d12 hwA h
        · exact Set.disjoint_left.mp d13 hwA h
      · exact hDsub h (Or.inl (Or.inl hwA))
  omega

private theorem case_A {G : SimpleGraph V} (hG : InF11 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    {A B C D : Set V} (hH : Hyp G A B C D) (hNo : ¬ Concl G A B C D)
    (hmin : ∀ Z₁ Z₂ Z₃ E : Set V, Hyp G Z₁ Z₂ Z₃ E → ¬ Concl G Z₁ Z₂ Z₃ E →
        (A ∪ B ∪ C ∪ D).ncard ≤ (Z₁ ∪ Z₂ ∪ Z₃ ∪ E).ncard)
    (hcA : ∃ f ∈ D, VertexComplete G f A) (hcB : ∃ f ∈ D, VertexComplete G f B) :
    False := by
  obtain ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23, hDsub, hDconn, htwo⟩ := hH
  have hHfull : Hyp G A B C D :=
    ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23, hDsub, hDconn, htwo⟩
  obtain ⟨f₀, hf₀D, hf₀A⟩ := hcA
  obtain ⟨f₁, hf₁D, hf₁B⟩ := hcB
  obtain ⟨p₀, hp₀, hp₀D⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hDconn hf₀D hf₁D
  -- "choose a path `p₁-⋯-pₙ` of `F` such that `p₁` is `X₁`-complete and `pₙ` is `X₂`-complete,
  -- with `n` minimum"
  obtain ⟨⟨p, a, b⟩, hspec, hpmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun t : List V × V × V =>
        IsPathFrom G t.1 t.2.1 t.2.2 ∧ VertexComplete G t.2.1 A ∧ VertexComplete G t.2.2 B ∧
          ∀ z ∈ t.1, z ∈ D)
      (fun t : List V × V × V => t.1.length)
      ⟨(p₀, f₀, f₁), hp₀, hf₀A, hf₁B, hp₀D⟩
  obtain ⟨hp, haA, hbB, hpD⟩ : IsPathFrom G p a b ∧ VertexComplete G a A ∧
      VertexComplete G b B ∧ ∀ z ∈ p, z ∈ D := hspec
  have haD : a ∈ D := hpD a (PathBasics.isPathFrom_ends_mem hp).1
  have hbD : b ∈ D := hpD b (PathBasics.isPathFrom_ends_mem hp).2
  -- "So `n ≥ 2`."
  have hab : a ≠ b := by
    rintro rfl
    exact hNo ⟨a, haD, Or.inl ⟨haA, hbB⟩⟩
  have hplen : 2 ≤ p.length := two_le_length_of_ends_ne hp hab
  -- "From the minimality of `F`, `F = V(P)`"
  have hDeq : D = {z : V | z ∈ p} := by
    refine Set.Subset.antisymm ?_ hpD
    by_contra hsub
    obtain ⟨z₀, hz₀D, hz₀p⟩ := Set.not_subset.mp hsub
    have hHyp' : Hyp G A B C {z : V | z ∈ p} := by
      refine ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23,
        fun z hz => hDsub (hpD z hz),
        InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp.1, Or.inl ⟨?_, ?_⟩⟩
      · exact fun x hx => ⟨a, (PathBasics.isPathFrom_ends_mem hp).1, (haA x hx).symm⟩
      · exact fun x hx => ⟨b, (PathBasics.isPathFrom_ends_mem hp).2, (hbB x hx).symm⟩
    have hNo' : ¬ Concl G A B C {z : V | z ∈ p} := by
      rintro ⟨f, hf, hrest⟩
      exact hNo ⟨f, hpD f hf, hrest⟩
    have hle := hmin A B C {z : V | z ∈ p} hHyp' hNo'
    have hstrict : (A ∪ B ∪ C ∪ {z : V | z ∈ p}).ncard < (A ∪ B ∪ C ∪ D).ncard := by
      refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (Set.toFinite _)
      · intro w hw
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr (hpD w h)
      · intro hsub2
        rcases hsub2 (Or.inr hz₀D) with h | h
        · exact hDsub hz₀D h
        · exact hz₀p h
    omega
  -- "there is a vertex `x₁ ∈ X₁` such that `p₁` is its only neighbour in `F`, and there exists
  -- `x₂ ∈ X₂` such that `pₙ` is its only neighbour in `F`"
  obtain ⟨x₁, hx₁A, hx₁uniq⟩ := front_end hHfull hNo hmin hp hab hDeq haA hbB
  have hrevmem : {z : V | z ∈ p.reverse} = {z : V | z ∈ p} := by ext z; simp
  obtain ⟨x₂, hx₂B, hx₂uniq⟩ :=
    front_end (hyp_swap12 hHfull) (fun hc => hNo (concl_swap12 hc))
      (by
        intro Z₁ Z₂ Z₃ E hz1 hz2
        rw [union4_swap12]
        exact hmin Z₁ Z₂ Z₃ E hz1 hz2)
      (PathBasics.isPathFrom_reverse hp) hab.symm (by rw [hDeq, ← hrevmem]) hbB haA
  -- the hole `x₂-x₁-p₁-⋯-pₙ-x₂`
  have hx₁np : x₁ ∉ p := fun hz => hDsub (hpD x₁ hz) (Or.inl (Or.inl hx₁A))
  have hx₂np : x₂ ∉ p := fun hz => hDsub (hpD x₂ hz) (Or.inl (Or.inr hx₂B))
  have hadj_x₁a : G.Adj x₁ a := (haA x₁ hx₁A).symm
  have hadj_x₂b : G.Adj x₂ b := (hbB x₂ hx₂B).symm
  have hadj_x₁x₂ : G.Adj x₁ x₂ := c12 x₁ hx₁A x₂ hx₂B
  have hnadj_x₁b : ¬ G.Adj x₁ b := fun hadj => hab.symm (hx₁uniq b hbD hadj)
  have hnadj_x₂a : ¬ G.Adj x₂ a := fun hadj => hab (hx₂uniq a haD hadj)
  have hint₁ : ∀ z ∈ SPGT.interior p, ¬ G.Adj x₁ z := by
    intro z hz hadj
    rw [PathBasics.mem_interior_iff_of_pathFrom hp] at hz
    exact hz.2.1 (hx₁uniq z (hpD z hz.1) hadj)
  have hint₂ : ∀ z ∈ SPGT.interior p, ¬ G.Adj x₂ z := by
    intro z hz hadj
    rw [PathBasics.mem_interior_iff_of_pathFrom hp] at hz
    exact hz.2.2 (hx₂uniq z (hpD z hz.1) hadj)
  have hpne : p ≠ [] := PathBasics.path_ne_nil hp.1
  have hpl1 : 1 ≤ pathLength p := by rw [PathBasics.pathLength_eq]; omega
  have hhole : IsHoleList G (x₂ :: x₁ :: p) :=
    PrismBasics.isHoleList_of_path_add_two_vertices hp hpl1 hadj_x₁a hadj_x₂b hadj_x₁x₂
      hx₁np hx₂np hnadj_x₁b hnadj_x₂a hint₁ hint₂
  -- "By 24.6 applied to the hole `x₂-x₁-p₁-⋯-pₙ-x₂` and any `x₃ ∈ X₃`, it follows that `n = 2`."
  obtain ⟨x₃, hx₃C⟩ := n3
  have hx₃notin : x₃ ∉ (x₂ :: x₁ :: p) := by
    intro hz
    rcases List.mem_cons.mp hz with h | hz1
    · exact Set.disjoint_left.mp d23 hx₂B (by rw [← h]; exact hx₃C)
    rcases List.mem_cons.mp hz1 with h | hz2
    · exact Set.disjoint_left.mp d13 hx₁A (by rw [← h]; exact hx₃C)
    · exact hDsub (hpD x₃ hz2) (Or.inr hx₃C)
  have h246 := SPGT.thm_24_6 G hG hbsp
  have hkey := h246.1 (x₂ :: x₁ :: p) hhole x₃ x₁ x₂ hx₃notin (by simp) (by simp)
    (c13 x₁ hx₁A x₃ hx₃C).symm (c23 x₂ hx₂B x₃ hx₃C).symm hadj_x₁x₂
  have hplen1 : pathLength p = 1 := by
    have h := hkey.1
    rw [PrismBasics.holeLength_cons_cons x₁ x₂ hpne] at h
    omega
  have hadjab : G.Adj a b := PathBasics.isPathFrom_ends_adj_of_length_one hp hplen1
  -- "Let `Q` be an antipath between `p₁, p₂` with interior in `X₃`"
  have haNC : a ∉ C := fun h => hDsub haD (Or.inr h)
  have hbNC : b ∉ C := fun h => hDsub hbD (Or.inr h)
  have haC : ∃ c ∈ C, ¬ G.Adj a c := by
    by_contra hc
    push Not at hc
    exact hNo ⟨a, haD, Or.inr (Or.inl ⟨haA, hc⟩)⟩
  have hbC : ∃ c ∈ C, ¬ G.Adj b c := by
    by_contra hc
    push Not at hc
    exact hNo ⟨b, hbD, Or.inr (Or.inr ⟨hbB, hc⟩)⟩
  obtain ⟨Q, hQ, hQint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in ac3 haNC hbNC haC hbC
  have hQ' : IsPathFrom Gᶜ Q a b := hQ
  have hQlen : 2 ≤ pathLength Q := by
    have h2 : 2 ≤ Q.length := two_le_length_of_ends_ne hQ' hab
    have hne1 : pathLength Q ≠ 1 := fun h1 =>
      (PathBasics.isPathFrom_ends_adj_of_length_one hQ' h1).2 hadjab
    have hpl : pathLength Q = Q.length - 1 := PathBasics.pathLength_eq Q
    omega
  have hQmem : ∀ z ∈ Q, z = a ∨ z = b ∨ z ∈ C := by
    intro z hz
    by_cases hza : z = a
    · exact Or.inl hza
    by_cases hzb : z = b
    · exact Or.inr (Or.inl hzb)
    · exact Or.inr (Or.inr (hQint z
        ((PathBasics.mem_interior_iff_of_pathFrom hQ').mpr ⟨hz, hza, hzb⟩)))
  -- "`x₁-p₂-Q-p₁-x₂` is an antipath of length ≥ 4"
  have hQrev : IsPathFrom Gᶜ Q.reverse b a := PathBasics.isPathFrom_reverse hQ'
  have hx₁NC : x₁ ∉ C := Set.disjoint_left.mp d13 hx₁A
  have hx₂NC : x₂ ∉ C := Set.disjoint_left.mp d23 hx₂B
  have hx₁ne_a : x₁ ≠ a := fun h => hDsub haD (Or.inl (Or.inl (by rw [← h]; exact hx₁A)))
  have hx₁ne_b : x₁ ≠ b := fun h => hDsub hbD (Or.inl (Or.inl (by rw [← h]; exact hx₁A)))
  have hx₂ne_a : x₂ ≠ a := fun h => hDsub haD (Or.inl (Or.inr (by rw [← h]; exact hx₂B)))
  have hx₂ne_b : x₂ ≠ b := fun h => hDsub hbD (Or.inl (Or.inr (by rw [← h]; exact hx₂B)))
  have hx₁nQ : x₁ ∉ Q.reverse := by
    intro hz
    rcases hQmem x₁ (List.mem_reverse.mp hz) with h | h | h
    · exact hx₁ne_a h
    · exact hx₁ne_b h
    · exact hx₁NC h
  have hx₂nQ : x₂ ∉ Q.reverse := by
    intro hz
    rcases hQmem x₂ (List.mem_reverse.mp hz) with h | h | h
    · exact hx₂ne_a h
    · exact hx₂ne_b h
    · exact hx₂NC h
  have hR : IsPathFrom Gᶜ (x₁ :: (Q.reverse ++ [x₂])) x₁ x₂ := by
    refine PathAttach.isPathFrom_cons_concat hQrev ⟨hx₁ne_b, hnadj_x₁b⟩ ⟨hx₂ne_a, hnadj_x₂a⟩
      (fun h => h.2 hadj_x₁x₂)
      (fun h => (Set.disjoint_left.mp d12 hx₁A) (by rw [h]; exact hx₂B)) hx₁nQ hx₂nQ ?_ ?_
    · intro z hz hzb hadj
      rcases hQmem z (List.mem_reverse.mp hz) with h | h | h
      · exact hadj.2 (by rw [h]; exact hadj_x₁a)
      · exact hzb h
      · exact hadj.2 (c13 x₁ hx₁A z h)
    · intro z hz hza hadj
      rcases hQmem z (List.mem_reverse.mp hz) with h | h | h
      · exact hza h
      · exact hadj.2 (by rw [h]; exact hadj_x₂b)
      · exact hadj.2 (c23 x₂ hx₂B z h)
  have hRlen : 5 ≤ (x₁ :: (Q.reverse ++ [x₂])).length := by
    rw [PathAttach.length_cons_append_singleton, List.length_reverse]
    have hpl : pathLength Q = Q.length - 1 := PathBasics.pathLength_eq Q
    omega
  exact h246.2 (exists_antipath_length_four hR.1 hRlen)

private theorem case_B {G : SimpleGraph V} (hG : InF11 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    {A B C D : Set V} (hH : Hyp G A B C D) (hNo : ¬ Concl G A B C D)
    (hmin : ∀ Z₁ Z₂ Z₃ E : Set V, Hyp G Z₁ Z₂ Z₃ E → ¬ Concl G Z₁ Z₂ Z₃ E →
        (A ∪ B ∪ C ∪ D).ncard ≤ (Z₁ ∪ Z₂ ∪ Z₃ ∪ E).ncard)
    (hnoA : ¬ ∃ f ∈ D, VertexComplete G f A)
    (hnoB : ¬ ∃ f ∈ D, VertexComplete G f B)
    (hnbrA : Nbrs G A D) :
    False := by
  obtain ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23, hDsub, hDconn, htwo⟩ := hH
  have hHfull : Hyp G A B C D :=
    ⟨d12, d13, d23, n1, n2, n3, ac1, ac2, ac3, c12, c13, c23, hDsub, hDconn, htwo⟩
  -- "We may also assume that all members of `X₁` have neighbours in `F`, and therefore `|X₁| ≥ 2`"
  have hnsub : ¬ A.Subsingleton := by
    intro hsub
    obtain ⟨x, hx⟩ := n1
    obtain ⟨g, hgD, hadj⟩ := hnbrA x hx
    refine hnoA ⟨g, hgD, ?_⟩
    intro y hy
    rw [hsub hy hx]
    exact hadj.symm
  -- "choose distinct `x₁, x₁' ∈ X₁` such that `X₁\{x₁}`, `X₁\{x₁'}` are both anticonnected"
  obtain ⟨x₁, hx₁A, x₁', hx₁'A, hx₁ne, hanti1, hanti1'⟩ :=
    NonCutVertices.exists_two_nonanticut ac1 hnsub
  have hne1 : (A \ {x₁}).Nonempty := ⟨x₁', hx₁'A, fun h => hx₁ne h.symm⟩
  have hne1' : (A \ {x₁'}).Nonempty := ⟨x₁, hx₁A, fun h => hx₁ne h⟩
  -- "From the minimality of `X₁`, there is a vertex `f` of `F` complete to two of
  -- `X₁\{x₁}, X₂, X₃`, and therefore complete to `X₁\{x₁}` and `X₃`"
  obtain ⟨f, hfD, hfcases⟩ :=
    shrink_X1 hHfull hmin Set.diff_subset hx₁A (by simp) hne1 hanti1 (fun x hx => hnbrA x hx.1)
  have hfB : ¬ VertexComplete G f B := fun h => hnoB ⟨f, hfD, h⟩
  have hfA1 : VertexComplete G f (A \ {x₁}) ∧ VertexComplete G f C := by
    rcases hfcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 hfB
    · exact ⟨h1, h2⟩
    · exact absurd h1 hfB
  obtain ⟨f', hf'D, hf'cases⟩ :=
    shrink_X1 hHfull hmin Set.diff_subset hx₁'A (by simp) hne1' hanti1' (fun x hx => hnbrA x hx.1)
  have hf'B : ¬ VertexComplete G f' B := fun h => hnoB ⟨f', hf'D, h⟩
  have hf'A1 : VertexComplete G f' (A \ {x₁'}) ∧ VertexComplete G f' C := by
    rcases hf'cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 hf'B
    · exact ⟨h1, h2⟩
    · exact absurd h1 hf'B
  have hff' : f ≠ f' := by
    intro he
    refine hNo ⟨f, hfD, Or.inr (Or.inl ⟨?_, hfA1.2⟩)⟩
    intro y hy
    by_cases hy1 : y = x₁
    · rw [he]
      exact hf'A1.1 y ⟨hy, fun h => hx₁ne (hy1.symm.trans h)⟩
    · exact hfA1.1 y ⟨hy, hy1⟩
  -- "Let `P` be a path in `F` between `f, f'`."
  obtain ⟨P, hP, hPD⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hDconn hfD hf'D
  have hPlen : 2 ≤ P.length := two_le_length_of_ends_ne hP hff'
  have hfP : f ∈ P := (PathBasics.isPathFrom_ends_mem hP).1
  have hf'P : f' ∈ P := (PathBasics.isPathFrom_ends_mem hP).2
  have hx₁f' : G.Adj x₁ f' := (hf'A1.1 x₁ ⟨hx₁A, fun h => hx₁ne h⟩).symm
  have hx₁'f : G.Adj x₁' f := (hfA1.1 x₁' ⟨hx₁'A, fun h => hx₁ne h.symm⟩).symm
  -- "Since all vertices of `X₁ ∪ X₃` have neighbours in `V(P)`, the minimality of `F` implies
  -- that `F = V(P)`"
  have hnbrA_P : Nbrs G A {z : V | z ∈ P} := by
    intro y hy
    by_cases hy1 : y = x₁
    · exact ⟨f', hf'P, (hf'A1.1 y ⟨hy, fun h => hx₁ne (hy1.symm.trans h)⟩).symm⟩
    · exact ⟨f, hfP, (hfA1.1 y ⟨hy, hy1⟩).symm⟩
  have hnbrC_P : Nbrs G C {z : V | z ∈ P} := fun y hy => ⟨f, hfP, (hfA1.2 y hy).symm⟩
  have hDeq : D = {z : V | z ∈ P} := by
    refine Set.Subset.antisymm ?_ hPD
    by_contra hsub
    obtain ⟨z₀, hz₀D, hz₀P⟩ := Set.not_subset.mp hsub
    exact shrink_F hHfull hNo hmin hPD hz₀D hz₀P
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hP.1)
      (Or.inr (Or.inl ⟨hnbrA_P, hnbrC_P⟩))
  -- "the minimality of `F` implies that `f'` is the unique neighbour of `x₁` in `F`"
  obtain ⟨hPrevtail, hPrevmem⟩ := tail_data (PathBasics.isPathFrom_reverse hP) hff'.symm
  have hDf'sub : {z : V | z ∈ P.reverse.tail} ⊆ D := by
    intro z hz
    rw [hDeq]
    exact List.mem_reverse.mp ((hPrevmem z).mp hz).1
  have hf'nin : f' ∉ {z : V | z ∈ P.reverse.tail} := fun hz => ((hPrevmem f').mp hz).2 rfl
  have hinDf' : ∀ z ∈ D, z ≠ f' → z ∈ {z : V | z ∈ P.reverse.tail} := by
    intro z hz hzf
    rw [hDeq] at hz
    exact (hPrevmem z).mpr ⟨List.mem_reverse.mpr hz, hzf⟩
  have hfin' : f ∈ {z : V | z ∈ P.reverse.tail} := hinDf' f hfD hff'
  have hx₁uniq : ∀ g ∈ D, G.Adj x₁ g → g = f' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hgD, hadj, hgf⟩ := hcon
    refine shrink_F hHfull hNo hmin hDf'sub hf'D hf'nin
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hPrevtail)
      (Or.inr (Or.inl ⟨?_, ?_⟩))
    · intro y hy
      by_cases hy1 : y = x₁
      · exact ⟨g, hinDf' g hgD hgf, by rw [hy1]; exact hadj⟩
      · exact ⟨f, hfin', (hfA1.1 y ⟨hy, hy1⟩).symm⟩
    · exact fun y hy => ⟨f, hfin', (hfA1.2 y hy).symm⟩
  -- "Similarly `f` is the unique neighbour of `x₁'` in `F`."
  obtain ⟨hPtail, hPmem⟩ := tail_data hP hff'
  have hDfsub : {z : V | z ∈ P.tail} ⊆ D := by
    intro z hz
    rw [hDeq]
    exact ((hPmem z).mp hz).1
  have hfnin : f ∉ {z : V | z ∈ P.tail} := fun hz => ((hPmem f).mp hz).2 rfl
  have hinDf : ∀ z ∈ D, z ≠ f → z ∈ {z : V | z ∈ P.tail} := by
    intro z hz hzf
    rw [hDeq] at hz
    exact (hPmem z).mpr ⟨hz, hzf⟩
  have hf'in : f' ∈ {z : V | z ∈ P.tail} := hinDf f' hf'D hff'.symm
  have hx₁'uniq : ∀ g ∈ D, G.Adj x₁' g → g = f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hgD, hadj, hgf⟩ := hcon
    refine shrink_F hHfull hNo hmin hDfsub hfD hfnin
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hPtail)
      (Or.inr (Or.inl ⟨?_, ?_⟩))
    · intro y hy
      by_cases hy1 : y = x₁'
      · exact ⟨g, hinDf g hgD hgf, by rw [hy1]; exact hadj⟩
      · exact ⟨f', hf'in, (hf'A1.1 y ⟨hy, hy1⟩).symm⟩
    · exact fun y hy => ⟨f', hf'in, (hf'A1.2 y hy).symm⟩
  -- "Let `Q` be an antipath in `X₁` joining `x₁, x₁'`."
  obtain ⟨Q, hQ, hQA⟩ :=
    InducedPathExtraction.exists_isAntipathFrom_of_anticonnected ac1 hx₁A hx₁'A
  have hQ' : IsPathFrom Gᶜ Q x₁ x₁' := hQ
  -- "Since `f` has a nonneighbour `x ∈ X₂`, `x-f-x₁-Q-x₁'` is an antipath"
  obtain ⟨xb, hxbB, hxbf⟩ : ∃ x ∈ B, ¬ G.Adj f x := by
    by_contra hc
    push Not at hc
    exact hnoB ⟨f, hfD, hc⟩
  have hfnQ : f ∉ Q := fun hz => hDsub hfD (Or.inl (Or.inl (hQA f hz)))
  have hnadj_f_x₁ : ¬ G.Adj f x₁ := fun hadj => hff' (hx₁uniq f hfD hadj.symm)
  have hR1 : IsPathFrom Gᶜ (f :: Q) f x₁' := by
    refine PathAttach.isPathFrom_cons hQ' ⟨?_, hnadj_f_x₁⟩ hfnQ ?_
    · exact fun h => hDsub hfD (Or.inl (Or.inl (by rw [h]; exact hx₁A)))
    · intro z hz hzx₁ hadj
      exact hadj.2 (hfA1.1 z ⟨hQA z hz, hzx₁⟩)
  have hxbnQ : xb ∉ (f :: Q) := by
    intro hz
    rcases List.mem_cons.mp hz with h | h
    · exact hDsub hfD (Or.inl (Or.inr (by rw [← h]; exact hxbB)))
    · exact Set.disjoint_left.mp d12 (hQA xb h) hxbB
  have hR : IsPathFrom Gᶜ (xb :: (f :: Q)) xb x₁' := by
    refine PathAttach.isPathFrom_cons hR1 ⟨?_, fun hadj => hxbf hadj.symm⟩ hxbnQ ?_
    · exact fun h => hDsub hfD (Or.inl (Or.inr (by rw [← h]; exact hxbB)))
    · intro z hz hzf hadj
      rcases List.mem_cons.mp hz with h | h
      · exact hzf h
      · exact hadj.2 (c12 z (hQA z h) xb hxbB).symm
  -- "and so `Q` has length 1, and hence `x₁, x₁'` are nonadjacent"
  have hQlen1 : pathLength Q = 1 := by
    have hpl : pathLength Q = Q.length - 1 := PathBasics.pathLength_eq Q
    have h2 : 2 ≤ Q.length := two_le_length_of_ends_ne hQ' hx₁ne
    by_contra hne
    have hRlen : 5 ≤ (xb :: (f :: Q)).length := by
      simp only [List.length_cons]
      omega
    exact (SPGT.thm_24_6 G hG hbsp).2 (exists_antipath_length_four hR.1 hRlen)
  have hnadj_x₁x₁' : ¬ G.Adj x₁ x₁' :=
    (PathBasics.isPathFrom_ends_adj_of_length_one hQ' hQlen1).2
  -- "From the minimality of `F`, there exists `x₂ ∈ X₂` with no neighbour in `F \ {f}`."
  obtain ⟨x₂, hx₂B, hx₂no⟩ : ∃ x ∈ B, ∀ g ∈ D, g ≠ f → ¬ G.Adj x g := by
    by_contra hcon
    push Not at hcon
    refine shrink_F hHfull hNo hmin hDfsub hfD hfnin
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hPtail)
      (Or.inr (Or.inr ⟨?_, ?_⟩))
    · intro y hy
      obtain ⟨g, hgD, hgf, hadj⟩ := hcon y hy
      exact ⟨g, hinDf g hgD hgf, hadj⟩
    · exact fun y hy => ⟨f', hf'in, (hf'A1.2 y hy).symm⟩
  obtain ⟨x₃, hx₃C⟩ := n3
  have hx₁x₂ : G.Adj x₁ x₂ := c12 x₁ hx₁A x₂ hx₂B
  have hx₁'x₂ : G.Adj x₁' x₂ := c12 x₁' hx₁'A x₂ hx₂B
  by_cases hadjx₂f : G.Adj x₂ f
  · -- the branch `x₂` **is** adjacent to `f`: the hole `x₂-f-P-f'-x₁-x₂` with `x₁'` outside it
    have hx₁nP : x₁ ∉ P := fun hz =>
      hDsub (by rw [hDeq]; exact hz) (Or.inl (Or.inl hx₁A))
    have houter : IsPathFrom G (P ++ [x₁]) f x₁ := by
      refine PathAttach.isPathFrom_concat hP hx₁f' hx₁nP ?_
      intro z hz hzf' hadj
      exact hzf' (hx₁uniq z (by rw [hDeq]; exact hz) hadj)
    have houterlen : 2 ≤ pathLength (P ++ [x₁]) := by
      rw [PathBasics.pathLength_eq]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hx₂nout : x₂ ∉ (P ++ [x₁]) := by
      intro hz
      rcases List.mem_append.mp hz with h | h
      · exact hDsub (by rw [hDeq]; exact h) (Or.inl (Or.inr hx₂B))
      · exact Set.disjoint_left.mp d12
          (by rw [List.mem_singleton.mp h]; exact hx₁A) hx₂B
    have hwint2 : ∀ z ∈ SPGT.interior (P ++ [x₁]), ¬ G.Adj x₂ z := by
      intro z hz hadj
      rw [PathBasics.mem_interior_iff_of_pathFrom houter] at hz
      obtain ⟨hzmem, hzf, hzx₁⟩ := hz
      rcases List.mem_append.mp hzmem with h | h
      · exact hx₂no z (by rw [hDeq]; exact h) hzf hadj
      · exact hzx₁ (List.mem_singleton.mp h)
    have hhole2 : IsHoleList G (x₂ :: (P ++ [x₁])) :=
      PrismBasics.isHoleList_of_path_add_vertex houter houterlen hadjx₂f hx₁x₂.symm
        hx₂nout hwint2
    have hx₁'nin : x₁' ∉ (x₂ :: (P ++ [x₁])) := by
      intro hz
      rcases List.mem_cons.mp hz with h | h
      · exact Set.disjoint_left.mp d12 hx₁'A (by rw [h]; exact hx₂B)
      rcases List.mem_append.mp h with h2 | h2
      · exact hDsub (by rw [hDeq]; exact h2) (Or.inl (Or.inl hx₁'A))
      · exact hx₁ne (List.mem_singleton.mp h2).symm
    have hkey2 := (SPGT.thm_24_6 G hG hbsp).1 (x₂ :: (P ++ [x₁])) hhole2 x₁' f x₂ hx₁'nin
      (List.mem_cons_of_mem _ (List.mem_append_left _ hfP)) (List.mem_cons_self)
      hx₁'f hx₁'x₂ hadjx₂f.symm
    obtain ⟨c₀, hc₀mem, hc₀f, hc₀x₂, hc₀adj⟩ := hkey2.2
    rcases List.mem_cons.mp hc₀mem with h | h
    · exact hc₀x₂ h
    rcases List.mem_append.mp h with h2 | h2
    · exact hc₀f (hx₁'uniq c₀ (by rw [hDeq]; exact h2) hc₀adj)
    · have hc : c₀ = x₁ := List.mem_singleton.mp h2
      exact hnadj_x₁x₁' (by rw [← hc]; exact hc₀adj.symm)
  · -- the branch `x₂` is also nonadjacent to `f`: the hole `x₂-x₁-f'-P-f-x₁'-x₂`
    have hx₂noD : ∀ g ∈ D, ¬ G.Adj x₂ g := by
      intro g hgD hadj
      by_cases hgf : g = f
      · exact hadjx₂f (by rw [← hgf]; exact hadj)
      · exact hx₂no g hgD hgf hadj
    have hPrev : IsPathFrom G P.reverse f' f := PathBasics.isPathFrom_reverse hP
    have hx₁nP : x₁ ∉ P.reverse := fun hz =>
      hDsub (by rw [hDeq]; exact List.mem_reverse.mp hz) (Or.inl (Or.inl hx₁A))
    have hx₁'nP : x₁' ∉ P.reverse := fun hz =>
      hDsub (by rw [hDeq]; exact List.mem_reverse.mp hz) (Or.inl (Or.inl hx₁'A))
    have hinner : IsPathFrom G (x₁ :: (P.reverse ++ [x₁'])) x₁ x₁' := by
      refine PathAttach.isPathFrom_cons_concat hPrev hx₁f' hx₁'f hnadj_x₁x₁' hx₁ne
        hx₁nP hx₁'nP ?_ ?_
      · intro z hz hzf' hadj
        exact hzf' (hx₁uniq z (by rw [hDeq]; exact List.mem_reverse.mp hz) hadj)
      · intro z hz hzf hadj
        exact hzf (hx₁'uniq z (by rw [hDeq]; exact List.mem_reverse.mp hz) hadj)
    have hinnerlen : 2 ≤ pathLength (x₁ :: (P.reverse ++ [x₁'])) := by
      rw [PathAttach.pathLength_cons_append_singleton, List.length_reverse]
      omega
    have hx₂nin : x₂ ∉ (x₁ :: (P.reverse ++ [x₁'])) := by
      intro hz
      rcases PathAttach.mem_cons_append_singleton.mp hz with h | h | h
      · exact Set.disjoint_left.mp d12 (by rw [h]; exact hx₁A) hx₂B
      · exact hDsub (by rw [hDeq]; exact List.mem_reverse.mp h) (Or.inl (Or.inr hx₂B))
      · exact Set.disjoint_left.mp d12 (by rw [h]; exact hx₁'A) hx₂B
    have hwint : ∀ z ∈ SPGT.interior (x₁ :: (P.reverse ++ [x₁'])), ¬ G.Adj x₂ z := by
      intro z hz hadj
      rw [PathBasics.mem_interior_iff_of_pathFrom hinner] at hz
      obtain ⟨hzmem, hz1, hz2⟩ := hz
      rcases PathAttach.mem_cons_append_singleton.mp hzmem with h | h | h
      · exact hz1 h
      · exact hx₂noD z (by rw [hDeq]; exact List.mem_reverse.mp h) hadj
      · exact hz2 h
    have hhole : IsHoleList G (x₂ :: (x₁ :: (P.reverse ++ [x₁']))) :=
      PrismBasics.isHoleList_of_path_add_vertex hinner hinnerlen hx₁x₂.symm hx₁'x₂.symm
        hx₂nin hwint
    have hx₃nin : x₃ ∉ (x₂ :: (x₁ :: (P.reverse ++ [x₁']))) := by
      intro hz
      rcases List.mem_cons.mp hz with h | h1
      · exact Set.disjoint_left.mp d23 hx₂B (by rw [← h]; exact hx₃C)
      rcases PathAttach.mem_cons_append_singleton.mp h1 with h | h | h
      · exact Set.disjoint_left.mp d13 hx₁A (by rw [← h]; exact hx₃C)
      · exact hDsub (by rw [hDeq]; exact List.mem_reverse.mp h) (Or.inr hx₃C)
      · exact Set.disjoint_left.mp d13 hx₁'A (by rw [← h]; exact hx₃C)
    have hkey := (SPGT.thm_24_6 G hG hbsp).1 (x₂ :: (x₁ :: (P.reverse ++ [x₁']))) hhole
      x₃ x₁ x₂ hx₃nin (by simp) (List.mem_cons_self)
      (c13 x₁ hx₁A x₃ hx₃C).symm (c23 x₂ hx₂B x₃ hx₃C).symm hx₁x₂
    have hlen4 := hkey.1
    rw [PrismBasics.holeLength_cons x₂ (List.cons_ne_nil _ _),
      PathAttach.pathLength_cons_append_singleton, List.length_reverse] at hlen4
    omega

/-- *"So there is at most one `i` such that `F` contains `Xᵢ`-complete vertices, and from the
symmetry we may assume that `F` contains no `X₁`- or `X₂`-complete vertices.  We may also assume
that all members of `X₁` have neighbours in `F`."* -/
private theorem case_B_dispatch {G : SimpleGraph V} (hG : InF11 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    {A B C D : Set V} (hH : Hyp G A B C D) (hNo : ¬ Concl G A B C D)
    (hmin : ∀ Z₁ Z₂ Z₃ E : Set V, Hyp G Z₁ Z₂ Z₃ E → ¬ Concl G Z₁ Z₂ Z₃ E →
        (A ∪ B ∪ C ∪ D).ncard ≤ (Z₁ ∪ Z₂ ∪ Z₃ ∪ E).ncard)
    (hnoA : ¬ ∃ f ∈ D, VertexComplete G f A)
    (hnoB : ¬ ∃ f ∈ D, VertexComplete G f B) :
    False := by
  have htwo := hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hor : Nbrs G A D ∨ Nbrs G B D := by
    rcases htwo with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
    · exact Or.inl h1
    · exact Or.inl h1
    · exact Or.inr h2
  rcases hor with h | h
  · exact case_B hG hbsp hH hNo hmin hnoA hnoB h
  · refine case_B hG hbsp (hyp_swap12 hH) (fun hc => hNo (concl_swap12 hc)) ?_ hnoB hnoA h
    intro Z₁ Z₂ Z₃ E hz1 hz2
    rw [union4_swap12]
    exact hmin Z₁ Z₂ Z₃ E hz1 hz2

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_24_7 (G : SimpleGraph V) (hG : InF11 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (X₁ X₂ X₃ : Set V)
    (hd₁₂ : Disjoint X₁ X₂) (hd₁₃ : Disjoint X₁ X₃) (hd₂₃ : Disjoint X₂ X₃)
    (hne₁ : X₁.Nonempty) (hne₂ : X₂.Nonempty) (hne₃ : X₃.Nonempty)
    (ha₁ : AnticonnectedSet G X₁) (ha₂ : AnticonnectedSet G X₂)
    (ha₃ : AnticonnectedSet G X₃)
    (hc₁₂ : Complete G X₁ X₂) (hc₁₃ : Complete G X₁ X₃) (hc₂₃ : Complete G X₂ X₃)
    (F : Set V) (hF : F ⊆ (X₁ ∪ X₂ ∪ X₃)ᶜ) (hFconn : ConnectedSet G F)
    (htwo :
      ((∀ x ∈ X₁, ∃ f ∈ F, G.Adj x f) ∧ (∀ x ∈ X₂, ∃ f ∈ F, G.Adj x f)) ∨
      ((∀ x ∈ X₁, ∃ f ∈ F, G.Adj x f) ∧ (∀ x ∈ X₃, ∃ f ∈ F, G.Adj x f)) ∨
      ((∀ x ∈ X₂, ∃ f ∈ F, G.Adj x f) ∧ (∀ x ∈ X₃, ∃ f ∈ F, G.Adj x f))) :
    ∃ f ∈ F,
      (VertexComplete G f X₁ ∧ VertexComplete G f X₂) ∨
      (VertexComplete G f X₁ ∧ VertexComplete G f X₃) ∨
      (VertexComplete G f X₂ ∧ VertexComplete G f X₃) := by
  by_contra hcon
  have hyp0 : Hyp G X₁ X₂ X₃ F :=
    ⟨hd₁₂, hd₁₃, hd₂₃, hne₁, hne₂, hne₃, ha₁, ha₂, ha₃, hc₁₂, hc₁₃, hc₂₃, hF, hFconn, htwo⟩
  -- "choose a counterexample with `X₁ ∪ X₂ ∪ X₃ ∪ F` minimal"
  obtain ⟨⟨Y₁, Y₂, Y₃, E⟩, ⟨hH, hNo⟩, hminraw⟩ :=
    ExtremalChoice.exists_min_nat
      (fun t : Set V × Set V × Set V × Set V =>
        Hyp G t.1 t.2.1 t.2.2.1 t.2.2.2 ∧ ¬ Concl G t.1 t.2.1 t.2.2.1 t.2.2.2)
      (fun t : Set V × Set V × Set V × Set V => (t.1 ∪ t.2.1 ∪ t.2.2.1 ∪ t.2.2.2).ncard)
      ⟨(X₁, X₂, X₃, F), hyp0, hcon⟩
  have hH : Hyp G Y₁ Y₂ Y₃ E := hH
  have hNo : ¬ Concl G Y₁ Y₂ Y₃ E := hNo
  have hmin : ∀ Z₁ Z₂ Z₃ D : Set V, Hyp G Z₁ Z₂ Z₃ D → ¬ Concl G Z₁ Z₂ Z₃ D →
      (Y₁ ∪ Y₂ ∪ Y₃ ∪ E).ncard ≤ (Z₁ ∪ Z₂ ∪ Z₃ ∪ D).ncard := by
    intro Z₁ Z₂ Z₃ D h1 h2
    exact hminraw (Z₁, Z₂, Z₃, D) ⟨h1, h2⟩
  -- "Suppose `F` contains an `Xᵢ`-complete vertex for two values of `i`"
  by_cases hcy1 : ∃ f ∈ E, VertexComplete G f Y₁
  · by_cases hcy2 : ∃ f ∈ E, VertexComplete G f Y₂
    · exact case_A hG hbsp hH hNo hmin hcy1 hcy2
    · by_cases hcy3 : ∃ f ∈ E, VertexComplete G f Y₃
      · refine case_A hG hbsp (hyp_swap23 hH) (fun hc => hNo (concl_swap23 hc)) ?_ hcy1 hcy3
        intro Z₁ Z₂ Z₃ D hz1 hz2
        rw [union4_swap23]
        exact hmin Z₁ Z₂ Z₃ D hz1 hz2
      · -- `Y₂` and `Y₃` carry no complete vertex: put them in positions 1, 2
        refine case_B_dispatch hG hbsp (hyp_swap23 (hyp_swap12 hH))
          (fun hc => hNo (concl_swap12 (concl_swap23 hc))) ?_ hcy2 hcy3
        intro Z₁ Z₂ Z₃ D hz1 hz2
        rw [union4_swap23, union4_swap12]
        exact hmin Z₁ Z₂ Z₃ D hz1 hz2
  · by_cases hcy2 : ∃ f ∈ E, VertexComplete G f Y₂
    · by_cases hcy3 : ∃ f ∈ E, VertexComplete G f Y₃
      · -- complete vertices for `Y₂` and `Y₃`: put them in positions 1, 2
        refine case_A hG hbsp (hyp_swap23 (hyp_swap12 hH))
          (fun hc => hNo (concl_swap12 (concl_swap23 hc))) ?_ hcy2 hcy3
        intro Z₁ Z₂ Z₃ D hz1 hz2
        rw [union4_swap23, union4_swap12]
        exact hmin Z₁ Z₂ Z₃ D hz1 hz2
      · -- `Y₁` and `Y₃` carry no complete vertex: put them in positions 1, 2
        refine case_B_dispatch hG hbsp (hyp_swap23 hH)
          (fun hc => hNo (concl_swap23 hc)) ?_ hcy1 hcy3
        intro Z₁ Z₂ Z₃ D hz1 hz2
        rw [union4_swap23]
        exact hmin Z₁ Z₂ Z₃ D hz1 hz2
    · exact case_B_dispatch hG hbsp hH hNo hmin hcy1 hcy2

end SPGT

end Workspace.Statements.S24
