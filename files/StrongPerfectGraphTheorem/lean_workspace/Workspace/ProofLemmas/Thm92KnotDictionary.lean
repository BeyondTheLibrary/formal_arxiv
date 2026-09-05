import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.Thm92Intrinsic
import Workspace.ProofLemmas.Thm92Branches
import Workspace.ProofLemmas.KnotLabels
import Workspace.ProofLemmas.PathBasics

/-!
# The knot-side dictionary for 9.2

When the two antipaths of a knot have length one, the four triples at its corners are exactly
the triangles of the induced graph.  Removing the triangle edges leaves the two path branches
and the four one-vertex branches.  The two lemmas below state the resulting translations of
locality and resolution.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace Workspace.ProofLemmas.Thm92KnotDictionary

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm92Intrinsic

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem path_no_triangle {F : SimpleGraph V} {p : List V}
    (hp : IsPathList F p) {a b c : V} (ha : a ∈ p) (hb : b ∈ p) (hc : c ∈ p)
    (hab : F.Adj a b) (hbc : F.Adj b c) (hca : F.Adj c a) : False := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
  have h1 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hi hj).mp hab
  have h2 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hj hk).mp hbc
  have h3 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hk hi).mp hca
  omega

/-- PAPER (proof of 9.2, printed p. 48): *"The proof is obvious and we omit it."*

The finite structural fact needed for the resolving half: the only triangles in a knot whose
two antipaths have length one are its four corner triangles. -/
lemma knot_triangle_is_corner (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hQ₁len : pathLength Q₁ = 1) (hQ₂len : pathLength Q₂ = 1)
    {u v w : ↥K} (huv : (G.induce K).Adj u v) (hvw : (G.induce K).Adj v w)
    (hwu : (G.induce K).Adj w u) :
    ({(u : V), (v : V), (w : V)} : Set V) = {x₁, x₂, a₁} ∨
    ({(u : V), (v : V), (w : V)} : Set V) = {x₁, y₂, a₂} ∨
    ({(u : V), (v : V), (w : V)} : Set V) = {y₁, y₂, b₁} ∨
    ({(u : V), (v : V), (w : V)} : Set V) = {y₁, x₂, b₂} := by
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq12, hlen1, hlen2, -, -, hanti, hcomp,
    hE11, hE12, hE21, hE22, -⟩ :=
    Workspace.ProofLemmas.KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have hQ₁eq : Q₁ = [x₁, y₁] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hQ₁ hQ₁len
  have hQ₂eq : Q₂ = [x₂, y₂] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hQ₂ hQ₂len
  have ha₁ : a₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).1
  have hb₁ : b₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).2
  have ha₂ : a₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).1
  have hb₂ : b₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).2
  have hx₁ : x₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hy₁ : y₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hx₂ : x₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have hy₂ : y₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have ha₁b₁ : a₁ ≠ b₁ := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hP₁ hlen1
  have ha₂b₂ : a₂ ≠ b₂ := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hP₂ hlen2
  have hx₁y₁ : x₁ ≠ y₁ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hQ₁.1
    rw [hQ₁eq] at hn; simpa using hn
  have hx₂y₂ : x₂ ≠ y₂ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hQ₂.1
    rw [hQ₂eq] at hn; simpa using hn
  have hnQ₁ : ¬ G.Adj x₁ y₁ := by
    have hQ₁' : IsAntipathFrom G [x₁, y₁] x₁ y₁ := by simpa [hQ₁eq] using hQ₁
    exact ((hQ₁'.1.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)).2
  have hnQ₂ : ¬ G.Adj x₂ y₂ := by
    have hQ₂' : IsAntipathFrom G [x₂, y₂] x₂ y₂ := by simpa [hQ₂eq] using hQ₂
    exact ((hQ₂'.1.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)).2
  have hnQ₁' : ¬ G.Adj y₁ x₁ := fun h => hnQ₁ h.symm
  have hnQ₂' : ¬ G.Adj y₂ x₂ := fun h => hnQ₂ h.symm
  -- every vertex of `K` lies on a path or is one of the four antipath vertices
  have kind : ∀ t : V, t ∈ K → (t ∈ P₁ ∨ t ∈ P₂) ∨ (t = x₁ ∨ t = y₁ ∨ t = x₂ ∨ t = y₂) := by
    intro t ht
    rw [hK] at ht
    simp only [Set.mem_union, Set.mem_setOf_eq] at ht
    rcases ht with ((h | h) | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · rw [hQ₁eq] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      tauto
    · rw [hQ₂eq] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      tauto
  -- which end of a path an antipath vertex can be adjacent to
  have p1x : ∀ t ∈ P₁, ∀ q : V, (q = x₁ ∨ q = x₂) → G.Adj t q → t = a₁ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE11 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₁y₁
    · rcases (hE12 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₂y₂
  have p1y : ∀ t ∈ P₁, ∀ q : V, (q = y₁ ∨ q = y₂) → G.Adj t q → t = b₁ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE11 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₁y₁
      · exact h
    · rcases (hE12 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₂y₂
      · exact h
  have p2a : ∀ t ∈ P₂, ∀ q : V, (q = x₁ ∨ q = y₂) → G.Adj t q → t = a₂ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE21 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₁y₁
    · rcases (hE22 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₂y₂.symm
  have p2b : ∀ t ∈ P₂, ∀ q : V, (q = y₁ ∨ q = x₂) → G.Adj t q → t = b₂ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE21 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₁y₁
      · exact h
    · rcases (hE22 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h hx₂y₂
      · exact h
  -- no two vertices of the same path lie in a common triangle of `K`
  have noTwoP1 : ∀ s t c : V, s ∈ P₁ → t ∈ P₁ → c ∈ K →
      G.Adj s t → G.Adj s c → G.Adj t c → False := by
    intro s t c hs ht hc hst hsc htc
    rcases kind c hc with (h | h) | (rfl | rfl | rfl | rfl)
    · exact path_no_triangle hP₁.1 hs ht h hst htc hsc.symm
    · exact hanti s hs c h hsc
    · exact hst.ne ((p1x s hs _ (Or.inl rfl) hsc).trans (p1x t ht _ (Or.inl rfl) htc).symm)
    · exact hst.ne ((p1y s hs _ (Or.inl rfl) hsc).trans (p1y t ht _ (Or.inl rfl) htc).symm)
    · exact hst.ne ((p1x s hs _ (Or.inr rfl) hsc).trans (p1x t ht _ (Or.inr rfl) htc).symm)
    · exact hst.ne ((p1y s hs _ (Or.inr rfl) hsc).trans (p1y t ht _ (Or.inr rfl) htc).symm)
  have noTwoP2 : ∀ s t c : V, s ∈ P₂ → t ∈ P₂ → c ∈ K →
      G.Adj s t → G.Adj s c → G.Adj t c → False := by
    intro s t c hs ht hc hst hsc htc
    rcases kind c hc with (h | h) | (rfl | rfl | rfl | rfl)
    · exact hanti c h s hs hsc.symm
    · exact path_no_triangle hP₂.1 hs ht h hst htc hsc.symm
    · exact hst.ne ((p2a s hs _ (Or.inl rfl) hsc).trans (p2a t ht _ (Or.inl rfl) htc).symm)
    · exact hst.ne ((p2b s hs _ (Or.inl rfl) hsc).trans (p2b t ht _ (Or.inl rfl) htc).symm)
    · exact hst.ne ((p2b s hs _ (Or.inr rfl) hsc).trans (p2b t ht _ (Or.inr rfl) htc).symm)
    · exact hst.ne ((p2a s hs _ (Or.inr rfl) hsc).trans (p2a t ht _ (Or.inr rfl) htc).symm)
  have pairwise : ∀ s t c : V, (s ∈ P₁ ∨ s ∈ P₂) → (t ∈ P₁ ∨ t ∈ P₂) → c ∈ K →
      G.Adj s t → G.Adj s c → G.Adj t c → False := by
    rintro s t c (hs | hs) (ht | ht) hc hst hsc htc
    · exact noTwoP1 s t c hs ht hc hst hsc htc
    · exact hanti s hs t ht hst
    · exact hanti t ht s hs hst.symm
    · exact noTwoP2 s t c hs ht hc hst hsc htc
  -- the four antipath vertices contain no triangle
  have qnotri : ∀ s t r : V, (s = x₁ ∨ s = y₁ ∨ s = x₂ ∨ s = y₂) →
      (t = x₁ ∨ t = y₁ ∨ t = x₂ ∨ t = y₂) → (r = x₁ ∨ r = y₁ ∨ r = x₂ ∨ r = y₂) →
      G.Adj s t → G.Adj t r → G.Adj r s → False := by
    rintro s t r (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
      hst htr hrs
    all_goals first
      | exact hst.ne rfl | exact htr.ne rfl | exact hrs.ne rfl
      | exact hnQ₁ hst | exact hnQ₁ htr | exact hnQ₁ hrs
      | exact hnQ₁' hst | exact hnQ₁' htr | exact hnQ₁' hrs
      | exact hnQ₂ hst | exact hnQ₂ htr | exact hnQ₂ hrs
      | exact hnQ₂' hst | exact hnQ₂' htr | exact hnQ₂' hrs
  -- a triangle with one path vertex and two antipath vertices is a corner
  have key : ∀ t q r : V, (t ∈ P₁ ∨ t ∈ P₂) →
      (q = x₁ ∨ q = y₁ ∨ q = x₂ ∨ q = y₂) → (r = x₁ ∨ r = y₁ ∨ r = x₂ ∨ r = y₂) →
      G.Adj t q → G.Adj t r → G.Adj q r →
      ({t, q, r} : Set V) = {x₁, x₂, a₁} ∨ ({t, q, r} : Set V) = {x₁, y₂, a₂} ∨
      ({t, q, r} : Set V) = {y₁, y₂, b₁} ∨ ({t, q, r} : Set V) = {y₁, x₂, b₂} := by
    rintro t q r ht (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) htq htr hqr
    -- q = x₁
    · exact absurd rfl hqr.ne
    · exact absurd hqr hnQ₁
    · rcases ht with h | h
      · have h1 : t = a₁ := p1x t h _ (Or.inl rfl) htq
        subst h1
        exact Or.inl (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
      · have h1 : t = a₂ := p2a t h _ (Or.inl rfl) htq
        have h2 : t = b₂ := p2b t h _ (Or.inr rfl) htr
        exact absurd (h1.symm.trans h2) ha₂b₂
    · rcases ht with h | h
      · have h1 : t = a₁ := p1x t h _ (Or.inl rfl) htq
        have h2 : t = b₁ := p1y t h _ (Or.inr rfl) htr
        exact absurd (h1.symm.trans h2) ha₁b₁
      · have h1 : t = a₂ := p2a t h _ (Or.inl rfl) htq
        subst h1
        exact Or.inr (Or.inl
          (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto))
    -- q = y₁
    · exact absurd hqr hnQ₁'
    · exact absurd rfl hqr.ne
    · rcases ht with h | h
      · have h1 : t = b₁ := p1y t h _ (Or.inl rfl) htq
        have h2 : t = a₁ := p1x t h _ (Or.inr rfl) htr
        exact absurd (h2.symm.trans h1) ha₁b₁
      · have h1 : t = b₂ := p2b t h _ (Or.inl rfl) htq
        subst h1
        exact Or.inr (Or.inr (Or.inr
          (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)))
    · rcases ht with h | h
      · have h1 : t = b₁ := p1y t h _ (Or.inl rfl) htq
        subst h1
        exact Or.inr (Or.inr (Or.inl
          (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)))
      · have h1 : t = b₂ := p2b t h _ (Or.inl rfl) htq
        have h2 : t = a₂ := p2a t h _ (Or.inr rfl) htr
        exact absurd (h2.symm.trans h1) ha₂b₂
    -- q = x₂
    · rcases ht with h | h
      · have h1 : t = a₁ := p1x t h _ (Or.inr rfl) htq
        subst h1
        exact Or.inl (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
      · have h1 : t = b₂ := p2b t h _ (Or.inr rfl) htq
        have h2 : t = a₂ := p2a t h _ (Or.inl rfl) htr
        exact absurd (h2.symm.trans h1) ha₂b₂
    · rcases ht with h | h
      · have h1 : t = a₁ := p1x t h _ (Or.inr rfl) htq
        have h2 : t = b₁ := p1y t h _ (Or.inl rfl) htr
        exact absurd (h1.symm.trans h2) ha₁b₁
      · have h1 : t = b₂ := p2b t h _ (Or.inr rfl) htq
        subst h1
        exact Or.inr (Or.inr (Or.inr
          (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)))
    · exact absurd rfl hqr.ne
    · exact absurd hqr hnQ₂
    -- q = y₂
    · rcases ht with h | h
      · have h1 : t = b₁ := p1y t h _ (Or.inr rfl) htq
        have h2 : t = a₁ := p1x t h _ (Or.inl rfl) htr
        exact absurd (h2.symm.trans h1) ha₁b₁
      · have h1 : t = a₂ := p2a t h _ (Or.inr rfl) htq
        subst h1
        exact Or.inr (Or.inl
          (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto))
    · rcases ht with h | h
      · have h1 : t = b₁ := p1y t h _ (Or.inr rfl) htq
        subst h1
        exact Or.inr (Or.inr (Or.inl
          (by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)))
      · have h1 : t = a₂ := p2a t h _ (Or.inr rfl) htq
        have h2 : t = b₂ := p2b t h _ (Or.inl rfl) htr
        exact absurd (h1.symm.trans h2) ha₂b₂
    · exact absurd hqr hnQ₂'
    · exact absurd rfl hqr.ne
  -- assemble: exactly one vertex of the triangle lies on a path
  have hUZ : G.Adj (u : V) (v : V) := huv
  have hZW : G.Adj (v : V) (w : V) := hvw
  have hWU : G.Adj (w : V) (u : V) := hwu
  rcases kind (u : V) u.2 with cU | cU <;> rcases kind (v : V) v.2 with cZ | cZ <;>
    rcases kind (w : V) w.2 with cW | cW
  · exact (pairwise _ _ _ cU cZ w.2 hUZ hWU.symm hZW).elim
  · exact (pairwise _ _ _ cU cZ w.2 hUZ hWU.symm hZW).elim
  · exact (pairwise _ _ _ cU cW v.2 hWU.symm hUZ hZW.symm).elim
  · exact key _ _ _ cU cZ cW hUZ hWU.symm hZW
  · exact (pairwise _ _ _ cZ cW u.2 hZW hUZ.symm hWU).elim
  · have hset : ({(u : V), (v : V), (w : V)} : Set V) = {(v : V), (u : V), (w : V)} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact key _ _ _ cZ cU cW hUZ.symm hZW hWU.symm
  · have hset : ({(u : V), (v : V), (w : V)} : Set V) = {(w : V), (u : V), (v : V)} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact key _ _ _ cW cU cZ hWU hZW.symm hUZ
  · exact (qnotri _ _ _ cU cZ cW hUZ hZW hWU).elim

/-- PAPER (proof of 9.2, printed p. 48): *"The proof is obvious and we omit it."*

This is the local part of the omitted knot dictionary: the sets local for a knot with
length-one antipaths are exactly the sets contained in a corner triangle or in one of the six
branches of its line-graph presentation. -/
lemma localForKnot_iff_intrinsic (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hQ₁ : pathLength Q₁ = 1) (hQ₂ : pathLength Q₂ = 1)
    (X : Set V) (hX : X ⊆ K) :
    LocalForKnot G P₁ P₂ Q₁ Q₂ X ↔
      IntrinsicLocal (G.induce K) {v : ↥K | (v : V) ∈ X} := by
  have hknot' := hknot
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hP₁, hP₂, hA₁, hA₂, -⟩ := hknot'
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq12, hlen1, hlen2, -, -, hanti, hcomp,
    hE11, hE12, hE21, hE22, -⟩ :=
    Workspace.ProofLemmas.KnotLabels.knot_labels hknot hP₁ hP₂ hA₁ hA₂
  obtain ⟨reach1, reach2, flatmem⟩ :=
    Workspace.ProofLemmas.Thm92Branches.branch_dictionary G P₁ P₂ Q₁ Q₂
      a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hA₁ hA₂ K hK hQ₁ hQ₂
  have hQ₁eq : Q₁ = [x₁, y₁] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hA₁ hQ₁
  have hQ₂eq : Q₂ = [x₂, y₂] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hA₂ hQ₂
  have ha₁ : a₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).1
  have hb₁ : b₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).2
  have ha₂ : a₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).1
  have hb₂ : b₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).2
  have hmx₁ : x₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hmy₁ : y₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hmx₂ : x₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have hmy₂ : y₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have ha₁b₁ : a₁ ≠ b₁ := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hP₁ hlen1
  have ha₂b₂ : a₂ ≠ b₂ := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hP₂ hlen2
  have hx₁y₁ : x₁ ≠ y₁ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hA₁.1
    rw [hQ₁eq] at hn; simpa using hn
  have hx₂y₂ : x₂ ≠ y₂ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hA₂.1
    rw [hQ₂eq] at hn; simpa using hn
  have ex₁x₂ : G.Adj x₁ x₂ := hcomp x₁ hmx₁ x₂ hmx₂
  have ex₁y₂ : G.Adj x₁ y₂ := hcomp x₁ hmx₁ y₂ hmy₂
  have ey₁x₂ : G.Adj y₁ x₂ := hcomp y₁ hmy₁ x₂ hmx₂
  have ey₁y₂ : G.Adj y₁ y₂ := hcomp y₁ hmy₁ y₂ hmy₂
  have ea₁x₁ : G.Adj a₁ x₁ := (hE11 a₁ ha₁ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₁x₂ : G.Adj a₁ x₂ := (hE12 a₁ ha₁ x₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₁y₁ : G.Adj b₁ y₁ := (hE11 b₁ hb₁ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₁y₂ : G.Adj b₁ y₂ := (hE12 b₁ hb₁ y₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have ea₂x₁ : G.Adj a₂ x₁ := (hE21 a₂ ha₂ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₂y₂ : G.Adj a₂ y₂ := (hE22 a₂ ha₂ y₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₂y₁ : G.Adj b₂ y₁ := (hE21 b₂ hb₂ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₂x₂ : G.Adj b₂ x₂ := (hE22 b₂ hb₂ x₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have memK : ∀ z : V, z ∈ P₁ ∨ z ∈ P₂ ∨ z ∈ Q₁ ∨ z ∈ Q₂ → z ∈ K := by
    intro z hz
    rw [hK]; simp only [Set.mem_union, Set.mem_setOf_eq]; tauto
  have ka₁ := memK a₁ (Or.inl ha₁)
  have kb₁ := memK b₁ (Or.inl hb₁)
  have ka₂ := memK a₂ (Or.inr (Or.inl ha₂))
  have kb₂ := memK b₂ (Or.inr (Or.inl hb₂))
  have kx₁ := memK x₁ (Or.inr (Or.inr (Or.inl hmx₁)))
  have ky₁ := memK y₁ (Or.inr (Or.inr (Or.inl hmy₁)))
  have kx₂ := memK x₂ (Or.inr (Or.inr (Or.inr hmx₂)))
  have ky₂ := memK y₂ (Or.inr (Or.inr (Or.inr hmy₂)))
  have kQ : ∀ z : V, (z ∈ Q₁ ∨ z ∈ Q₂) ↔ (z = x₁ ∨ z = y₁ ∨ z = x₂ ∨ z = y₂) := by
    intro z
    rw [hQ₁eq, hQ₂eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have kind : ∀ t : V, t ∈ K → (t ∈ P₁ ∨ t ∈ P₂) ∨ (t = x₁ ∨ t = y₁ ∨ t = x₂ ∨ t = y₂) := by
    intro t ht
    rw [hK] at ht
    simp only [Set.mem_union, Set.mem_setOf_eq] at ht
    rcases ht with ((h | h) | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ((kQ t).1 (Or.inl h))
    · exact Or.inr ((kQ t).1 (Or.inr h))
  have notP1 : ∀ z : V, (z = x₁ ∨ z = y₁ ∨ z = x₂ ∨ z = y₂) → z ∉ P₁ := by
    rintro z (rfl | rfl | rfl | rfl) hz
    · exact d1q1 z hz hmx₁
    · exact d1q1 z hz hmy₁
    · exact d1q2 z hz hmx₂
    · exact d1q2 z hz hmy₂
  have notP2 : ∀ z : V, (z = x₁ ∨ z = y₁ ∨ z = x₂ ∨ z = y₂) → z ∉ P₂ := by
    rintro z (rfl | rfl | rfl | rfl) hz
    · exact d2q1 z hz hmx₁
    · exact d2q1 z hz hmy₁
    · exact d2q2 z hz hmx₂
    · exact d2q2 z hz hmy₂
  have notQ : ∀ t : V, (t ∈ P₁ ∨ t ∈ P₂) → ¬ (t = x₁ ∨ t = y₁ ∨ t = x₂ ∨ t = y₂) := by
    rintro t (h | h) hq
    · exact notP1 t hq h
    · exact notP2 t hq h
  have p1x : ∀ t ∈ P₁, ∀ q : V, (q = x₁ ∨ q = x₂) → G.Adj t q → t = a₁ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE11 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₁y₁
    · rcases (hE12 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₂y₂
  have p1y : ∀ t ∈ P₁, ∀ q : V, (q = y₁ ∨ q = y₂) → G.Adj t q → t = b₁ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE11 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₁y₁
      · exact h
    · rcases (hE12 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₂y₂
      · exact h
  have p2a : ∀ t ∈ P₂, ∀ q : V, (q = x₁ ∨ q = y₂) → G.Adj t q → t = a₂ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE21 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₁y₁
    · rcases (hE22 t ht q (by simp)).1 hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₂y₂.symm
  have p2b : ∀ t ∈ P₂, ∀ q : V, (q = y₁ ∨ q = x₂) → G.Adj t q → t = b₂ := by
    rintro t ht q (rfl | rfl) hadj
    · rcases (hE21 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₁y₁
      · exact h
    · rcases (hE22 t ht q (by simp)).1 hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h hx₂y₂
      · exact h
  -- a set inside one path branch is local
  have pathLocal1 : X ⊆ {v : V | v ∈ P₁} → LocalForKnot G P₁ P₂ Q₁ Q₂ X := by
    intro hsub
    refine ⟨Or.inr (Set.disjoint_left.mpr (fun z hz hz2 => d12 z (hsub hz) hz2)), ?_, ?_, ?_⟩
    · exact fun hQ => notP1 x₁ (Or.inl rfl) (hsub (hQ hmx₁))
    · exact fun hQ => notP1 x₂ (Or.inr (Or.inr (Or.inl rfl))) (hsub (hQ hmx₂))
    · intro z hz z' hz'
      exact absurd (hsub hz'.1) (notP1 z' ((kQ z').1 hz'.2))
  have pathLocal2 : X ⊆ {v : V | v ∈ P₂} → LocalForKnot G P₁ P₂ Q₁ Q₂ X := by
    intro hsub
    refine ⟨Or.inl (Set.disjoint_left.mpr (fun z hz hz1 => d12 z hz1 (hsub hz))), ?_, ?_, ?_⟩
    · exact fun hQ => notP2 x₁ (Or.inl rfl) (hsub (hQ hmx₁))
    · exact fun hQ => notP2 x₂ (Or.inr (Or.inr (Or.inl rfl))) (hsub (hQ hmx₂))
    · intro z hz z' hz'
      exact absurd (hsub hz'.1) (notP2 z' ((kQ z').1 hz'.2))
  -- a set inside a one-vertex branch is local
  have singLocal : ∀ q : V, (q = x₁ ∨ q = y₁ ∨ q = x₂ ∨ q = y₂) →
      X ⊆ ({q} : Set V) → LocalForKnot G P₁ P₂ Q₁ Q₂ X := by
    intro q hq hsub
    refine ⟨Or.inl (Set.disjoint_left.mpr (fun z hz hz1 => notP1 q hq ((hsub hz) ▸ hz1))),
      ?_, ?_, ?_⟩
    · exact fun hQ => hx₁y₁ ((hsub (hQ hmx₁)).trans (hsub (hQ hmy₁)).symm)
    · exact fun hQ => hx₂y₂ ((hsub (hQ hmx₂)).trans (hsub (hQ hmy₂)).symm)
    · intro z hz z' hz'
      exact absurd hq (notQ q (by rw [← hsub hz.1]; exact hz.2))
  -- a set inside a corner triangle is local
  have cornerLocal : ∀ t q r : V, (t ∈ P₁ ∨ t ∈ P₂) →
      (q = x₁ ∨ q = y₁) → (r = x₂ ∨ r = y₂) →
      G.Adj t q → G.Adj t r → X ⊆ ({t, q, r} : Set V) →
      LocalForKnot G P₁ P₂ Q₁ Q₂ X := by
    intro t q r ht hq hr htq htr hsub
    have hqQ : q = x₁ ∨ q = y₁ ∨ q = x₂ ∨ q = y₂ :=
      hq.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
    have hrQ : r = x₁ ∨ r = y₁ ∨ r = x₂ ∨ r = y₂ :=
      hr.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr h)))
    have hone1 : ∀ z : V, z ∈ X → (z = x₁ ∨ z = y₁) → z = q := by
      intro z hzX hz
      rcases hsub hzX with h | h | h
      · exact absurd (hz.elim (fun h' => Or.inl h') (fun h' => Or.inr (Or.inl h')))
          (notQ z (by rw [h]; exact ht))
      · exact h
      · exfalso
        have hzQ1 : z ∈ Q₁ := by
          rcases hz with h' | h' <;> rw [h']
          · exact hmx₁
          · exact hmy₁
        have hzQ2 : z ∈ Q₂ := by
          rcases hr with h' | h' <;> rw [h, h']
          · exact hmx₂
          · exact hmy₂
        exact dq12 z hzQ1 hzQ2
    have hone2 : ∀ z : V, z ∈ X → (z = x₂ ∨ z = y₂) → z = r := by
      intro z hzX hz
      rcases hsub hzX with h | h | h
      · exact absurd
          (hz.elim (fun h' => Or.inr (Or.inr (Or.inl h')))
            (fun h' => Or.inr (Or.inr (Or.inr h'))))
          (notQ z (by rw [h]; exact ht))
      · exfalso
        have hzQ2 : z ∈ Q₂ := by
          rcases hz with h' | h' <;> rw [h']
          · exact hmx₂
          · exact hmy₂
        have hzQ1 : z ∈ Q₁ := by
          rcases hq with h' | h' <;> rw [h, h']
          · exact hmx₁
          · exact hmy₁
        exact dq12 z hzQ1 hzQ2
      · exact h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases ht with h | h
      · refine Or.inr (Set.disjoint_left.mpr ?_)
        intro z hz hzP2
        rcases hsub hz with hzt | hzt | hzt
        · exact d12 t h (hzt ▸ hzP2)
        · exact notP2 q hqQ (hzt ▸ hzP2)
        · exact notP2 r hrQ (hzt ▸ hzP2)
      · refine Or.inl (Set.disjoint_left.mpr ?_)
        intro z hz hzP1
        rcases hsub hz with hzt | hzt | hzt
        · exact d12 t (hzt ▸ hzP1) h
        · exact notP1 q hqQ (hzt ▸ hzP1)
        · exact notP1 r hrQ (hzt ▸ hzP1)
    · exact fun hQ =>
        hx₁y₁ ((hone1 x₁ (hQ hmx₁) (Or.inl rfl)).trans (hone1 y₁ (hQ hmy₁) (Or.inr rfl)).symm)
    · exact fun hQ =>
        hx₂y₂ ((hone2 x₂ (hQ hmx₂) (Or.inl rfl)).trans (hone2 y₂ (hQ hmy₂) (Or.inr rfl)).symm)
    · intro z hz z' hz'
      have hzt : z = t := by
        rcases hsub hz.1 with h | h | h
        · exact h
        · exact absurd hqQ (notQ q (by rw [← h]; exact hz.2))
        · exact absurd hrQ (notQ r (by rw [← h]; exact hz.2))
      have hz'qr : z' = q ∨ z' = r := by
        rcases hsub hz'.1 with h | h | h
        · exact absurd ((kQ z').1 hz'.2) (notQ z' (by rw [h]; exact ht))
        · exact Or.inl h
        · exact Or.inr h
      rcases hz'qr with h | h
      · rw [hzt, h]; exact htq
      · rw [hzt, h]; exact htr
  -- a set inside a corner triangle is intrinsically local
  have cornerIntrinsic : ∀ (t q r : V), t ∈ K → q ∈ K → r ∈ K →
      G.Adj t q → G.Adj q r → G.Adj r t → X ⊆ ({t, q, r} : Set V) →
      IntrinsicLocal (G.induce K) {v : ↥K | (v : V) ∈ X} := by
    intro t q r kt kq kr h1 h2 h3 hsub
    refine Or.inl ⟨⟨t, kt⟩, ⟨q, kq⟩, ⟨r, kr⟩, h1, h2, h3, ?_⟩
    intro z hz
    rcases hsub hz with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  constructor
  · rintro ⟨hdisj, hnQ1, hnQ2, hcompl⟩
    by_cases hXQ : ∃ z ∈ X, (z ∈ Q₁ ∨ z ∈ Q₂)
    · obtain ⟨q0, hq0X, hq0Q⟩ := hXQ
      have hq0Q' : q0 = x₁ ∨ q0 = y₁ ∨ q0 = x₂ ∨ q0 = y₂ := (kQ q0).1 hq0Q
      by_cases hXP : ∃ p ∈ X, (p ∈ P₁ ∨ p ∈ P₂)
      · obtain ⟨p0, hp0X, hp0P⟩ := hXP
        have hadj : G.Adj p0 q0 := hcompl p0 ⟨hp0X, hp0P⟩ q0 ⟨hq0X, hq0Q⟩
        rcases hp0P with hp | hp
        · have hXnP2 : ∀ z ∈ X, z ∉ P₂ := by
            rcases hdisj with hd | hd
            · exact absurd hp (Set.disjoint_left.mp hd hp0X)
            · exact fun z hz => Set.disjoint_left.mp hd hz
          have hcase : (p0 = a₁ ∧ (q0 = x₁ ∨ q0 = x₂)) ∨ (p0 = b₁ ∧ (q0 = y₁ ∨ q0 = y₂)) := by
            rcases hq0Q' with rfl | rfl | rfl | rfl
            · exact Or.inl ⟨p1x p0 hp _ (Or.inl rfl) hadj, Or.inl rfl⟩
            · exact Or.inr ⟨p1y p0 hp _ (Or.inl rfl) hadj, Or.inl rfl⟩
            · exact Or.inl ⟨p1x p0 hp _ (Or.inr rfl) hadj, Or.inr rfl⟩
            · exact Or.inr ⟨p1y p0 hp _ (Or.inr rfl) hadj, Or.inr rfl⟩
          rcases hcase with ⟨hp0eq, hq0⟩ | ⟨hp0eq, hq0⟩
          · rw [hp0eq] at hp0X hp
            refine cornerIntrinsic a₁ x₁ x₂ ka₁ kx₁ kx₂ ea₁x₁ ex₁x₂ ea₁x₂.symm ?_
            intro z hzX
            rcases kind z (hX hzX) with (h1 | h1) | hq
            · exact Or.inl (p1x z h1 q0 hq0 (hcompl z ⟨hzX, Or.inl h1⟩ q0 ⟨hq0X, hq0Q⟩))
            · exact absurd h1 (hXnP2 z hzX)
            · have hadj2 : G.Adj a₁ z := hcompl a₁ ⟨hp0X, Or.inl hp⟩ z ⟨hzX, (kQ z).2 hq⟩
              rcases hq with rfl | rfl | rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact absurd (p1y a₁ ha₁ _ (Or.inl rfl) hadj2) ha₁b₁
              · exact Or.inr (Or.inr rfl)
              · exact absurd (p1y a₁ ha₁ _ (Or.inr rfl) hadj2) ha₁b₁
          · rw [hp0eq] at hp0X hp
            refine cornerIntrinsic b₁ y₁ y₂ kb₁ ky₁ ky₂ eb₁y₁ ey₁y₂ eb₁y₂.symm ?_
            intro z hzX
            rcases kind z (hX hzX) with (h1 | h1) | hq
            · exact Or.inl (p1y z h1 q0 hq0 (hcompl z ⟨hzX, Or.inl h1⟩ q0 ⟨hq0X, hq0Q⟩))
            · exact absurd h1 (hXnP2 z hzX)
            · have hadj2 : G.Adj b₁ z := hcompl b₁ ⟨hp0X, Or.inl hp⟩ z ⟨hzX, (kQ z).2 hq⟩
              rcases hq with rfl | rfl | rfl | rfl
              · exact absurd (p1x b₁ hb₁ _ (Or.inl rfl) hadj2).symm ha₁b₁
              · exact Or.inr (Or.inl rfl)
              · exact absurd (p1x b₁ hb₁ _ (Or.inr rfl) hadj2).symm ha₁b₁
              · exact Or.inr (Or.inr rfl)
        · have hXnP1 : ∀ z ∈ X, z ∉ P₁ := by
            rcases hdisj with hd | hd
            · exact fun z hz => Set.disjoint_left.mp hd hz
            · exact absurd hp (Set.disjoint_left.mp hd hp0X)
          have hcase : (p0 = a₂ ∧ (q0 = x₁ ∨ q0 = y₂)) ∨ (p0 = b₂ ∧ (q0 = y₁ ∨ q0 = x₂)) := by
            rcases hq0Q' with rfl | rfl | rfl | rfl
            · exact Or.inl ⟨p2a p0 hp _ (Or.inl rfl) hadj, Or.inl rfl⟩
            · exact Or.inr ⟨p2b p0 hp _ (Or.inl rfl) hadj, Or.inl rfl⟩
            · exact Or.inr ⟨p2b p0 hp _ (Or.inr rfl) hadj, Or.inr rfl⟩
            · exact Or.inl ⟨p2a p0 hp _ (Or.inr rfl) hadj, Or.inr rfl⟩
          rcases hcase with ⟨hp0eq, hq0⟩ | ⟨hp0eq, hq0⟩
          · rw [hp0eq] at hp0X hp
            refine cornerIntrinsic a₂ x₁ y₂ ka₂ kx₁ ky₂ ea₂x₁ ex₁y₂ ea₂y₂.symm ?_
            intro z hzX
            rcases kind z (hX hzX) with (h1 | h1) | hq
            · exact absurd h1 (hXnP1 z hzX)
            · exact Or.inl (p2a z h1 q0 hq0 (hcompl z ⟨hzX, Or.inr h1⟩ q0 ⟨hq0X, hq0Q⟩))
            · have hadj2 : G.Adj a₂ z := hcompl a₂ ⟨hp0X, Or.inr hp⟩ z ⟨hzX, (kQ z).2 hq⟩
              rcases hq with rfl | rfl | rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact absurd (p2b a₂ ha₂ _ (Or.inl rfl) hadj2) ha₂b₂
              · exact absurd (p2b a₂ ha₂ _ (Or.inr rfl) hadj2) ha₂b₂
              · exact Or.inr (Or.inr rfl)
          · rw [hp0eq] at hp0X hp
            refine cornerIntrinsic b₂ y₁ x₂ kb₂ ky₁ kx₂ eb₂y₁ ey₁x₂ eb₂x₂.symm ?_
            intro z hzX
            rcases kind z (hX hzX) with (h1 | h1) | hq
            · exact absurd h1 (hXnP1 z hzX)
            · exact Or.inl (p2b z h1 q0 hq0 (hcompl z ⟨hzX, Or.inr h1⟩ q0 ⟨hq0X, hq0Q⟩))
            · have hadj2 : G.Adj b₂ z := hcompl b₂ ⟨hp0X, Or.inr hp⟩ z ⟨hzX, (kQ z).2 hq⟩
              rcases hq with rfl | rfl | rfl | rfl
              · exact absurd (p2a b₂ hb₂ _ (Or.inl rfl) hadj2).symm ha₂b₂
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
              · exact absurd (p2a b₂ hb₂ _ (Or.inr rfl) hadj2).symm ha₂b₂
      · have hXQonly : ∀ z ∈ X, (z = x₁ ∨ z = y₁ ∨ z = x₂ ∨ z = y₂) := by
          intro z hz
          rcases kind z (hX hz) with (h | h) | h
          · exact absurd ⟨z, hz, Or.inl h⟩ hXP
          · exact absurd ⟨z, hz, Or.inr h⟩ hXP
          · exact h
        have h1 : x₁ ∉ X ∨ y₁ ∉ X := by
          by_contra hc
          simp only [not_or, not_not] at hc
          refine hnQ1 ?_
          intro z hz
          rcases (by rw [hQ₁eq] at hz; simpa using hz : z = x₁ ∨ z = y₁) with rfl | rfl
          · exact hc.1
          · exact hc.2
        have h2 : x₂ ∉ X ∨ y₂ ∉ X := by
          by_contra hc
          simp only [not_or, not_not] at hc
          refine hnQ2 ?_
          intro z hz
          rcases (by rw [hQ₂eq] at hz; simpa using hz : z = x₂ ∨ z = y₂) with rfl | rfl
          · exact hc.1
          · exact hc.2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · refine cornerIntrinsic b₁ y₁ y₂ kb₁ ky₁ ky₂ eb₁y₁ ey₁y₂ eb₁y₂.symm ?_
          intro z hz
          rcases hXQonly z hz with rfl | rfl | rfl | rfl
          · exact absurd hz h1
          · exact Or.inr (Or.inl rfl)
          · exact absurd hz h2
          · exact Or.inr (Or.inr rfl)
        · refine cornerIntrinsic b₂ y₁ x₂ kb₂ ky₁ kx₂ eb₂y₁ ey₁x₂ eb₂x₂.symm ?_
          intro z hz
          rcases hXQonly z hz with rfl | rfl | rfl | rfl
          · exact absurd hz h1
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd hz h2
        · refine cornerIntrinsic a₂ x₁ y₂ ka₂ kx₁ ky₂ ea₂x₁ ex₁y₂ ea₂y₂.symm ?_
          intro z hz
          rcases hXQonly z hz with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact absurd hz h1
          · exact absurd hz h2
          · exact Or.inr (Or.inr rfl)
        · refine cornerIntrinsic a₁ x₁ x₂ ka₁ kx₁ kx₂ ea₁x₁ ex₁x₂ ea₁x₂.symm ?_
          intro z hz
          rcases hXQonly z hz with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact absurd hz h1
          · exact Or.inr (Or.inr rfl)
          · exact absurd hz h2
    · have hXPonly : ∀ z ∈ X, (z ∈ P₁ ∨ z ∈ P₂) := by
        intro z hz
        rcases kind z (hX hz) with h | h
        · exact h
        · exact absurd ⟨z, hz, (kQ z).2 h⟩ hXQ
      rcases hdisj with hd | hd
      · have hsub : ∀ z ∈ X, z ∈ P₂ := fun z hz =>
          (hXPonly z hz).resolve_left (Set.disjoint_left.mp hd hz)
        rcases Set.eq_empty_or_nonempty X with hXe | ⟨c, hc⟩
        · refine Or.inr (Or.inl ?_)
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rw [hXe]
          exact fun h => h
        · refine Or.inr (Or.inr ⟨⟨c, hX hc⟩, hc, ?_⟩)
          intro B hB
          exact reach2 _ _ (hsub c hc) (hsub _ hB)
      · have hsub : ∀ z ∈ X, z ∈ P₁ := fun z hz =>
          (hXPonly z hz).resolve_right (Set.disjoint_left.mp hd hz)
        rcases Set.eq_empty_or_nonempty X with hXe | ⟨c, hc⟩
        · refine Or.inr (Or.inl ?_)
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rw [hXe]
          exact fun h => h
        · refine Or.inr (Or.inr ⟨⟨c, hX hc⟩, hc, ?_⟩)
          intro B hB
          exact reach1 _ _ (hsub c hc) (hsub _ hB)
  · rintro (⟨A, B, C, hAB, hBC, hCA, hsub⟩ | hflat)
    · have hcorner := knot_triangle_is_corner G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
        hknot hP₁ hP₂ hA₁ hA₂ K hK hQ₁ hQ₂ hAB hBC hCA
      have hXsub : X ⊆ ({(A : V), (B : V), (C : V)} : Set V) := by
        intro z hz
        rcases hsub (show (⟨z, hX hz⟩ : ↥K) ∈ {v : ↥K | (v : V) ∈ X} from hz) with h | h | h
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (Or.inl (congrArg Subtype.val h))
        · exact Or.inr (Or.inr (congrArg Subtype.val h))
      rcases hcorner with hc | hc | hc | hc
      · rw [hc] at hXsub
        refine cornerLocal a₁ x₁ x₂ (Or.inl ha₁) (Or.inl rfl) (Or.inl rfl) ea₁x₁ ea₁x₂ ?_
        intro z hz
        have h := hXsub hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      · rw [hc] at hXsub
        refine cornerLocal a₂ x₁ y₂ (Or.inr ha₂) (Or.inl rfl) (Or.inr rfl) ea₂x₁ ea₂y₂ ?_
        intro z hz
        have h := hXsub hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      · rw [hc] at hXsub
        refine cornerLocal b₁ y₁ y₂ (Or.inl hb₁) (Or.inr rfl) (Or.inr rfl) eb₁y₁ eb₁y₂ ?_
        intro z hz
        have h := hXsub hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      · rw [hc] at hXsub
        refine cornerLocal b₂ y₁ x₂ (Or.inr hb₂) (Or.inr rfl) (Or.inl rfl) eb₂y₁ eb₂x₂ ?_
        intro z hz
        have h := hXsub hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
    · rcases hflat with hempty | ⟨A, hA, hreach⟩
      · refine pathLocal1 (fun z hz => ?_)
        exfalso
        have h1 : (⟨z, hX hz⟩ : ↥K) ∈ ({v : ↥K | (v : V) ∈ X}) := hz
        rw [hempty] at h1
        exact h1
      · rcases kind (A : V) A.2 with (h | h) | h
        · have step : ∀ s t : ↥K, FlatAdj (G.induce K) s t → (s : V) ∈ P₁ → (t : V) ∈ P₁ := by
            intro s t hst hs
            rcases flatmem s t hst with ⟨-, h2⟩ | ⟨h1, -⟩
            · exact h2
            · exact absurd hs (fun hh => d12 _ hh h1)
          have hall : ∀ B : ↥K, Relation.ReflTransGen (FlatAdj (G.induce K)) A B →
              (B : V) ∈ P₁ := by
            intro B hB
            induction hB with
            | refl => exact h
            | tail _ h2 ih => exact step _ _ h2 ih
          exact pathLocal1 (fun z hz => hall ⟨z, hX hz⟩ (hreach _ hz))
        · have step : ∀ s t : ↥K, FlatAdj (G.induce K) s t → (s : V) ∈ P₂ → (t : V) ∈ P₂ := by
            intro s t hst hs
            rcases flatmem s t hst with ⟨h1, -⟩ | ⟨-, h2⟩
            · exact absurd h1 (fun hh => d12 _ hh hs)
            · exact h2
          have hall : ∀ B : ↥K, Relation.ReflTransGen (FlatAdj (G.induce K)) A B →
              (B : V) ∈ P₂ := by
            intro B hB
            induction hB with
            | refl => exact h
            | tail _ h2 ih => exact step _ _ h2 ih
          exact pathLocal2 (fun z hz => hall ⟨z, hX hz⟩ (hreach _ hz))
        · have hall : ∀ B : ↥K, Relation.ReflTransGen (FlatAdj (G.induce K)) A B → B = A := by
            intro B hB
            induction hB with
            | refl => rfl
            | tail h1 h2 ih =>
                exfalso
                rw [ih] at h2
                rcases flatmem _ _ h2 with ⟨hp, -⟩ | ⟨hp, -⟩
                · exact notP1 _ h hp
                · exact notP2 _ h hp
          exact singLocal (A : V) h
            (fun z hz => congrArg Subtype.val (hall ⟨z, hX hz⟩ (hreach _ hz)))

private theorem one_of_two_of_subsingleton {X S : Set V} {p q : V}
    (hS : (S \ X).Subsingleton) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    p ∈ X ∨ q ∈ X := by
  by_contra h
  simp only [not_or] at h
  exact hpq (hS ⟨hp, h.1⟩ ⟨hq, h.2⟩)

/-- Resolution is equivalent to missing at most one vertex from each of the four corner
triangles, together with meeting the two path branches. -/
lemma resolvesKnot_iff_corner_saturation (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hQ₁len : pathLength Q₁ = 1) (hQ₂len : pathLength Q₂ = 1) (X : Set V) :
    ResolvesKnot G P₁ P₂ Q₁ Q₂ X ↔
      (({x₁, x₂, a₁} : Set V) \ X).Subsingleton ∧
      (({x₁, y₂, a₂} : Set V) \ X).Subsingleton ∧
      (({y₁, y₂, b₁} : Set V) \ X).Subsingleton ∧
      (({y₁, x₂, b₂} : Set V) \ X).Subsingleton ∧
      (X ∩ {v : V | v ∈ P₁}).Nonempty ∧ (X ∩ {v : V | v ∈ P₂}).Nonempty := by
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq12, -, -, -, -, -, hcomp,
    hE11, hE12, hE21, hE22, -⟩ :=
    Workspace.ProofLemmas.KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have hQ₁eq : Q₁ = [x₁, y₁] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hQ₁ hQ₁len
  have hQ₂eq : Q₂ = [x₂, y₂] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hQ₂ hQ₂len
  have ha₁ : a₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).1
  have hb₁ : b₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).2
  have ha₂ : a₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).1
  have hb₂ : b₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).2
  have hx₁ : x₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hy₁ : y₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hx₂ : x₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have hy₂ : y₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have ex₁x₂ : G.Adj x₁ x₂ := hcomp x₁ hx₁ x₂ hx₂
  have ex₁y₂ : G.Adj x₁ y₂ := hcomp x₁ hx₁ y₂ hy₂
  have ey₁x₂ : G.Adj y₁ x₂ := hcomp y₁ hy₁ x₂ hx₂
  have ey₁y₂ : G.Adj y₁ y₂ := hcomp y₁ hy₁ y₂ hy₂
  have ea₁x₁ : G.Adj a₁ x₁ :=
    (hE11 a₁ ha₁ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₁x₂ : G.Adj a₁ x₂ :=
    (hE12 a₁ ha₁ x₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₁y₁ : G.Adj b₁ y₁ :=
    (hE11 b₁ hb₁ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₁y₂ : G.Adj b₁ y₂ :=
    (hE12 b₁ hb₁ y₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have ea₂x₁ : G.Adj a₂ x₁ :=
    (hE21 a₂ ha₂ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₂y₂ : G.Adj a₂ y₂ :=
    (hE22 a₂ ha₂ y₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₂y₁ : G.Adj b₂ y₁ :=
    (hE21 b₂ hb₂ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₂x₂ : G.Adj b₂ x₂ :=
    (hE22 b₂ hb₂ x₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have hx₁y₁ : x₁ ≠ y₁ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hQ₁.1
    rw [hQ₁eq] at hn
    simpa using hn
  have hx₂y₂ : x₂ ≠ y₂ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hQ₂.1
    rw [hQ₂eq] at hn
    simpa using hn
  have p₁U : ∀ v ∈ P₁, v ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} : Set V) :=
    fun v hv => Or.inl hv
  have p₂U : ∀ v ∈ P₂, v ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} : Set V) :=
    fun v hv => Or.inr hv
  have q₁U : ∀ v ∈ Q₁, v ∈ ({v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) :=
    fun v hv => Or.inl hv
  have q₂U : ∀ v ∈ Q₂, v ∈ ({v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) :=
    fun v hv => Or.inr hv
  constructor
  · rintro ⟨hinc, hmeet₁, hmeet₂, hcover⟩
    have qchoice : ∀ q ∈ Q₁, ∀ r ∈ Q₂, q ∈ X ∨ r ∈ X := by
      intro q hq r hr
      rcases hinc with hinc | hinc
      · exact Or.inl (hinc hq)
      · exact Or.inr (hinc hr)
    have corner : ∀ (p q r : V),
        p ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} : Set V) →
        q ∈ Q₁ → r ∈ Q₂ → G.Adj p q → G.Adj p r →
        (({p, q, r} : Set V) \ X).Subsingleton := by
      intro p q r hp hq hr hpq hpr z hz z' hz'
      have hpqX := hcover p hp q (q₁U q hq) hpq
      have hprX := hcover p hp r (q₂U r hr) hpr
      have hqrX := qchoice q hq r hr
      rcases hz with ⟨hz, hnz⟩
      rcases hz' with ⟨hz', hnz'⟩
      rcases hz with hz | hz | hz <;> rcases hz' with hz' | hz' | hz'
      all_goals subst_vars
      all_goals try rfl
      all_goals exfalso; tauto
    exact ⟨by
        rw [show ({x₁, x₂, a₁} : Set V) = {a₁, x₁, x₂} by ext z; simp; tauto]
        exact corner a₁ x₁ x₂ (p₁U a₁ ha₁) hx₁ hx₂ ea₁x₁ ea₁x₂,
      by
        rw [show ({x₁, y₂, a₂} : Set V) = {a₂, x₁, y₂} by ext z; simp; tauto]
        exact corner a₂ x₁ y₂ (p₂U a₂ ha₂) hx₁ hy₂ ea₂x₁ ea₂y₂,
      by
        rw [show ({y₁, y₂, b₁} : Set V) = {b₁, y₁, y₂} by ext z; simp; tauto]
        exact corner b₁ y₁ y₂ (p₁U b₁ hb₁) hy₁ hy₂ eb₁y₁ eb₁y₂,
      by
        rw [show ({y₁, x₂, b₂} : Set V) = {b₂, y₁, x₂} by ext z; simp; tauto]
        exact corner b₂ y₁ x₂ (p₂U b₂ hb₂) hy₁ hx₂ eb₂y₁ eb₂x₂,
      hmeet₁, hmeet₂⟩
  · rintro ⟨hT₁, hT₂, hT₃, hT₄, hmeet₁, hmeet₂⟩
    have s₁ : x₁ ∈ X ∨ x₂ ∈ X :=
      one_of_two_of_subsingleton hT₁ (by simp) (by simp) ex₁x₂.ne
    have s₂ : x₁ ∈ X ∨ y₂ ∈ X :=
      one_of_two_of_subsingleton hT₂ (by simp) (by simp) ex₁y₂.ne
    have s₃ : y₁ ∈ X ∨ y₂ ∈ X :=
      one_of_two_of_subsingleton hT₃ (by simp) (by simp) ey₁y₂.ne
    have s₄ : y₁ ∈ X ∨ x₂ ∈ X :=
      one_of_two_of_subsingleton hT₄ (by simp) (by simp) ey₁x₂.ne
    refine ⟨?_, hmeet₁, hmeet₂, ?_⟩
    · have key : (x₁ ∈ X ∧ y₁ ∈ X) ∨ (x₂ ∈ X ∧ y₂ ∈ X) := by tauto
      rcases key with h | h
      · left
        intro v hv
        rw [hQ₁eq] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact h.1
        · exact h.2
      · right
        intro v hv
        rw [hQ₂eq] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact h.1
        · exact h.2
    · intro u hu w hw huw
      simp only [Set.mem_union, Set.mem_setOf_eq] at hu hw
      rw [hQ₁eq, hQ₂eq] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hu with hu | hu
      · rcases hw with (hwe | hwe) | (hwe | hwe)
        · have hua : u = a₁ := by
            rw [hwe] at huw
            rcases (hE11 u hu x₁ (by simp)).mp huw with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd h hx₁y₁
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₁ (by simp) (by simp) ea₁x₁.ne
        · have hua : u = b₁ := by
            rw [hwe] at huw
            rcases (hE11 u hu y₁ (by simp)).mp huw with ⟨-, h⟩ | ⟨h, -⟩
            · exact absurd h.symm hx₁y₁
            · exact h
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₃ (by simp) (by simp) eb₁y₁.ne
        · have hua : u = a₁ := by
            rw [hwe] at huw
            rcases (hE12 u hu x₂ (by simp)).mp huw with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd h hx₂y₂
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₁ (by simp) (by simp) ea₁x₂.ne
        · have hua : u = b₁ := by
            rw [hwe] at huw
            rcases (hE12 u hu y₂ (by simp)).mp huw with ⟨-, h⟩ | ⟨h, -⟩
            · exact absurd h.symm hx₂y₂
            · exact h
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₃ (by simp) (by simp) eb₁y₂.ne
      · rcases hw with (hwe | hwe) | (hwe | hwe)
        · have hua : u = a₂ := by
            rw [hwe] at huw
            rcases (hE21 u hu x₁ (by simp)).mp huw with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd h hx₁y₁
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₂ (by simp) (by simp) ea₂x₁.ne
        · have hua : u = b₂ := by
            rw [hwe] at huw
            rcases (hE21 u hu y₁ (by simp)).mp huw with ⟨-, h⟩ | ⟨h, -⟩
            · exact absurd h.symm hx₁y₁
            · exact h
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₄ (by simp) (by simp) eb₂y₁.ne
        · have hua : u = b₂ := by
            rw [hwe] at huw
            rcases (hE22 u hu x₂ (by simp)).mp huw with ⟨-, h⟩ | ⟨h, -⟩
            · exact absurd h hx₂y₂
            · exact h
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₄ (by simp) (by simp) eb₂x₂.ne
        · have hua : u = a₂ := by
            rw [hwe] at huw
            rcases (hE22 u hu y₂ (by simp)).mp huw with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd h hx₂y₂.symm
          rw [hwe, hua]
          exact one_of_two_of_subsingleton hT₂ (by simp) (by simp) ea₂y₂.ne

/-- PAPER (proof of 9.2, printed p. 48): *"The proof is obvious and we omit it."*

This is the resolving part of the omitted knot dictionary.  The four corner triangles are all
the triangles of the induced graph, so meeting at least two vertices of every one is precisely
the edge-cover condition in `ResolvesKnot`, once one antipath is included. -/
lemma resolvesKnot_iff_intrinsic (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hQ₁ : pathLength Q₁ = 1) (hQ₂ : pathLength Q₂ = 1)
    (X : Set V) (hX : X ⊆ K) :
    ResolvesKnot G P₁ P₂ Q₁ Q₂ X ↔
      IntrinsicSaturates (G.induce K) {v : ↥K | (v : V) ∈ X} ∧
        (X ∩ {v : V | v ∈ P₁}).Nonempty ∧
        (X ∩ {v : V | v ∈ P₂}).Nonempty := by
  have hknot' := hknot
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hP₁, hP₂, hA₁, hA₂, -⟩ := hknot'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcomp, hE11, hE12, hE21, hE22, -⟩ :=
    Workspace.ProofLemmas.KnotLabels.knot_labels hknot hP₁ hP₂ hA₁ hA₂
  have hQ₁eq : Q₁ = [x₁, y₁] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hA₁ hQ₁
  have hQ₂eq : Q₂ = [x₂, y₂] :=
    Workspace.ProofLemmas.KnotLabels.anti_eq_pair_of_length_one hA₂ hQ₂
  have ha₁ : a₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).1
  have hb₁ : b₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).2
  have ha₂ : a₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).1
  have hb₂ : b₂ ∈ P₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂).2
  have hx₁ : x₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hy₁ : y₁ ∈ Q₁ := by rw [hQ₁eq]; simp
  have hx₂ : x₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have hy₂ : y₂ ∈ Q₂ := by rw [hQ₂eq]; simp
  have memK : ∀ z : V, z ∈ P₁ ∨ z ∈ P₂ ∨ z ∈ Q₁ ∨ z ∈ Q₂ → z ∈ K := by
    intro z hz
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    tauto
  have ka₁ := memK a₁ (Or.inl ha₁)
  have kb₁ := memK b₁ (Or.inl hb₁)
  have ka₂ := memK a₂ (Or.inr (Or.inl ha₂))
  have kb₂ := memK b₂ (Or.inr (Or.inl hb₂))
  have kx₁ := memK x₁ (Or.inr (Or.inr (Or.inl hx₁)))
  have ky₁ := memK y₁ (Or.inr (Or.inr (Or.inl hy₁)))
  have kx₂ := memK x₂ (Or.inr (Or.inr (Or.inr hx₂)))
  have ky₂ := memK y₂ (Or.inr (Or.inr (Or.inr hy₂)))
  have ex₁x₂ : G.Adj x₁ x₂ := hcomp x₁ hx₁ x₂ hx₂
  have ex₁y₂ : G.Adj x₁ y₂ := hcomp x₁ hx₁ y₂ hy₂
  have ey₁x₂ : G.Adj y₁ x₂ := hcomp y₁ hy₁ x₂ hx₂
  have ey₁y₂ : G.Adj y₁ y₂ := hcomp y₁ hy₁ y₂ hy₂
  have ea₁x₁ : G.Adj a₁ x₁ :=
    (hE11 a₁ ha₁ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₁x₂ : G.Adj a₁ x₂ :=
    (hE12 a₁ ha₁ x₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₁y₁ : G.Adj b₁ y₁ :=
    (hE11 b₁ hb₁ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₁y₂ : G.Adj b₁ y₂ :=
    (hE12 b₁ hb₁ y₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have ea₂x₁ : G.Adj a₂ x₁ :=
    (hE21 a₂ ha₂ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₂y₂ : G.Adj a₂ y₂ :=
    (hE22 a₂ ha₂ y₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₂y₁ : G.Adj b₂ y₁ :=
    (hE21 b₂ hb₂ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₂x₂ : G.Adj b₂ x₂ :=
    (hE22 b₂ hb₂ x₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  let XK : Set (↥K) := {v | (v : V) ∈ X}
  have rawCorner : ∀ (p q r : V), ∀ (kp : p ∈ K) (kq : q ∈ K) (kr : r ∈ K),
      G.Adj p q → G.Adj q r → G.Adj r p → IntrinsicSaturates (G.induce K) XK →
      (({p, q, r} : Set V) \ X).Subsingleton := by
    intro p q r kp kq kr hpq hqr hrp hs z hz z' hz'
    have kz : z ∈ K := by
      rcases hz.1 with rfl | rfl | rfl
      · exact kp
      · exact kq
      · exact kr
    have kz' : z' ∈ K := by
      rcases hz'.1 with rfl | rfl | rfl
      · exact kp
      · exact kq
      · exact kr
    let P : ↥K := ⟨p, kp⟩
    let Q : ↥K := ⟨q, kq⟩
    let R : ↥K := ⟨r, kr⟩
    let Z : ↥K := ⟨z, kz⟩
    let Z' : ↥K := ⟨z', kz'⟩
    have hsub := hs P Q R hpq hqr hrp
    have hzsub : Z ∈ ({P, Q, R} : Set (↥K)) \ XK := by
      refine ⟨?_, hz.2⟩
      rcases hz.1 with hz | hz | hz
      · exact Or.inl (Subtype.ext hz)
      · exact Or.inr (Or.inl (Subtype.ext hz))
      · exact Or.inr (Or.inr (Subtype.ext hz))
    have hzsub' : Z' ∈ ({P, Q, R} : Set (↥K)) \ XK := by
      refine ⟨?_, hz'.2⟩
      rcases hz'.1 with hz | hz | hz
      · exact Or.inl (Subtype.ext hz)
      · exact Or.inr (Or.inl (Subtype.ext hz))
      · exact Or.inr (Or.inr (Subtype.ext hz))
    exact congrArg Subtype.val (hsub hzsub hzsub')
  have intrinsic_iff_corners : IntrinsicSaturates (G.induce K) XK ↔
      (({x₁, x₂, a₁} : Set V) \ X).Subsingleton ∧
      (({x₁, y₂, a₂} : Set V) \ X).Subsingleton ∧
      (({y₁, y₂, b₁} : Set V) \ X).Subsingleton ∧
      (({y₁, x₂, b₂} : Set V) \ X).Subsingleton := by
    constructor
    · intro hs
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact rawCorner x₁ x₂ a₁ kx₁ kx₂ ka₁ ex₁x₂ ea₁x₂.symm ea₁x₁ hs
      · exact rawCorner x₁ y₂ a₂ kx₁ ky₂ ka₂ ex₁y₂ ea₂y₂.symm ea₂x₁ hs
      · exact rawCorner y₁ y₂ b₁ ky₁ ky₂ kb₁ ey₁y₂ eb₁y₂.symm eb₁y₁ hs
      · exact rawCorner y₁ x₂ b₂ ky₁ kx₂ kb₂ ey₁x₂ eb₂x₂.symm eb₂y₁ hs
    · rintro ⟨hT₁, hT₂, hT₃, hT₄⟩ u v w huv hvw hwu z hz z' hz'
      have hc := knot_triangle_is_corner G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
        hknot hP₁ hP₂ hA₁ hA₂ K hK hQ₁ hQ₂ huv hvw hwu
      have hraw : (({(u : V), (v : V), (w : V)} : Set V) \ X).Subsingleton := by
        rcases hc with hc | hc | hc | hc
        · rw [hc]; exact hT₁
        · rw [hc]; exact hT₂
        · rw [hc]; exact hT₃
        · rw [hc]; exact hT₄
      apply Subtype.ext
      apply hraw
      · refine ⟨?_, hz.2⟩
        rcases hz.1 with hz | hz | hz
        · exact Or.inl (congrArg Subtype.val hz)
        · exact Or.inr (Or.inl (congrArg Subtype.val hz))
        · exact Or.inr (Or.inr (congrArg Subtype.val hz))
      · refine ⟨?_, hz'.2⟩
        rcases hz'.1 with hz' | hz' | hz'
        · exact Or.inl (congrArg Subtype.val hz')
        · exact Or.inr (Or.inl (congrArg Subtype.val hz'))
        · exact Or.inr (Or.inr (congrArg Subtype.val hz'))
  change ResolvesKnot G P₁ P₂ Q₁ Q₂ X ↔ IntrinsicSaturates (G.induce K) XK ∧
    (X ∩ {v : V | v ∈ P₁}).Nonempty ∧ (X ∩ {v : V | v ∈ P₂}).Nonempty
  rw [resolvesKnot_iff_corner_saturation G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
    hknot hP₁ hP₂ hA₁ hA₂ hQ₁ hQ₂ X]
  rw [intrinsic_iff_corners]
  tauto

end Workspace.ProofLemmas.Thm92KnotDictionary
