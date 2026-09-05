import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.Thm92Intrinsic
import Workspace.ProofLemmas.KnotLabels
import Workspace.ProofLemmas.PathBasics

/-!
# The six branches of a knot with length-one antipaths

PAPER (proof of 9.2, printed p. 48): *"The proof is obvious and we omit it."*

Let `(P₁,P₂,Q₁,Q₂)` be a knot whose two antipaths have length one, and let `K` be the vertex
set it induces.  Then `G|K` is the line graph of a subdivision of `K₄`: its triangles are the
four triples `{x₁,x₂,a₁}`, `{x₁,y₂,a₂}`, `{y₁,y₂,b₁}`, `{y₁,x₂,b₂}` and its remaining edges are
the edges of `P₁` and of `P₂`.  This file proves the "remaining edges" half, in the intrinsic
language of `Thm92Intrinsic`: an edge of `G|K` is flat exactly when both of its ends lie on the
same one of `P₁, P₂`, so the flat components are `V(P₁)`, `V(P₂)` and the four singletons
`{x₁}, {y₁}, {x₂}, {y₂}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm92Branches

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm92Intrinsic

variable {V : Type*}

/-- An induced path contains no triangle. -/
theorem path_no_triangle {F : SimpleGraph V} {p : List V}
    (hp : IsPathList F p) {a b c : V} (ha : a ∈ p) (hb : b ∈ p) (hc : c ∈ p)
    (hab : F.Adj a b) (hbc : F.Adj b c) (hca : F.Adj c a) : False := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
  have h1 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hi hj).mp hab
  have h2 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hj hk).mp hbc
  have h3 := (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hk hi).mp hca
  omega

/-- **The flat structure of a knot with length-one antipaths.**

The three conclusions say: any two vertices of `P₁` are joined by a chain of flat edges, the
same for `P₂`, and every flat edge has both ends on the same one of `P₁, P₂`.  Together they
identify the flat components of `G|K` with `V(P₁)`, `V(P₂)` and the four singletons of the
antipath vertices. -/
theorem branch_dictionary [DecidableEq V] (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hQ₁len : pathLength Q₁ = 1) (hQ₂len : pathLength Q₂ = 1) :
    (∀ u v : ↥K, (u : V) ∈ P₁ → (v : V) ∈ P₁ →
        Relation.ReflTransGen (FlatAdj (G.induce K)) u v) ∧
    (∀ u v : ↥K, (u : V) ∈ P₂ → (v : V) ∈ P₂ →
        Relation.ReflTransGen (FlatAdj (G.induce K)) u v) ∧
    (∀ u v : ↥K, FlatAdj (G.induce K) u v →
        ((u : V) ∈ P₁ ∧ (v : V) ∈ P₁) ∨ ((u : V) ∈ P₂ ∧ (v : V) ∈ P₂)) := by
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq12, -, -, -, -, hanti, hcomp,
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
  -- the four corner edges between the antipaths
  have ex₁x₂ : G.Adj x₁ x₂ := hcomp x₁ hx₁ x₂ hx₂
  have ex₁y₂ : G.Adj x₁ y₂ := hcomp x₁ hx₁ y₂ hy₂
  have ey₁x₂ : G.Adj y₁ x₂ := hcomp y₁ hy₁ x₂ hx₂
  have ey₁y₂ : G.Adj y₁ y₂ := hcomp y₁ hy₁ y₂ hy₂
  -- the eight edges between the paths and the antipaths
  have ea₁x₁ : G.Adj a₁ x₁ := (hE11 a₁ ha₁ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₁x₂ : G.Adj a₁ x₂ := (hE12 a₁ ha₁ x₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₁y₁ : G.Adj b₁ y₁ := (hE11 b₁ hb₁ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₁y₂ : G.Adj b₁ y₂ := (hE12 b₁ hb₁ y₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have ea₂x₁ : G.Adj a₂ x₁ := (hE21 a₂ ha₂ x₁ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have ea₂y₂ : G.Adj a₂ y₂ := (hE22 a₂ ha₂ y₂ (by simp)).2 (Or.inl ⟨rfl, rfl⟩)
  have eb₂y₁ : G.Adj b₂ y₁ := (hE21 b₂ hb₂ y₁ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  have eb₂x₂ : G.Adj b₂ x₂ := (hE22 b₂ hb₂ x₂ (by simp)).2 (Or.inr ⟨rfl, rfl⟩)
  -- the antipath vertices are four distinct vertices
  have hx₁y₁ : x₁ ≠ y₁ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hQ₁.1
    rw [hQ₁eq] at hn; simpa using hn
  have hx₂y₂ : x₂ ≠ y₂ := by
    have hn := Workspace.ProofLemmas.PathBasics.antipath_nodup hQ₂.1
    rw [hQ₂eq] at hn; simpa using hn
  have hx₁x₂ : x₁ ≠ x₂ := fun h => dq12 x₁ hx₁ (h ▸ hx₂)
  have hx₁y₂ : x₁ ≠ y₂ := fun h => dq12 x₁ hx₁ (h ▸ hy₂)
  have hy₁x₂ : y₁ ≠ x₂ := fun h => dq12 y₁ hy₁ (h ▸ hx₂)
  have hy₁y₂ : y₁ ≠ y₂ := fun h => dq12 y₁ hy₁ (h ▸ hy₂)
  -- membership in `K`
  have memK : ∀ z : V, z ∈ P₁ ∨ z ∈ P₂ ∨ z ∈ Q₁ ∨ z ∈ Q₂ → z ∈ K := by
    intro z hz
    rw [hK]; simp only [Set.mem_union, Set.mem_setOf_eq]; tauto
  have ka₁ := memK a₁ (Or.inl ha₁)
  have kb₁ := memK b₁ (Or.inl hb₁)
  have ka₂ := memK a₂ (Or.inr (Or.inl ha₂))
  have kb₂ := memK b₂ (Or.inr (Or.inl hb₂))
  have kx₁ := memK x₁ (Or.inr (Or.inr (Or.inl hx₁)))
  have ky₁ := memK y₁ (Or.inr (Or.inr (Or.inl hy₁)))
  have kx₂ := memK x₂ (Or.inr (Or.inr (Or.inr hx₂)))
  have ky₂ := memK y₂ (Or.inr (Or.inr (Or.inr hy₂)))
  -- every vertex of `K` is on `P₁`, on `P₂`, or one of the four antipath vertices
  have kind : ∀ t : V, t ∈ K → t ∈ P₁ ∨ t ∈ P₂ ∨ t = x₁ ∨ t = y₁ ∨ t = x₂ ∨ t = y₂ := by
    intro t ht
    rw [hK] at ht
    simp only [Set.mem_union, Set.mem_setOf_eq] at ht
    rcases ht with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [hQ₁eq] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      tauto
    · rw [hQ₂eq] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      tauto
  -- reading off which end of a path an antipath vertex can be adjacent to
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
  -- an edge of `P₁` or of `P₂` lies in no triangle
  have flat1 : ∀ u v : ↥K, (u : V) ∈ P₁ → (v : V) ∈ P₁ → G.Adj (u : V) (v : V) →
      FlatAdj (G.induce K) u v := by
    intro u v hu hv huv
    refine ⟨huv, ?_⟩
    rintro ⟨c, hc1, hc2⟩
    have hc1' : G.Adj (u : V) (c : V) := hc1
    have hc2' : G.Adj (v : V) (c : V) := hc2
    rcases kind (c : V) c.2 with hc | hc | rfl | rfl | rfl | rfl
    · exact path_no_triangle hP₁.1 hu hv hc huv hc2' hc1'.symm
    · exact hanti (u : V) hu (c : V) hc hc1'
    · exact huv.ne ((p1x _ hu _ (Or.inl rfl) hc1').trans (p1x _ hv _ (Or.inl rfl) hc2').symm)
    · exact huv.ne ((p1y _ hu _ (Or.inl rfl) hc1').trans (p1y _ hv _ (Or.inl rfl) hc2').symm)
    · exact huv.ne ((p1x _ hu _ (Or.inr rfl) hc1').trans (p1x _ hv _ (Or.inr rfl) hc2').symm)
    · exact huv.ne ((p1y _ hu _ (Or.inr rfl) hc1').trans (p1y _ hv _ (Or.inr rfl) hc2').symm)
  have flat2 : ∀ u v : ↥K, (u : V) ∈ P₂ → (v : V) ∈ P₂ → G.Adj (u : V) (v : V) →
      FlatAdj (G.induce K) u v := by
    intro u v hu hv huv
    refine ⟨huv, ?_⟩
    rintro ⟨c, hc1, hc2⟩
    have hc1' : G.Adj (u : V) (c : V) := hc1
    have hc2' : G.Adj (v : V) (c : V) := hc2
    rcases kind (c : V) c.2 with hc | hc | rfl | rfl | rfl | rfl
    · exact hanti (c : V) hc (u : V) hu hc1'.symm
    · exact path_no_triangle hP₂.1 hu hv hc huv hc2' hc1'.symm
    · exact huv.ne ((p2a _ hu _ (Or.inl rfl) hc1').trans (p2a _ hv _ (Or.inl rfl) hc2').symm)
    · exact huv.ne ((p2b _ hu _ (Or.inl rfl) hc1').trans (p2b _ hv _ (Or.inl rfl) hc2').symm)
    · exact huv.ne ((p2b _ hu _ (Or.inr rfl) hc1').trans (p2b _ hv _ (Or.inr rfl) hc2').symm)
    · exact huv.ne ((p2a _ hu _ (Or.inr rfl) hc1').trans (p2a _ hv _ (Or.inr rfl) hc2').symm)
  -- every other edge of `G|K` lies in a triangle
  have mixed : ∀ t q : V, (t ∈ P₁ ∨ t ∈ P₂) →
      (q = x₁ ∨ q = y₁ ∨ q = x₂ ∨ q = y₂) → G.Adj t q →
      ∃ c : V, c ∈ K ∧ G.Adj t c ∧ G.Adj q c := by
    rintro t q (ht | ht) (rfl | rfl | rfl | rfl) hadj
    · exact ⟨x₂, kx₂, (p1x t ht _ (Or.inl rfl) hadj) ▸ ea₁x₂, ex₁x₂⟩
    · exact ⟨y₂, ky₂, (p1y t ht _ (Or.inl rfl) hadj) ▸ eb₁y₂, ey₁y₂⟩
    · exact ⟨x₁, kx₁, (p1x t ht _ (Or.inr rfl) hadj) ▸ ea₁x₁, ex₁x₂.symm⟩
    · exact ⟨y₁, ky₁, (p1y t ht _ (Or.inr rfl) hadj) ▸ eb₁y₁, ey₁y₂.symm⟩
    · exact ⟨y₂, ky₂, (p2a t ht _ (Or.inl rfl) hadj) ▸ ea₂y₂, ex₁y₂⟩
    · exact ⟨x₂, kx₂, (p2b t ht _ (Or.inl rfl) hadj) ▸ eb₂x₂, ey₁x₂⟩
    · exact ⟨y₁, ky₁, (p2b t ht _ (Or.inr rfl) hadj) ▸ eb₂y₁, ey₁x₂.symm⟩
    · exact ⟨x₁, kx₁, (p2a t ht _ (Or.inr rfl) hadj) ▸ ea₂x₁, ex₁y₂.symm⟩
  have qq : ∀ q r : V, (q = x₁ ∨ q = y₁ ∨ q = x₂ ∨ q = y₂) →
      (r = x₁ ∨ r = y₁ ∨ r = x₂ ∨ r = y₂) → G.Adj q r →
      ∃ c : V, c ∈ K ∧ G.Adj q c ∧ G.Adj r c := by
    have hnQ₁ : ¬ G.Adj x₁ y₁ := by
      have hQ₁' : IsAntipathFrom G [x₁, y₁] x₁ y₁ := by simpa [hQ₁eq] using hQ₁
      exact ((hQ₁'.1.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)).2
    have hnQ₂ : ¬ G.Adj x₂ y₂ := by
      have hQ₂' : IsAntipathFrom G [x₂, y₂] x₂ y₂ := by simpa [hQ₂eq] using hQ₂
      exact ((hQ₂'.1.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)).2
    rintro q r (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) hadj
    · exact absurd rfl hadj.ne
    · exact absurd hadj hnQ₁
    · exact ⟨a₁, ka₁, ea₁x₁.symm, ea₁x₂.symm⟩
    · exact ⟨a₂, ka₂, ea₂x₁.symm, ea₂y₂.symm⟩
    · exact absurd hadj.symm hnQ₁
    · exact absurd rfl hadj.ne
    · exact ⟨b₂, kb₂, eb₂y₁.symm, eb₂x₂.symm⟩
    · exact ⟨b₁, kb₁, eb₁y₁.symm, eb₁y₂.symm⟩
    · exact ⟨a₁, ka₁, ea₁x₂.symm, ea₁x₁.symm⟩
    · exact ⟨b₂, kb₂, eb₂x₂.symm, eb₂y₁.symm⟩
    · exact absurd rfl hadj.ne
    · exact absurd hadj hnQ₂
    · exact ⟨a₂, ka₂, ea₂y₂.symm, ea₂x₁.symm⟩
    · exact ⟨b₁, kb₁, eb₁y₂.symm, eb₁y₁.symm⟩
    · exact absurd hadj.symm hnQ₂
    · exact absurd rfl hadj.ne
  have kind2 : ∀ t : V, t ∈ K →
      (t ∈ P₁ ∨ t ∈ P₂) ∨ (t = x₁ ∨ t = y₁ ∨ t = x₂ ∨ t = y₂) := by
    intro t ht
    rcases kind t ht with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have flatmem : ∀ u v : ↥K, FlatAdj (G.induce K) u v →
      ((u : V) ∈ P₁ ∧ (v : V) ∈ P₁) ∨ ((u : V) ∈ P₂ ∧ (v : V) ∈ P₂) := by
    intro u v hf
    have huv : G.Adj (u : V) (v : V) := hf.1
    have hcommon : (((u : V) ∈ P₁ ∧ (v : V) ∈ P₁) ∨ ((u : V) ∈ P₂ ∧ (v : V) ∈ P₂)) ∨
        ∃ c : V, c ∈ K ∧ G.Adj (u : V) c ∧ G.Adj (v : V) c := by
      rcases kind2 _ u.2 with hu | hu
      · rcases kind2 _ v.2 with hv | hv
        · rcases hu with hu | hu
          · rcases hv with hv | hv
            · exact Or.inl (Or.inl ⟨hu, hv⟩)
            · exact absurd huv (hanti _ hu _ hv)
          · rcases hv with hv | hv
            · exact absurd huv.symm (hanti _ hv _ hu)
            · exact Or.inl (Or.inr ⟨hu, hv⟩)
        · exact Or.inr (mixed _ _ hu hv huv)
      · rcases kind2 _ v.2 with hv | hv
        · exact Or.inr ((mixed _ _ hv hu huv.symm).imp
            (fun c hc => ⟨hc.1, hc.2.2, hc.2.1⟩))
        · exact Or.inr (qq _ _ hu hv huv)
    rcases hcommon with h | ⟨c, hcK, h1, h2⟩
    · exact h
    · exact (hf.2 ⟨⟨c, hcK⟩, h1, h2⟩).elim
  -- flat reachability along a path
  have hidx1 : ∀ (i : ℕ) (hi : i < P₁.length), (P₁[i]'hi) ∈ K :=
    fun i hi => memK _ (Or.inl (List.getElem_mem hi))
  have hidx2 : ∀ (i : ℕ) (hi : i < P₂.length), (P₂[i]'hi) ∈ K :=
    fun i hi => memK _ (Or.inr (Or.inl (List.getElem_mem hi)))
  have up1 : ∀ (j i : ℕ) (hi : i < P₁.length) (hj : j < P₁.length), i ≤ j →
      Relation.ReflTransGen (FlatAdj (G.induce K))
        ⟨P₁[i]'hi, hidx1 i hi⟩ ⟨P₁[j]'hj, hidx1 j hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro i hi hj hij
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro i hi hj hij
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        have hk : k < P₁.length := by omega
        refine Relation.ReflTransGen.tail (ih i hi hk hik) ?_
        refine flat1 ⟨P₁[k]'hk, hidx1 k hk⟩ ⟨P₁[k+1]'hj, hidx1 (k+1) hj⟩
          (List.getElem_mem hk) (List.getElem_mem hj) ?_
        exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hP₁.1 hk hj).mpr (Or.inl rfl)
      · obtain rfl : i = k + 1 := by omega
        exact Relation.ReflTransGen.refl
  have up2 : ∀ (j i : ℕ) (hi : i < P₂.length) (hj : j < P₂.length), i ≤ j →
      Relation.ReflTransGen (FlatAdj (G.induce K))
        ⟨P₂[i]'hi, hidx2 i hi⟩ ⟨P₂[j]'hj, hidx2 j hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro i hi hj hij
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro i hi hj hij
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        have hk : k < P₂.length := by omega
        refine Relation.ReflTransGen.tail (ih i hi hk hik) ?_
        refine flat2 ⟨P₂[k]'hk, hidx2 k hk⟩ ⟨P₂[k+1]'hj, hidx2 (k+1) hj⟩
          (List.getElem_mem hk) (List.getElem_mem hj) ?_
        exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hP₂.1 hk hj).mpr (Or.inl rfl)
      · obtain rfl : i = k + 1 := by omega
        exact Relation.ReflTransGen.refl
  have hsymm : Symmetric (FlatAdj (G.induce K)) := fun _ _ h => flatAdj_symm h
  refine ⟨?_, ?_, flatmem⟩
  · intro u v hu hv
    obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hv
    have hu' : u = ⟨P₁[i]'hi, hidx1 i hi⟩ := Subtype.ext hiu.symm
    have hv' : v = ⟨P₁[j]'hj, hidx1 j hj⟩ := Subtype.ext hjv.symm
    rw [hu', hv']
    rcases le_total i j with h | h
    · exact up1 j i hi hj h
    · exact Relation.ReflTransGen.symmetric hsymm (up1 i j hj hi h)
  · intro u v hu hv
    obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hv
    have hu' : u = ⟨P₂[i]'hi, hidx2 i hi⟩ := Subtype.ext hiu.symm
    have hv' : v = ⟨P₂[j]'hj, hidx2 j hj⟩ := Subtype.ext hjv.symm
    rw [hu', hv']
    rcases le_total i j with h | h
    · exact up2 j i hi hj h
    · exact Relation.ReflTransGen.symmetric hsymm (up2 i j hj hi h)

end Workspace.ProofLemmas.Thm92Branches
