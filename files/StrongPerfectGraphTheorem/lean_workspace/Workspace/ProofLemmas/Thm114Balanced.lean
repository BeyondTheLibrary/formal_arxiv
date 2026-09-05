/-  Carve-outs for statement 11.4 (`Workspace.Statements.S11.SPGT.thm_11_4`).

    Two pieces of §2 machinery, in the exact shape the proof of 11.4 consumes them.

    1.  `balanced_of_complete_star` is step (2) of the printed proof:

          *"For `b₁ ∈ B₁` is complete to `{b₀, q₁, …, qₙ}` from the minimality of `n`.  But
          `b₁` has no neighbour in `F`, so by 2.6, `(F, {b₀, q₁, …, qₙ})` is balanced.  Since
          `F` is connected and every vertex in `{b₀, q₁, …, qₙ}` has a neighbour in `F`, the
          claim follows from 2.7.1."*

        Stated with `F` renamed to `F`, `{b₀, q₁, …, qₙ}` to `X`, `A ∪ B ∪ C` to `S` and `b₁`
        to `v`, this is literally 2.6 followed by the first half of 2.7.

    2.  `not_leap_of_balanced_path` is the standing way the paper discards the *leap*
        alternative of the Roussel–Rubio lemma 2.1: a leap `a, b` for an odd path `p` whose
        interior lies in `S` produces an odd path from `a` to `b` (namely `a` followed by the
        interior of `p` followed by `b`) between nonadjacent vertices of `X` with interior in
        `S`, which the first clause of `Balanced G S X` forbids.

        `Workspace.ProofLemmas.BalancedNoLeap.not_leap_of_balanced` is the same argument for a
        leap for a *hole*; the private lemma inside that file that does the path-level work is
        not exported, so it is restated here.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_7

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm114Balanced

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Step (2) of the printed proof of 11.4**, in general form.

`F` is connected and anticomplete to `S`, every vertex of `X` has a neighbour in `F`, and some
vertex `v ∈ S` is `X`-complete and `F`-anticomplete.  Then `(S, X)` is balanced: 2.6 gives
that `(F, X)` is balanced, and 2.7.1 transports it across `F` to `S`. -/
theorem balanced_of_complete_star {G : SimpleGraph V} (hG : Berge G) (S F X : Set V)
    (hFconn : ConnectedSet G F)
    (hFS : Anticomplete G F S)
    (hSFX : S ⊆ (F ∪ X)ᶜ)
    (hFX : Disjoint F X)
    (hXnbr : ∀ x ∈ X, ∃ f ∈ F, G.Adj x f)
    (v : V) (hvFX : v ∉ F ∪ X)
    (hvX : VertexComplete G v X) (hvF : VertexAnticomplete G v F) :
    Balanced G S X := by
  have h1 : Balanced G F X :=
    Workspace.Statements.S02.SPGT.thm_2_6 G hG F X hFX v hvFX hvX hvF
  exact (Workspace.Statements.S02.SPGT.thm_2_7 G hG F X h1 S hSFX).1 hFconn hXnbr hFS

/-- **A balanced pair admits no leap for an odd path.**

If `(S, X)` is balanced, `p` is an odd path whose interior lies in `S` and none of whose
vertices lies in `X`, then no two vertices `a, b ∈ X` form a leap for `p`. -/
theorem not_leap_of_balanced_path {G : SimpleGraph V} {p : List V} {S X : Set V}
    (hbal : Balanced G S X)
    (hint : ∀ w ∈ SPGT.interior p, w ∈ S)
    (hpX : ∀ w ∈ p, w ∉ X)
    (hodd : Odd (pathLength p))
    {a b : V} (ha : a ∈ X) (hb : b ∈ X)
    (hleap : IsLeapForPath G p a b) : False := by
  classical
  obtain ⟨hp, hlen, hab, hnab, hA, hB⟩ := hleap
  have hp3 : 3 ≤ p.length := by
    rw [pathLength] at hlen
    omega
  have haP : a ∉ p := fun h => hpX a h ha
  have hbP : b ∉ p := fun h => hpX b h hb
  let M := (p.drop 1).take (p.length - 2)
  have hMlen : M.length = p.length - 2 := by
    simp [M, List.length_take, List.length_drop]
    omega
  have hidx : p.length - 2 - 1 + 1 = p.length - 2 := by omega
  have hMpath : IsPathList G M := by
    dsimp [M]
    exact Workspace.ProofLemmas.PathBasics.isPathList_take
      (Workspace.ProofLemmas.PathBasics.isPathList_drop hp (k := 1) (by omega)) (by omega)
  have hMhead : M.head? = some (p[1]'(by omega)) := by
    dsimp [M]
    have h := Workspace.ProofLemmas.PathBasics.head?_slice p
      (i := 1) (j := p.length - 2) (by omega) (by omega)
    rwa [hidx] at h
  have hMlast : M.getLast? = some (p[p.length - 2]'(by omega)) := by
    dsimp [M]
    have h := Workspace.ProofLemmas.PathBasics.getLast?_slice p
      (i := 1) (j := p.length - 2) (by omega) (by omega)
    rwa [hidx] at h
  have hMmem : ∀ x : V, x ∈ M ↔
      ∃ (k : ℕ) (hk : k < p.length), 1 ≤ k ∧ k ≤ p.length - 2 ∧ p[k]'hk = x := by
    intro x
    dsimp [M]
    have h := Workspace.ProofLemmas.PathBasics.mem_slice_iff p
      (i := 1) (j := p.length - 2) (x := x) (by omega) (by omega)
    rwa [hidx] at h
  have hMfrom : IsPathFrom G M (p[1]'(by omega)) (p[p.length - 2]'(by omega)) :=
    ⟨hMpath, hMhead, hMlast⟩
  have haM : a ∉ M := fun hm => haP (by
    obtain ⟨k, hk, -, -, rfl⟩ := (hMmem a).mp hm
    exact List.getElem_mem hk)
  have hbM : b ∉ M := fun hm => hbP (by
    obtain ⟨k, hk, -, -, rfl⟩ := (hMmem b).mp hm
    exact List.getElem_mem hk)
  have ha1 : G.Adj a (p[1]'(by omega)) := (hA 1 (by omega)).2 (Or.inr (Or.inl rfl))
  have hb1 : G.Adj b (p[p.length - 2]'(by omega)) :=
    (hB (p.length - 2) (by omega)).2 (Or.inr (Or.inl rfl))
  have haother : ∀ x ∈ M, x ≠ p[1]'(by omega) → ¬ G.Adj a x := by
    intro x hx hne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hMmem x).mp hx
    have hk := (hA k hk).1 hadj
    have : k = 1 := by omega
    exact hne (hp.2.1.getElem_inj_iff.2 this)
  have hbother : ∀ x ∈ M, x ≠ p[p.length - 2]'(by omega) → ¬ G.Adj b x := by
    intro x hx hne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hMmem x).mp hx
    have hk := (hB k hk).1 hadj
    have : k = p.length - 2 := by omega
    exact hne (hp.2.1.getElem_inj_iff.2 this)
  let R := a :: (M ++ [b])
  have hR : IsPathFrom G R a b := by
    dsimp [R]
    exact Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hMfrom ha1 hb1 hnab hab
      haM hbM haother hbother
  have hRlen : pathLength R = pathLength p := by
    dsimp [R]
    rw [Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton,
      hMlen]
    simp only [pathLength]
    omega
  have hRint : ∀ x ∈ SPGT.interior R, x ∈ S := by
    intro x hx
    have hx' := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR).1 hx
    rcases Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton.mp hx'.1 with
      hxa | hxM | hxb
    · exact absurd hxa hx'.2.1
    · obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hMmem x).mp hxM
      exact hint _ (Workspace.ProofLemmas.PathBasics.getElem_mem_interior hp hk hk1 (by omega))
    · exact absurd hxb hx'.2.2
  exact hbal.1 a b R ha hb hnab hR hRint (hRlen ▸ hodd)

end Workspace.ProofLemmas.Thm114Balanced
