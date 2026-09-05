import Workspace.ProofLemmas.Thm175Claim4Setup
import Workspace.ProofLemmas.Thm175Claim4CleanPaths
import Workspace.ProofLemmas.Thm175Claim4OtherComplete

/-! The choices of `p_b,p_c` and the optimality step in 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Selection

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Minimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- **17.5 (4), printed pp. 107--108.**
PAPER: "Choose `c` with `2≤c≤d` minimum such that `p_c` is `V`-complete.
Since `p₂` is nonadjacent to `x₁` it follows that `c≥3`. Since `p₁-⋯-p_c`
is between `V`-complete vertices and its internal vertices are not
`V`-complete and `z` has no neighbour in it, it is even by 2.2, and so `c`
is odd."
Here `V=X\{x_s}`. The returned index is zero-based. The existence of a
`V`-complete vertex uses 2.2 on `p₁-⋯-p_d-y₁`, as in the preceding sentence. -/
theorem gap_first_other_complete (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (ht0 : s.t₀ = 0) (h1 : 1 < c.core.p.length)
    (hp₂W : VertexComplete G (c.core.p[1]'h1) (wSet s)) :
    ∃ k, ∃ hk : k < c.core.p.length, 2 ≤ k ∧ Even k ∧
      VertexComplete G (c.core.p[k]'hk)
        (c.X \ {s.qX[s.qX.length - 1]'(by have := s.hXlong; omega)}) ∧
      ∀ i (hi : i < c.core.p.length), 0 < i → i < k →
        ¬ VertexComplete G (c.core.p[i]'hi)
          (c.X \ {s.qX[s.qX.length - 1]'(by have := s.hXlong; omega)}) := by
  exact Thm175Claim4OtherComplete.first_other_complete hG s hfirst ht0 h1 hp₂W

/-- PAPER: "If `c-b>1` then `p_b-⋯-p_c,W,V` is a counterexample ...
contradicting the optimality of `X,Y,P`. So `c=b+1`."
The finite maximum chooses `b`, and the shorter counterexample proves the
adjacency needed in the two-antihole argument. -/
theorem adjacent_completions (hG : InF7 G) (s : Setup c) (hopt : IsOptimal c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (ht0 : s.t₀ = 0) (h1 : 1 < c.core.p.length)
    (hp₂W : VertexComplete G (c.core.p[1]'h1) (wSet s))
    (hbound : ∀ i (hi : i < c.core.p.length),
      VertexComplete G (c.core.p[i]'hi) (wSet s) → i = 0 ∨ i = 1 ∨ i = 3) :
    ∃ u v, u ∈ c.core.p ∧ v ∈ c.core.p ∧ u ≠ c.core.p₁ ∧ v ≠ c.core.p₁ ∧
      G.Adj u v ∧ VertexComplete G u (wSet s) ∧
      VertexComplete G v (c.X \ {s.qX[s.qX.length - 1]'(by have := s.hXlong; omega)}) := by
  classical
  obtain ⟨k, hk, hk2, hkeven, hkV, hkfirst⟩ := gap_first_other_complete hG s hfirst ht0 h1 hp₂W
  have hknotW : ¬ VertexComplete G (c.core.p[k]'hk) (wSet s) := by
    intro hc
    have := hbound k hk hc
    rw [Nat.even_iff] at hkeven
    omega
  let S : Finset (Fin c.core.p.length) := Finset.univ.filter
    (fun i => i.val ≤ k ∧ VertexComplete G (c.core.p[i.val]'i.isLt) (wSet s))
  have h1S : (⟨1, h1⟩ : Fin c.core.p.length) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, hp₂W⟩
  obtain ⟨b, hbS, hbmax⟩ := Finset.exists_max_image S (fun i => i.val) ⟨_, h1S⟩
  have hbdata : b.val ≤ k ∧ VertexComplete G (c.core.p[b.val]'b.isLt) (wSet s) :=
    (Finset.mem_filter.mp hbS).2
  have hbpos : 0 < b.val := by have hh : 1 ≤ b.val := hbmax _ h1S; omega
  have hbk : b.val < k := by
    have hne : b.val ≠ k := by intro he; apply hknotW; simpa only [he] using hbdata.2
    omega
  have hbodd : Odd b.val := by
    have := hbound b.val b.isLt hbdata.2
    rw [Nat.odd_iff]
    omega
  have hmaxW : ∀ i (hi : i < c.core.p.length), i ≤ k →
      VertexComplete G (c.core.p[i]'hi) (wSet s) → i ≤ b.val := by
    intro i hi hik hc
    exact hbmax ⟨i, hi⟩ (by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hik, hc⟩)
  have hs := s.hXlong
  let xs := s.qX[s.qX.length - 1]'(by omega)
  let U := c.X \ {xs}
  have hW : wSet s = c.X \ {s.x₁} := by simp [wSet, ht0]
  have hqpath : IsPathList Gᶜ s.qX := by
    have ht := PathBasics.isPathList_take s.hanti.1 (k := s.qX.length) (by omega)
    simpa using ht
  have hq : IsAntipathFrom G s.qX s.x₁ xs := by
    refine ⟨hqpath, s.hxhead, ?_⟩
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hxne : s.x₁ ≠ xs := PathBasics.isPathFrom_ends_ne hq (by dsimp [pathLength]; omega)
  have hUlist : U = {v | v ∈ s.qX.dropLast} := by
    ext v
    change (v ∈ c.X ∧ v ≠ xs) ↔ v ∈ s.qX.dropLast
    rw [PathBasics.mem_dropLast_iff hqpath.2.1 hqpath.1]
    rw [s.hXverts]
    have he : s.qX.getLast hqpath.1 = xs := by simp [xs, List.getLast_eq_getElem]
    rw [he]
  have hUa : AnticonnectedSet G U := by
    rw [hUlist, List.dropLast_eq_take]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_take hqpath (by omega))
  have hWU : wSet s ∪ U = c.X := by
    rw [hW]
    ext v
    constructor
    · rintro (hv | hv)
      · exact hv.1
      · exact hv.1
    · intro hv
      by_cases he : v = s.x₁
      · right
        exact ⟨hv, fun hx => hxne (he.symm.trans hx)⟩
      · exact Or.inl ⟨hv, he⟩
  let Q := (c.core.p.drop b.val).take (k - b.val + 1)
  have hQ := PathBasics.isPathFrom_slice c.core.hp.1 hbk hk
  have hQlen : Q.length = k - b.val + 1 := PathBasics.length_slice c.core.p (by omega) hk
  have hQsub : ∀ v ∈ Q, v ∈ c.core.p := fun v hv =>
    List.drop_subset _ _ (List.take_subset _ _ hv)
  have hQW : ∀ v ∈ Q, VertexComplete G v (wSet s) ↔ v = c.core.p[b.val]'b.isLt := by
    intro v hv
    constructor
    · intro hc
      obtain ⟨i, hi, hbi, hik, hiv⟩ := (PathBasics.mem_slice_iff c.core.p (by omega) hk).mp hv
      have him := hmaxW i hi hik (hiv ▸ hc)
      have he : i = b.val := by omega
      subst i
      exact hiv.symm
    · rintro rfl
      exact hbdata.2
  have hQU : ∀ v ∈ Q, VertexComplete G v U ↔ v = c.core.p[k]'hk := by
    intro v hv
    constructor
    · intro hc
      obtain ⟨i, hi, hbi, hik, hiv⟩ := (PathBasics.mem_slice_iff c.core.p (by omega) hk).mp hv
      have he : i = k := by
        by_contra hne
        exact hkfirst i hi (by omega) (by omega) (hiv ▸ hc)
      subst i
      exact hiv.symm
    · rintro rfl
      exact hkV
  have hdiff : k - b.val = 1 := by
    by_contra hne
    have hlong : 1 < pathLength Q := by rw [pathLength, hQlen]; omega
    have hodd : Odd (pathLength Q) := by
      rw [pathLength, hQlen, Nat.odd_iff]
      rw [Nat.even_iff] at hkeven
      rw [Nat.odd_iff] at hbodd
      omega
    have hE : edges G (wSet s) Q = ∅ := by
      ext e
      constructor
      · rintro ⟨v, hv, w, hw, he, ha, hvC, hwC⟩
        rw [(hQW v hv).mp hvC, (hQW w hw).mp hwC] at ha
        exact (G.irrefl ha).elim
      · simp
    let cc : Counterexample G z :=
      { X := wSet s
        Y := U
        core :=
          { p := Q
            p₁ := c.core.p[b.val]'b.isLt
            pₙ := c.core.p[k]'hk
            hp := hQ
            hodd := hodd
            hlong := hlong
            houtX := fun v hv => p_out_wSet s v (hQsub v hv)
            houtY := fun v hv hu => c.core.houtX v (hQsub v hv) hu.1
            hp₁X := hbdata.2
            hYuniq := hQU
            hzP := fun hz => c.core.hzP (hQsub z hz)
            hzanti := fun v hv => c.core.hzanti v (hQsub v hv)
            heven := by change Even (edges G (wSet s) Q).ncard; rw [hE]; simp }
        hXa := wSet_anticonnected s
        hYa := hUa
        hXYa := by rw [hWU]; exact c.hXa
        hz := by rw [hWU]; exact fun hz => c.hz (Or.inl hz)
        hzXY := by rw [hWU]; exact fun v hv => c.hzXY v (Or.inl hv) }
    apply hopt.1 cc
    change Q.length < c.core.p.length
    rw [hQlen]
    omega
  have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (show 0 < c.core.p.length by omega)
  refine ⟨_, _, List.getElem_mem b.isLt, List.getElem_mem hk, ?_, ?_, ?_, hbdata.2, hkV⟩
  · intro he
    have := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hp0.symm)
    omega
  · intro he
    have := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hp0.symm)
    omega
  · exact (PathBasics.path_adj_iff c.core.hp.1 b.isLt hk).mpr (Or.inl (by omega))

end Workspace.ProofLemmas.Thm175Claim4Selection
