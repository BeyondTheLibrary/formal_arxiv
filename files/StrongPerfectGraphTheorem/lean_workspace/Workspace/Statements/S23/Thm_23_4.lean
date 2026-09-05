/-  Proof attempt for 23.4.  Statement frozen from
    Workspace/Statements/S23/Thm_23_4.lean.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.LongOddPrism
import Workspace.Statements.S15.Thm_15_1
import Workspace.Statements.S23.Thm_23_3
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.SkewPartitionFromSeparator
import Workspace.ProofLemmas.ExtremalChoice

/-!
# Section 23 — The end of wheels

The six numbered statements 23.1 … 23.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem*.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S23

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Small generic helpers -/

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {α : Type*} (q : List α) {p r : ℕ} (h : p = r)
    (hp : p < q.length) (hr : r < q.length) : q[p]'hp = q[r]'hr := by
  subst h; rfl

private theorem mem_drop_iff' {α : Type*} (l : List α) (k : ℕ) (b : α) :
    b ∈ l.drop k ↔ ∃ i, ∃ h : i < l.length, k ≤ i ∧ l[i]'h = b := by
  constructor
  · intro hb
    obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hb
    rw [List.length_drop] at hi
    refine ⟨k + i, by omega, by omega, ?_⟩
    rw [← hib, List.getElem_drop]
  · rintro ⟨i, hi, hki, rfl⟩
    have hlt : i - k < (l.drop k).length := by rw [List.length_drop]; omega
    have heq : (l.drop k)[i - k]'hlt = l[i]'hi := by
      rw [List.getElem_drop]
      exact gidx l (by omega) _ _
    rw [← heq]
    exact List.getElem_mem hlt

/-- `VertexComplete` against `Xᵢ = {x₀,…,xᵢ}`, unfolded. -/
private theorem vc_wheelSystemX {G : SimpleGraph V} {q : V} {x : ℕ → V} {t : ℕ} :
    VertexComplete G q (wheelSystemX x t) ↔ ∀ j, j ≤ t → G.Adj q (x j) := by
  constructor
  · intro h j hj; exact h _ ⟨j, hj, rfl⟩
  · rintro h v ⟨j, hj, rfl⟩; exact h j hj

private theorem mem_wheelSystemX {x : ℕ → V} {t j : ℕ} (hj : j ≤ t) :
    x j ∈ wheelSystemX x t := ⟨j, hj, rfl⟩

/-! ### The family of sequences of the printed proof of 23.4

PAPER: *"Choose `t` maximum such that there is a sequence `x₂,…,x_t` with the following
properties: • for `2 ≤ i ≤ t`, there is a connected subset `A_{i−1}` of `V(G)` including
`A_{i−2}`, containing a neighbour of `xᵢ`, containing no neighbour of `z` or `y`, and
containing no `{x₀,…,x_{i−1}}`-complete vertex, • for `1 ≤ i ≤ t`, `xᵢ` is not
`{x₀,…,x_{i−1}}`-complete, and • `x₀,…,x_t` are `{y,z}`-complete."*

Note that the printed conditions are **symmetric in `z` and `y`** (the connected sets avoid
the neighbours of *both*); that symmetry is exactly the paper's *"From the symmetry between
`z, y` we may assume its first vertex is `y`"*.  It is recorded here by `goodSeq_swap`. -/
private def GoodSeq (G : SimpleGraph V) (z y : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) : Prop :=
  1 ≤ t ∧
  (∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k) ∧
  (∀ j ≤ t, x j ∉ A₀ ∧ x j ≠ z ∧ x j ≠ y) ∧
  ((∃ b ∈ A₀, G.Adj (x 0) b) ∧ (∃ b ∈ A₀, G.Adj (x 1) b) ∧
    ∀ b ∈ A₀, ¬ VertexComplete G b ({x 0, x 1} : Set V)) ∧
  (∀ i, 2 ≤ i → i ≤ t →
    ∃ B : Set V, A₀ ⊆ B ∧ ConnectedSet G B ∧ (∃ b ∈ B, G.Adj (x i) b) ∧
      (∀ b ∈ B, ¬ G.Adj z b) ∧ (∀ b ∈ B, ¬ G.Adj y b) ∧
      (∀ b ∈ B, ¬ VertexComplete G b (wheelSystemX x (i - 1)))) ∧
  (∀ i, 1 ≤ i → i ≤ t → ¬ VertexComplete G (x i) (wheelSystemX x (i - 1))) ∧
  (∀ j ≤ t, G.Adj z (x j)) ∧ (∀ j ≤ t, G.Adj y (x j))

private theorem goodSeq_swap {G : SimpleGraph V} {z y : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (h : GoodSeq G z y A₀ x t) : GoodSeq G y z A₀ x t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, fun j hj => ⟨(h3 j hj).1, (h3 j hj).2.2, (h3 j hj).2.1⟩, h4, ?_, h6, h8, h7⟩
  intro i hi hit
  obtain ⟨B, hB1, hB2, hB3, hB4, hB5, hB6⟩ := h5 i hi hit
  exact ⟨B, hB1, hB2, hB3, hB5, hB4, hB6⟩

/-- A `GoodSeq` is in particular a wheel system with respect to the frame `(z, A₀)`. -/
private theorem isWheelSystem_of_goodSeq {G : SimpleGraph V} {z y : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : GoodSeq G z y A₀ x t) : IsWheelSystem G z A₀ x t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, fun j hj => ⟨(h3 j hj).1, (h3 j hj).2.1⟩, h4, ?_, h6, h7⟩
  intro i hi hit
  obtain ⟨B, hB1, hB2, hB3, hB4, hB5, hB6⟩ := h5 i hi hit
  exact ⟨B, hB1, hB2, hB3, hB4, hB6⟩

/-! ### The endgame of the printed proof

*"From the minimality of the length of `P` it follows that `z` is not adjacent to any of
`p₂,…,p_k`.  If `z` is adjacent to `p₁` then we may set `x_{t+1} = p₁`, contrary to the
maximality of `t`.  So `p₁,…,p_{k+1}` are all nonadjacent to `z`.  Hence `(z,A₀)` is a frame,
and `x₀,…,x_t` is a wheel system with respect to it, and `y` is adjacent to all of
`z, x₀,…,x_t`, and there is a connected subset of `V(G)` including `A₀`, containing a
neighbour of `y`, containing no neighbour of `z`, and containing no `{x₀,…,x_t}`-complete
vertex.  But this contradicts 23.3."*

`u` is the paper's `y` (the first vertex of the minimum-length path `P`) and `w` is the
paper's `z`; the hypotheses are stated so that either assignment of `{z,y}` to `(u,w)` may be
supplied — that is the paper's symmetry. -/
private theorem endgame {G : SimpleGraph V} (hG : InF9 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    {u w : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ} {P : List V} {a : V}
    (hA₀ne : A₀.Nonempty) (hA₀conn : ConnectedSet G A₀)
    (huA₀ : u ∉ A₀) (hwA₀ : w ∉ A₀)
    (hunbr : ∀ b ∈ A₀, ¬ G.Adj u b) (hwnbr : ∀ b ∈ A₀, ¬ G.Adj w b)
    (huw : G.Adj u w)
    (hgood : GoodSeq G u w A₀ x t)
    (hmaxt : ∀ x' : ℕ → V, ¬ GoodSeq G u w A₀ x' (t + 1))
    (ha : a ∈ A₀) (hP : IsPathFrom G P u a)
    (hPX : ∀ s ∈ P, s ∉ wheelSystemX x t)
    (hPint : ∀ s ∈ SPGT.interior P, ¬ VertexComplete G s (wheelSystemX x t))
    (hmin : ∀ (Q : List V) (q b : V), (q = u ∨ q = w) → b ∈ A₀ → IsPathFrom G Q q b →
      (∀ s ∈ Q, s ∉ wheelSystemX x t) →
      (∀ s ∈ SPGT.interior Q, ¬ VertexComplete G s (wheelSystemX x t)) →
      P.length ≤ Q.length) :
    False := by
  classical
  obtain ⟨ht1, hinj, hnot, hcond1, hcond2, hcond3, hux, hwx⟩ := hgood
  -- basic facts about `X = {x₀,…,x_t}`
  have huXc : VertexComplete G u (wheelSystemX x t) := vc_wheelSystemX.mpr hux
  have hwXc : VertexComplete G w (wheelSystemX x t) := vc_wheelSystemX.mpr hwx
  have hA₀X : ∀ b ∈ A₀, ¬ VertexComplete G b (wheelSystemX x t) := by
    intro b hb hc
    refine hcond1.2.2 b hb ?_
    rintro v (rfl | rfl)
    · exact hc _ (mem_wheelSystemX (Nat.zero_le t))
    · exact hc _ (mem_wheelSystemX ht1)
  -- the shape of `P`
  set n := P.length with hn
  have hn0 : 0 < n := PathBasics.path_length_pos hP.1
  have hP0 : P[0]'hn0 = u := PathBasics.getElem_zero_of_head? hP.2.1 hn0
  have hPl : P[n - 1]'(by omega) = a := PathBasics.getElem_last_of_getLast? hP.2.2 hn0
  have hn2 : 2 ≤ n := by
    by_contra hc
    have hn1 : n = 1 := by omega
    have : u = a := by rw [← hP0, ← hPl]; exact gidx P (by omega) _ _
    exact huA₀ (this ▸ ha)
  have hn3 : 3 ≤ n := by
    by_contra hc
    have hn2' : n = 2 := by omega
    have hadj : G.Adj (P[0]'hn0) (P[1]'(by omega)) := PathBasics.path_adj_succ hP.1 (by omega)
    rw [hP0] at hadj
    refine hunbr a ha ?_
    have : (P[1]'(by omega)) = a := by rw [← hPl]; exact gidx P (by omega) _ _
    rwa [this] at hadj
  have h1n : 1 < n := by omega
  -- **the minimality claim**: neither end is adjacent to `p₂,…,p_{k+1}`
  have claim : ∀ q : V, (q = u ∨ q = w) → ∀ i, ∀ hi : i < n, 2 ≤ i → ¬ G.Adj q (P[i]'hi) := by
    intro q hq i hi h2i hadj
    have hqXc : VertexComplete G q (wheelSystemX x t) := by
      rcases hq with rfl | rfl
      · exact huXc
      · exact hwXc
    have hqnbr : ∀ b ∈ A₀, ¬ G.Adj q b := by
      rcases hq with rfl | rfl
      · exact hunbr
      · exact hwnbr
    have hqA₀ : q ∉ A₀ := by
      rcases hq with rfl | rfl
      · exact huA₀
      · exact hwA₀
    -- the largest index of `P` adjacent to `q`
    set pr : ℕ → Prop := fun j => ∃ h : j < n, 2 ≤ j ∧ G.Adj q (P[j]'h) with hprdef
    have hpri : pr i := ⟨hi, h2i, hadj⟩
    have hJspec : pr (Nat.findGreatest pr (n - 1)) :=
      Nat.findGreatest_spec (m := i) (by omega) hpri
    set J := Nat.findGreatest pr (n - 1) with hJdef
    obtain ⟨hJn, hJ2, hJadj⟩ := hJspec
    have hJle : J ≤ n - 1 := Nat.findGreatest_le _
    have hJgt : ∀ m, J < m → m ≤ n - 1 → ¬ pr m := fun m h1 h2 =>
      Nat.findGreatest_is_greatest h1 h2
    have hJne : J ≠ n - 1 := by
      intro hc
      refine hqnbr a ha ?_
      have : (P[J]'hJn) = a := by rw [← hPl]; exact gidx P hc _ _
      rwa [this] at hJadj
    have hJlt : J < n - 1 := by omega
    -- the vertices of `P` from position `J` on
    have hdropmem : ∀ s ∈ P.drop J, ∃ i, ∃ h : i < n, J ≤ i ∧ P[i]'h = s := by
      intro s hs
      exact (mem_drop_iff' P J s).mp hs
    have hdropX : ∀ s ∈ P.drop J, ¬ VertexComplete G s (wheelSystemX x t) := by
      intro s hs
      obtain ⟨i', hi', hJi', rfl⟩ := hdropmem s hs
      by_cases hlast : i' = n - 1
      · have : (P[i']'hi') = a := by rw [← hPl]; exact gidx P hlast _ _
        rw [this]; exact hA₀X a ha
      · exact hPint _ (PathBasics.getElem_mem_interior hP.1 hi' (by omega) (by omega))
    have hqnotmem : q ∉ P.drop J := by
      intro hs
      obtain ⟨i', hi', hJi', hval⟩ := hdropmem q hs
      exact hdropX q hs (hval ▸ hqXc)
    have hother : ∀ s ∈ P.drop J, s ≠ P[J]'hJn → ¬ G.Adj q s := by
      intro s hs hsne
      obtain ⟨i', hi', hJi', rfl⟩ := hdropmem s hs
      have hi'J : i' ≠ J := by
        intro hc; exact hsne (gidx P hc _ _)
      by_cases hlast : i' = n - 1
      · have : (P[i']'hi') = a := by rw [← hPl]; exact gidx P hlast _ _
        rw [this]; exact hqnbr a ha
      · intro hcontra
        exact hJgt i' (by omega) (by omega) ⟨hi', by omega, hcontra⟩
    -- the shorter path `q-p_J-⋯-p_{k+1}`
    have hslice := PathBasics.isPathFrom_slice hP.1 hJlt (show n - 1 < n by omega)
    have hlen : ((P.drop J).take (n - 1 - J + 1)) = P.drop J := by
      refine List.take_of_length_le ?_
      rw [List.length_drop]; omega
    rw [hlen, hPl] at hslice
    have hQ : IsPathFrom G (q :: P.drop J) q a :=
      PathAttach.isPathFrom_cons hslice hJadj hqnotmem hother
    have hQX : ∀ s ∈ q :: P.drop J, s ∉ wheelSystemX x t := by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact fun hc => G.irrefl (hqXc s hc)
      · exact hPX s (List.mem_of_mem_drop hs)
    have hQint : ∀ s ∈ SPGT.interior (q :: P.drop J),
        ¬ VertexComplete G s (wheelSystemX x t) := by
      intro s hs
      rw [PathBasics.mem_interior_iff_of_pathFrom hQ] at hs
      obtain ⟨hs1, hs2, hs3⟩ := hs
      rcases List.mem_cons.mp hs1 with rfl | hs1
      · exact absurd rfl hs2
      · exact hdropX s hs1
    have hle := hmin (q :: P.drop J) q a hq ha hQ hQX hQint
    simp only [List.length_cons, List.length_drop] at hle
    omega
  -- `w` is not adjacent to `p₁` either: else `x_{t+1} = p₁` extends the sequence
  set p1 : V := P[1]'h1n with hp1def
  have hup1 : G.Adj u p1 := by
    have h : G.Adj (P[0]'hn0) (P[1]'h1n) :=
      (PathBasics.path_adj_iff hP.1 hn0 h1n).mpr (Or.inl rfl)
    rw [hP0] at h
    rw [hp1def]
    exact h
  have hp1int : p1 ∈ SPGT.interior P :=
    PathBasics.getElem_mem_interior hP.1 h1n (le_refl 1) (by omega)
  have hp1X : ¬ VertexComplete G p1 (wheelSystemX x t) := hPint _ hp1int
  have hp1notX : p1 ∉ wheelSystemX x t := hPX _ (List.getElem_mem h1n)
  have hp1A₀ : p1 ∉ A₀ := fun hc => hunbr p1 hc hup1
  have hp1u : p1 ≠ u := fun hc => hp1X (hc ▸ huXc)
  have hp1w : p1 ≠ w := fun hc => hp1X (hc ▸ hwXc)
  -- the sets used both for the extension and for the final contradiction
  have hchain : ∀ k : ℕ, k < n → ConnectedSet G {s : V | s ∈ P.drop k} := by
    intro k hk
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain
      (InducedPathExtraction.isChain_of_isPathList (PathBasics.isPathList_drop hP.1 hk))
  have hamem : ∀ k : ℕ, k ≤ n - 1 → a ∈ {s : V | s ∈ P.drop k} := by
    intro k hk
    exact (mem_drop_iff' P k a).mpr ⟨n - 1, by omega, hk, hPl⟩
  have hdropXgen : ∀ k : ℕ, 1 ≤ k →
      ∀ s ∈ P.drop k, ¬ VertexComplete G s (wheelSystemX x t) := by
    intro k hk s hs
    obtain ⟨i', hi', hki', rfl⟩ := (mem_drop_iff' P k s).mp hs
    by_cases hlast : i' = n - 1
    · have : (P[i']'hi') = a := by rw [← hPl]; exact gidx P hlast _ _
      rw [this]; exact hA₀X a ha
    · exact hPint _ (PathBasics.getElem_mem_interior hP.1 hi' (by omega) (by omega))
  have hwp1 : ¬ G.Adj w p1 := by
    intro hwadj
    -- the extended sequence
    set x' : ℕ → V := fun j => if j = t + 1 then p1 else x j with hx'def
    have hx'le : ∀ j, j ≤ t → x' j = x j := by
      intro j hj; rw [hx'def]; exact if_neg (by omega)
    have hx'top : x' (t + 1) = p1 := by rw [hx'def]; exact if_pos rfl
    have hXeq : ∀ i, i ≤ t → wheelSystemX x' i = wheelSystemX x i := by
      intro i hi
      ext v
      constructor
      · rintro ⟨j, hj, hv⟩
        exact ⟨j, hj, by rw [hv]; exact hx'le j (by omega)⟩
      · rintro ⟨j, hj, hv⟩
        exact ⟨j, hj, by rw [hv]; exact (hx'le j (by omega)).symm⟩
    -- the connected set witnessing condition 2 at the new index
    have hB2 : ∃ B : Set V, A₀ ⊆ B ∧ ConnectedSet G B ∧ (∃ b ∈ B, G.Adj (x' (t + 1)) b) ∧
        (∀ b ∈ B, ¬ G.Adj u b) ∧ (∀ b ∈ B, ¬ G.Adj w b) ∧
        (∀ b ∈ B, ¬ VertexComplete G b (wheelSystemX x' (t + 1 - 1))) := by
      refine ⟨A₀ ∪ {s : V | s ∈ P.drop 2}, Set.subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
      · exact ConnectedSetUnionAttach.connectedSet_union hA₀conn (hchain 2 (by omega))
          (Or.inl ⟨a, ha, hamem 2 (by omega)⟩)
      · refine ⟨P[2]'(by omega), Or.inr ((mem_drop_iff' P 2 _).mpr ⟨2, by omega, le_refl 2, rfl⟩),
          ?_⟩
        rw [hx'top, hp1def]
        have := PathBasics.path_adj_succ hP.1 (show 1 + 1 < n by omega)
        exact this
      · rintro b (hb | hb)
        · exact hunbr b hb
        · obtain ⟨i', hi', h2i', rfl⟩ := (mem_drop_iff' P 2 b).mp hb
          exact claim u (Or.inl rfl) i' hi' h2i'
      · rintro b (hb | hb)
        · exact hwnbr b hb
        · obtain ⟨i', hi', h2i', rfl⟩ := (mem_drop_iff' P 2 b).mp hb
          exact claim w (Or.inr rfl) i' hi' h2i'
      · rw [show t + 1 - 1 = t from rfl, hXeq t (le_refl t)]
        rintro b (hb | hb)
        · exact hA₀X b hb
        · exact hdropXgen 2 (by omega) b hb
    refine hmaxt x' ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- injectivity
      intro j hj k hk hjk
      by_cases hj' : j = t + 1 <;> by_cases hk' : k = t + 1
      · omega
      · exfalso
        rw [hj', hx'top, hx'le k (by omega)] at hjk
        exact hp1notX (hjk ▸ mem_wheelSystemX (show k ≤ t by omega))
      · exfalso
        rw [hk', hx'top, hx'le j (by omega)] at hjk
        exact hp1notX (hjk.symm ▸ mem_wheelSystemX (show j ≤ t by omega))
      · rw [hx'le j (by omega), hx'le k (by omega)] at hjk
        exact hinj j (by omega) k (by omega) hjk
    · -- the new vertices avoid `A₀`, `u`, `w`
      intro j hj
      by_cases hj' : j = t + 1
      · rw [hj', hx'top]; exact ⟨hp1A₀, hp1u, hp1w⟩
      · rw [hx'le j (by omega)]; exact hnot j (by omega)
    · -- condition 1 is untouched
      rw [hx'le 0 (by omega), hx'le 1 (by omega)]; exact hcond1
    · -- condition 2
      intro i hi hit
      by_cases hi' : i = t + 1
      · subst hi'; exact hB2
      · obtain ⟨B, hB1, hBc, hBn, hBz, hBy, hBX⟩ := hcond2 i hi (by omega)
        refine ⟨B, hB1, hBc, ?_, hBz, hBy, ?_⟩
        · rw [hx'le i (by omega)]; exact hBn
        · rw [hXeq (i - 1) (by omega)]; exact hBX
    · -- condition 3
      intro i hi hit
      by_cases hi' : i = t + 1
      · subst hi'
        rw [hx'top, show t + 1 - 1 = t from rfl, hXeq t (le_refl t)]
        exact hp1X
      · rw [hx'le i (by omega), hXeq (i - 1) (by omega)]
        exact hcond3 i hi (by omega)
    · -- `u` is adjacent to all of them
      intro j hj
      by_cases hj' : j = t + 1
      · rw [hj', hx'top]; exact hup1
      · rw [hx'le j (by omega)]; exact hux j (by omega)
    · -- `w` is adjacent to all of them
      intro j hj
      by_cases hj' : j = t + 1
      · rw [hj', hx'top]; exact hwadj
      · rw [hx'le j (by omega)]; exact hwx j (by omega)
  -- **the final contradiction with 23.3**
  have hframeW : IsFrame G w A₀ := ⟨hA₀ne, hA₀conn, hwA₀, hwnbr⟩
  have hwsW : IsWheelSystem G w A₀ x t :=
    isWheelSystem_of_goodSeq (goodSeq_swap ⟨ht1, hinj, hnot, hcond1, hcond2, hcond3, hux, hwx⟩)
  have hBmem : (A₀ ∪ {s : V | s ∈ P.drop 1}) ∈
      {A : Set V | A₀ ⊆ A ∧ ConnectedSet G A ∧ (∀ v ∈ A, ¬ G.Adj w v) ∧
        (∀ v ∈ A, ¬ VertexComplete G v (wheelSystemX x t))} := by
    refine ⟨Set.subset_union_left, ?_, ?_, ?_⟩
    · exact ConnectedSetUnionAttach.connectedSet_union hA₀conn (hchain 1 (by omega))
        (Or.inl ⟨a, ha, hamem 1 (by omega)⟩)
    · rintro b (hb | hb)
      · exact hwnbr b hb
      · obtain ⟨i', hi', h1i', rfl⟩ := (mem_drop_iff' P 1 b).mp hb
        by_cases hone : i' = 1
        · have : (P[i']'hi') = p1 := by rw [hp1def]; exact gidx P hone _ _
          rw [this]; exact hwp1
        · exact claim w (Or.inr rfl) i' hi' (by omega)
    · rintro b (hb | hb)
      · exact hA₀X b hb
      · exact hdropXgen 1 (by omega) b hb
  have hBsub : (A₀ ∪ {s : V | s ∈ P.drop 1}) ⊆ wheelSystemA G w A₀ x t :=
    Set.subset_sUnion_of_mem hBmem
  refine thm_23_3 G hG hbsp w A₀ hframeW x t hwsW ⟨u, ?_, ?_, ?_⟩
  · rintro (hc | hc)
    · exact G.irrefl (hc ▸ huw)
    · exact G.irrefl (huXc u hc)
  · rintro v (rfl | hv)
    · exact huw
    · exact huXc v hv
  · refine ⟨p1, hBsub (Or.inr ((mem_drop_iff' P 1 p1).mpr ⟨1, h1n, le_refl 1, rfl⟩)), hup1⟩

/-! ### The core of the printed proof of 23.4 -/

/-- The whole printed argument, with the hole already stripped away: `(z, A₀)` is the frame
`A₀ = V(C) \ {z, x₀, x₁}` of the printed proof, `x₀, z, x₁` is the printed path in `C`, and
`y` is the printed vertex with three consecutive neighbours.  The hypotheses are exactly
those the hole supplies. -/
private theorem core {G : SimpleGraph V} (hG : InF9 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    {z y x₀ x₁ : V} {A₀ : Set V}
    (hA₀ne : A₀.Nonempty) (hA₀conn : ConnectedSet G A₀)
    (hzA₀ : z ∉ A₀) (hyA₀ : y ∉ A₀)
    (hznbr : ∀ b ∈ A₀, ¬ G.Adj z b)
    (hzy : G.Adj z y)
    (hx₀A₀ : ∃ b ∈ A₀, G.Adj x₀ b) (hx₁A₀ : ∃ b ∈ A₀, G.Adj x₁ b)
    (hA₀nc : ∀ b ∈ A₀, ¬ VertexComplete G b ({x₀, x₁} : Set V))
    (hx₀x₁ : x₀ ≠ x₁) (hnadj01 : ¬ G.Adj x₁ x₀)
    (hx₀A : x₀ ∉ A₀) (hx₁A : x₁ ∉ A₀)
    (hx₀z : x₀ ≠ z) (hx₁z : x₁ ≠ z) (hx₀y : x₀ ≠ y) (hx₁y : x₁ ≠ y)
    (hzx₀ : G.Adj z x₀) (hzx₁ : G.Adj z x₁) (hyx₀ : G.Adj y x₀) (hyx₁ : G.Adj y x₁) :
    False := by
  classical
  -- the height-`1` wheel system `x₀, x₁`
  set xs : ℕ → V := fun j => if j = 0 then x₀ else x₁ with hxs
  have hxs0 : xs 0 = x₀ := by rw [hxs]; exact if_pos rfl
  have hxs1 : xs 1 = x₁ := by rw [hxs]; exact if_neg (by omega)
  have hX0 : wheelSystemX xs 0 = ({x₀} : Set V) := by
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have : j = 0 := by omega
      rw [this, hxs0]
    · rintro rfl; exact ⟨0, le_refl 0, hxs0.symm⟩
  have hX1 : wheelSystemX xs 1 = ({x₀, x₁} : Set V) := by
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j
      · exact Or.inl hxs0
      · exact Or.inr hxs1
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, hxs0.symm⟩
      · exact ⟨1, by omega, hxs1.symm⟩
  have hbase : GoodSeq G z y A₀ xs 1 := by
    refine ⟨le_refl 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj k hk hjk
      interval_cases j <;> interval_cases k <;> simp_all
    · intro j hj
      interval_cases j
      · rw [hxs0]; exact ⟨hx₀A, hx₀z, hx₀y⟩
      · rw [hxs1]; exact ⟨hx₁A, hx₁z, hx₁y⟩
    · rw [hxs0, hxs1]; exact ⟨hx₀A₀, hx₁A₀, hA₀nc⟩
    · intro i hi hit; omega
    · intro i hi hit
      have : i = 1 := by omega
      subst this
      rw [hxs1, show (1 : ℕ) - 1 = 0 from rfl, hX0]
      intro hc
      exact hnadj01 (hc x₀ rfl)
    · intro j hj
      interval_cases j
      · rw [hxs0]; exact hzx₀
      · rw [hxs1]; exact hzx₁
    · intro j hj
      interval_cases j
      · rw [hxs0]; exact hyx₀
      · rw [hxs1]; exact hyx₁
  -- **23.3 applied to `(z, A₀)` and `x₀, x₁`**: `y` has no other neighbour in `C`
  have hA₀sub : A₀ ⊆ wheelSystemA G z A₀ xs 1 := by
    refine Set.subset_sUnion_of_mem ⟨le_refl _, hA₀conn, hznbr, ?_⟩
    rw [hX1]; exact hA₀nc
  have hynbr : ∀ b ∈ A₀, ¬ G.Adj y b := by
    intro b hb hadj
    refine thm_23_3 G hG hbsp z A₀ ⟨hA₀ne, hA₀conn, hzA₀, hznbr⟩ xs 1
      (isWheelSystem_of_goodSeq hbase) ⟨y, ?_, ?_, b, hA₀sub hb, hadj⟩
    · rw [hX1]
      rintro (hc | hc | hc)
      · exact G.irrefl (hc ▸ hzy)
      · exact hx₀y hc.symm
      · exact hx₁y hc.symm
    · rw [hX1]
      rintro v (rfl | rfl | rfl)
      · exact hzy.symm
      · exact hyx₀
      · exact hyx₁
  -- **choose `t` maximum**
  have hbd : ∀ s : ℕ, (∃ x : ℕ → V, GoodSeq G z y A₀ x s) → s ≤ Fintype.card V := by
    rintro s ⟨x, hx⟩
    have hinj := hx.2.1
    have h1 : ((Finset.range (s + 1)).image x).card = (Finset.range (s + 1)).card := by
      refine Finset.card_image_of_injOn ?_
      intro p hp q hq hpq
      exact hinj p (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hp) q
        (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hq) hpq
    have h2 := Finset.card_le_univ ((Finset.range (s + 1)).image x)
    rw [h1, Finset.card_range] at h2
    omega
  obtain ⟨t, ⟨x, hgood⟩, hmax⟩ :=
    ExtremalChoice.exists_max_nat (fun s => ∃ x : ℕ → V, GoodSeq G z y A₀ x s) id
      (Fintype.card V) hbd ⟨1, xs, hbase⟩
  have hmaxt : ∀ x' : ℕ → V, ¬ GoodSeq G z y A₀ x' (t + 1) := by
    intro x' hc
    have hle : t + 1 ≤ t := hmax (t + 1) ⟨x', hc⟩
    omega
  obtain ⟨ht1, hinj, hnot, hcond1, hcond2, hcond3, hzx, hyx⟩ := hgood
  have hgood' : GoodSeq G z y A₀ x t := ⟨ht1, hinj, hnot, hcond1, hcond2, hcond3, hzx, hyx⟩
  set X : Set V := wheelSystemX x t with hXdef
  have hzXc : VertexComplete G z X := vc_wheelSystemX.mpr hzx
  have hyXc : VertexComplete G y X := vc_wheelSystemX.mpr hyx
  have hA₀X : ∀ b ∈ A₀, ¬ VertexComplete G b X := by
    intro b hb hc
    refine hcond1.2.2 b hb ?_
    rintro v (rfl | rfl)
    · exact hc _ (mem_wheelSystemX (Nat.zero_le t))
    · exact hc _ (mem_wheelSystemX ht1)
  have hA₀nX : ∀ b ∈ A₀, b ∉ X := by
    rintro b hb ⟨j, hj, rfl⟩
    exact (hnot j hj).1 hb
  -- **"Since `G` admits no skew partition by 15.1 …"**
  have hno : ¬ AdmitsSkewPartition G := fun h =>
    hbsp (_root_.Workspace.Statements.S15.SPGT.thm_15_1 G hG.1.1.1 h)
  have hXne : X.Nonempty := ⟨x 0, mem_wheelSystemX (Nat.zero_le t)⟩
  have hNne : {q : V | VertexComplete G q X}.Nonempty := ⟨z, hzXc⟩
  have hB := SkewPartitionFromSeparator.not_anticonnectedSet_separator_of_nonempty
    (G := G) hXne hNne
  have hA₀A : ∀ b ∈ A₀, b ∈ (X ∪ {q : V | VertexComplete G q X})ᶜ := by
    intro b hb
    exact SkewPartitionFromSeparator.mem_compl_separator_iff.mpr ⟨hA₀nX b hb, hA₀X b hb⟩
  obtain ⟨a₀, ha₀⟩ : ∃ b : V, b ∈ A₀ := id hA₀ne
  have hAne : ((X ∪ {q : V | VertexComplete G q X})ᶜ).Nonempty := ⟨a₀, hA₀A a₀ ha₀⟩
  have hyX : y ∉ X := by
    rintro ⟨j, hj, rfl⟩
    exact (hnot j hj).2.2 rfl
  have hyattach := SkewPartitionFromSeparator.exists_adj_compl_separator_of_no_skew_partition
    hno hXne hyXc ⟨z, hzXc, hzy.ne⟩ hAne
  obtain ⟨P₁, hP₁, hP₁X, hP₁int⟩ :=
    SkewPartitionFromSeparator.exists_path_interior_avoiding_of_no_skew_partition
      hno hB hyX (hA₀nX a₀ ha₀) (Or.inr hyattach) (Or.inl (hA₀A a₀ ha₀))
  -- **"Choose such a path of minimum length."**
  obtain ⟨P, ⟨q, b, hq, hb, hpath, hs, hsi⟩, hmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun Q : List V => ∃ q b : V, (q = z ∨ q = y) ∧ b ∈ A₀ ∧ IsPathFrom G Q q b ∧
        (∀ s ∈ Q, s ∉ X) ∧ (∀ s ∈ SPGT.interior Q, ¬ VertexComplete G s X))
      List.length ⟨P₁, y, a₀, Or.inr rfl, ha₀, hP₁, hP₁X, hP₁int⟩
  -- **"From the symmetry between `z, y` we may assume its first vertex is `y`."**
  rcases hq with rfl | rfl
  · exact endgame hG hbsp hA₀ne hA₀conn hzA₀ hyA₀ hznbr hynbr hzy hgood' hmaxt hb hpath hs hsi
      (fun Q q' b' hq' hb' hpath' hs' hsi' =>
        hmin Q ⟨q', b', hq', hb', hpath', hs', hsi'⟩)
  · refine endgame hG hbsp hA₀ne hA₀conn hyA₀ hzA₀ hynbr hznbr hzy.symm
      (goodSeq_swap hgood') (fun x' hc => hmaxt x' (goodSeq_swap hc)) hb hpath hs hsi ?_
    intro Q q' b' hq' hb' hpath' hs' hsi'
    exact hmin Q ⟨q', b', hq'.symm, hb', hpath', hs', hsi'⟩


/-- **23.4** — one of the twelve main steps: this is statement **1.8.10** (printed
p. 142), introduced by *"Now we can prove 1.8.10, the following."*

PAPER: *"Let `G ∈ F₉`, admitting no balanced skew partition, and let `C` be a hole
in `G` of length `≥ 6`.  Then there is no vertex of `G \ V(C)` with three
consecutive neighbours in `C`.  In particular, every recalcitrant graph belongs to
`F₁₀`."*

Transcription notes.

* *"three consecutive neighbours in `C`"* are three vertices occupying three
  cyclically consecutive positions of the hole and all adjacent to the vertex in
  question — the encoding already used in `Classes.InF10` (printed p. 7), whose
  first half this statement is (for `G`; `InF10` asks it for `Ḡ` as well).
* The hole `C` is universally quantified **inside** the conclusion rather than
  taken as a hypothesis binder; for this sentence the two readings are
  equivalent.
* The closing sentence *"In particular, every recalcitrant graph belongs to
  `F₁₀`"* is genuine mathematical content about all recalcitrant graphs, asserted
  under no hypothesis, and is the separate theorem `thm_23_4_recalcitrant`
  below. -/
theorem thm_23_4 (G : SimpleGraph V) (hG : InF9 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G) :
    ∀ C : List V, IsHoleList G C → 6 ≤ holeLength C →
        ¬ ∃ v : V, v ∉ C ∧ ∃ c₁ c₂ c₃ : V,
            (∃ k : ℕ, [c₁, c₂, c₃] <+: C.rotate k) ∧
            G.Adj v c₁ ∧ G.Adj v c₂ ∧ G.Adj v c₃ := by
  classical
  rintro C hC h6 ⟨v, hvC, c₁, c₂, c₃, ⟨k, tl, htl⟩, hvc₁, hvc₂, hvc₃⟩
  -- rotate so that the three consecutive neighbours are the first three vertices
  set D : List V := C.rotate k with hD
  have hDhole : IsHoleList G D := HoleBasics.isHoleList_rotate hC k
  have hDlen : D.length = C.length := by rw [hD, List.length_rotate]
  have hm6 : 6 ≤ D.length := by rw [hDlen]; exact h6
  have hDeq : D = c₁ :: c₂ :: c₃ :: tl := htl.symm
  have h0m : 0 < D.length := by omega
  have h1m : 1 < D.length := by omega
  have h2m : 2 < D.length := by omega
  have h3m : 3 < D.length := by omega
  have hd0 : D[0]'h0m = c₁ := by simp [hDeq]
  have hd1 : D[1]'h1m = c₂ := by simp [hDeq]
  have hd2 : D[2]'h2m = c₃ := by simp [hDeq]
  have hvD : v ∉ D := by rw [hD]; exact fun hc => hvC (List.mem_rotate.mp hc)
  -- `A₀ = V(C) \ {c₂, c₁, c₃}`
  set A₀ : Set V := {b : V | b ∈ D ∧ b ≠ c₁ ∧ b ≠ c₂ ∧ b ≠ c₃} with hA₀def
  have hA₀iff : ∀ b : V, b ∈ A₀ ↔ ∃ i, ∃ h : i < D.length, 3 ≤ i ∧ D[i]'h = b := by
    intro b
    constructor
    · rintro ⟨hbD, hb1, hb2, hb3⟩
      obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hbD
      refine ⟨i, hi, ?_, hib⟩
      by_contra hc
      interval_cases i
      · exact hb1 (by rw [← hib]; exact hd0)
      · exact hb2 (by rw [← hib]; exact hd1)
      · exact hb3 (by rw [← hib]; exact hd2)
    · rintro ⟨i, hi, h3i, rfl⟩
      refine ⟨List.getElem_mem hi, ?_, ?_, ?_⟩
      · rw [← hd0]; exact HoleBasics.hole_ne_of_ne_index hDhole hi h0m (by omega)
      · rw [← hd1]; exact HoleBasics.hole_ne_of_ne_index hDhole hi h1m (by omega)
      · rw [← hd2]; exact HoleBasics.hole_ne_of_ne_index hDhole hi h2m (by omega)
  -- `A₀` is nonempty and connected
  have hA₀ne : A₀.Nonempty := ⟨D[3]'h3m, (hA₀iff _).mpr ⟨3, h3m, le_refl 3, rfl⟩⟩
  have hA₀eq : A₀ = {s : V | s ∈ D.drop 3} := by
    ext b
    rw [hA₀iff b]
    simp only [Set.mem_setOf_eq]
    rw [mem_drop_iff' D 3 b]
  have hA₀conn : ConnectedSet G A₀ := by
    rw [hA₀eq]
    refine InducedPathExtraction.connectedSet_setOf_mem_of_isChain ?_
    refine List.isChain_iff_getElem.mpr ?_
    intro i hi
    rw [List.length_drop] at hi
    have e1 : (D.drop 3)[i]'(by rw [List.length_drop]; omega) = D[3 + i]'(by omega) := by
      rw [List.getElem_drop]
    have e2 : (D.drop 3)[i + 1]'(by rw [List.length_drop]; omega) = D[3 + i + 1]'(by omega) := by
      rw [List.getElem_drop]
      exact gidx D (by omega) _ _
    rw [e1, e2]
    exact HoleBasics.hole_adj_succ hDhole (by omega)
  -- neighbours of `c₂` on the hole
  have hznbr : ∀ b ∈ A₀, ¬ G.Adj c₂ b := by
    intro b hb
    obtain ⟨i, hi, h3i, rfl⟩ := (hA₀iff b).mp hb
    rw [← hd1]
    refine HoleBasics.hole_not_adj_of_gap' hDhole h1m hi ?_ ?_
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · by_cases hc : i + 1 = D.length
      · rw [hc, Nat.mod_self]; omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
  -- `c₁` and `c₃` each have a neighbour in `A₀`
  have hx₀A₀ : ∃ b ∈ A₀, G.Adj c₁ b := by
    refine ⟨D[D.length - 1]'(by omega),
      (hA₀iff _).mpr ⟨D.length - 1, by omega, by omega, rfl⟩, ?_⟩
    rw [← hd0]
    exact (HoleBasics.hole_adj_wrap hDhole).symm
  have hx₁A₀ : ∃ b ∈ A₀, G.Adj c₃ b := by
    refine ⟨D[3]'h3m, (hA₀iff _).mpr ⟨3, h3m, le_refl 3, rfl⟩, ?_⟩
    rw [← hd2]
    exact HoleBasics.hole_adj_succ hDhole (by omega)
  -- no vertex of `A₀` is `{c₁,c₃}`-complete
  have hA₀nc : ∀ b ∈ A₀, ¬ VertexComplete G b ({c₁, c₃} : Set V) := by
    intro b hb hcomp
    obtain ⟨i, hi, h3i, rfl⟩ := (hA₀iff b).mp hb
    have hb1 : G.Adj (D[i]'hi) (D[0]'h0m) := by rw [hd0]; exact hcomp c₁ (Or.inl rfl)
    have hb3 : G.Adj (D[i]'hi) (D[2]'h2m) := by rw [hd2]; exact hcomp c₃ (Or.inr rfl)
    rcases (HoleBasics.hole_adj_iff hDhole hi h0m).mp hb1 with e1 | e1
    · -- `0 = (i+1) % D.length`
      have hwrap : i + 1 = D.length := by
        by_cases hc : i + 1 = D.length
        · exact hc
        · rw [Nat.mod_eq_of_lt (by omega)] at e1; omega
      rcases (HoleBasics.hole_adj_iff hDhole hi h2m).mp hb3 with e2 | e2
      · by_cases hc : i + 1 = D.length
        · rw [hc, Nat.mod_self] at e2; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at e2; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at e2; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at e1; omega
  -- the remaining bookkeeping facts about `c₁, c₂, c₃, v`
  have hx₀x₁ : c₁ ≠ c₃ := by
    rw [← hd0, ← hd2]; exact HoleBasics.hole_ne_of_ne_index hDhole h0m h2m (by omega)
  have hnadj01 : ¬ G.Adj c₃ c₁ := by
    rw [← hd0, ← hd2]
    refine HoleBasics.hole_not_adj_of_gap' hDhole h2m h0m ?_ ?_
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hc₁A : c₁ ∉ A₀ := by rintro ⟨-, hc, -, -⟩; exact hc rfl
  have hc₂A : c₂ ∉ A₀ := by rintro ⟨-, -, hc, -⟩; exact hc rfl
  have hc₃A : c₃ ∉ A₀ := by rintro ⟨-, -, -, hc⟩; exact hc rfl
  have hvA : v ∉ A₀ := by rintro ⟨hc, -, -, -⟩; exact hvD hc
  have hx₀z : c₁ ≠ c₂ := by
    rw [← hd0, ← hd1]; exact HoleBasics.hole_ne_of_ne_index hDhole h0m h1m (by omega)
  have hx₁z : c₃ ≠ c₂ := by
    rw [← hd2, ← hd1]; exact HoleBasics.hole_ne_of_ne_index hDhole h2m h1m (by omega)
  have hx₀y : c₁ ≠ v := hvc₁.ne'
  have hx₁y : c₃ ≠ v := hvc₃.ne'
  have hzx₀ : G.Adj c₂ c₁ := by
    rw [← hd0, ← hd1]; exact (HoleBasics.hole_adj_succ hDhole (by omega)).symm
  have hzx₁ : G.Adj c₂ c₃ := by
    rw [← hd1, ← hd2]; exact HoleBasics.hole_adj_succ hDhole (by omega)
  exact core hG hbsp hA₀ne hA₀conn hc₂A hvA hznbr hvc₂.symm hx₀A₀ hx₁A₀ hA₀nc hx₀x₁ hnadj01
    hc₁A hc₃A hx₀z hx₁z hx₀y hx₁y hzx₀ hzx₁ hvc₁ hvc₃


end SPGT

end Workspace.Statements.S23
