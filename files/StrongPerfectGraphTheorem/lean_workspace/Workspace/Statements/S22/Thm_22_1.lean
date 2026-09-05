import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Statements.S15.Thm_15_1
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.SkewPartitionFromSeparator
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.PathBasics

/-!
# 22.1

PAPER (printed p. 137), the whole printed proof:

> *"Choose a sequence `x_{s+1}, …, x_t`, all `Y`-complete and such that `x₀, …, x_t` is a wheel
> system with respect to `(z, A₀)`, with `t` maximum.  So `t ≥ s ≥ 1`.  Define `Xᵢ` and `Aᵢ` as
> usual.  From 15.2, there is a path `P` from `z` to `A_t`, disjoint from `X_t` and containing
> no `X_t`-complete vertex except `z`.  Let `v` be the neighbour of `z` in this path.  From the
> maximality of `A_t`, it follows that `P` has length 2.  So `v` has a neighbour in `A_t`, and
> therefore `x₀, …, x_t, v` is a wheel system.  From the maximality of `t` it follows that `v`
> is not `Y`-complete, and therefore `Y` is a hub for this wheel system.  This proves 22.1."*

Step for step:

| printed sentence | Lean |
|---|---|
| *"Choose … with `t` maximum"* | `ExtremalChoice.exists_max_nat` over `(ℕ → V) × ℕ`, bounded by `Fintype.card V` because the terms of a wheel system are distinct |
| *"From 15.2, there is a path `P` from `z` to `A_t`, disjoint from `X_t` and containing no `X_t`-complete vertex except `z`"* | `SkewPartitionFromSeparator.exists_path_interior_avoiding_of_no_skew_partition` at `X := X_t`; the no-skew-partition hypothesis comes from `thm_15_1` |
| *"From the maximality of `A_t` … `v` has a neighbour in `A_t`"* | `WheelSystemBasics.mem_wheelSystemA_of_witness` at `B := A_t ∪ V(P.drop 2)` |
| *"therefore `x₀,…,x_t,v` is a wheel system"* | the seven clauses, verified for `fun j => if j ≤ t then f j else v` |
| *"From the maximality of `t` it follows that `v` is not `Y`-complete"* | else `(f', t+1)` beats the maximum |

Two things the paper leaves implicit:

* Applying the separator machinery at `X := X_t` needs `z` to have a neighbour outside
  `X_t ∪ {X_t`-complete vertices`}`, and that in turn needs a **second** `X_t`-complete vertex
  besides `z` (otherwise deleting `z` from the separator leaves `X_t`, which *is*
  anticonnected — each `xᵢ` has a non-neighbour among `x₀,…,x_{i−1}` by condition 3).  The
  second vertex is any member of `Y`: every `x₀, …, x_t` is `Y`-complete, so every member of
  `Y` is `X_t`-complete.
* The paper concludes *"`P` has length 2"*; the proof only ever uses the consequence *"`v` has
  a neighbour in `A_t`"*, which is what is established here (`P[2] ∈ A_t`).  `v ∉ A_t` because
  `A_t` contains no neighbour of `z`, so `P` does have at least three vertices.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S22

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **22.1** (printed p. 137).

PAPER: *"Let `G ∈ F₈`, not admitting a balanced skew partition, let `(z, A₀)` be a
frame, and let `x₀,…,x_s` be a wheel system.  Let
`Y ⊆ V(G) \ (A₀ ∪ {z, x₀,…,x_s})` be nonempty and anticonnected, such that
`z, x₀,…,x_s` are `Y`-complete.  Then there is a sequence `x_{s+1},…,x_{t+1}` with
`t ≥ s` such that `x₀,…,x_{t+1}` is a wheel system with respect to the frame
`(z, A₀)`, with hub `Y`."* -/
theorem thm_22_1 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (s : ℕ) (hws : IsWheelSystem G z A₀ x s)
    (Y : Set V) (hYdisj : ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z ∧ ∀ i ≤ s, y ≠ x i)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hzY : VertexComplete G z Y) (hxY : ∀ i ≤ s, VertexComplete G (x i) Y) :
    ∃ (x' : ℕ → V) (t : ℕ), s ≤ t ∧ (∀ i ≤ s, x' i = x i) ∧
      IsHubForWheelSystem G z A₀ x' (t + 1) Y := by
  classical
  have hs1 : 1 ≤ s := hws.1
  have hnoskew : ¬ AdmitsSkewPartition G := fun h =>
    hbsp (_root_.Workspace.Statements.S15.SPGT.thm_15_1 G hG.1.1 h)
  -- ### "Choose a sequence `x_{s+1},…,x_t`, … with `t` maximum."
  have hbd : ∀ p : (ℕ → V) × ℕ,
      (s ≤ p.2 ∧ (∀ i ≤ s, p.1 i = x i) ∧ IsWheelSystem G z A₀ p.1 p.2 ∧
        ∀ i, s < i → i ≤ p.2 → VertexComplete G (p.1 i) Y) → p.2 ≤ Fintype.card V := by
    rintro ⟨g, m⟩ ⟨-, -, hg, -⟩
    simp only at hg ⊢
    have hinj : Function.Injective (fun j : Fin (m + 1) => g (j : ℕ)) := by
      intro a b hab
      exact Fin.ext (hg.2.1 (a : ℕ) (Nat.lt_succ_iff.mp a.isLt) (b : ℕ)
        (Nat.lt_succ_iff.mp b.isLt) hab)
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨⟨f, t⟩, hP, hmax⟩ :=
    ExtremalChoice.exists_max_nat
      (fun p : (ℕ → V) × ℕ =>
        s ≤ p.2 ∧ (∀ i ≤ s, p.1 i = x i) ∧ IsWheelSystem G z A₀ p.1 p.2 ∧
          ∀ i, s < i → i ≤ p.2 → VertexComplete G (p.1 i) Y)
      (fun p => p.2) (Fintype.card V) hbd
      ⟨⟨x, s⟩, le_refl s, fun i _ => rfl, hws, fun i h1 h2 => absurd h1 (by omega)⟩
  simp only at hP hmax
  obtain ⟨hst, hfx, hwsf, hfY⟩ := hP
  have ht1 : 1 ≤ t := le_trans hs1 hst
  -- Every term of the chosen system is `Y`-complete.
  have hallY : ∀ i ≤ t, VertexComplete G (f i) Y := by
    intro i hi
    rcases (by omega : i ≤ s ∨ s < i) with h | h
    · rw [hfx i h]; exact hxY i h
    · exact hfY i h hi
  -- ### `X_t` and `A_t`.
  have hA₀At : A₀ ⊆ wheelSystemA G z A₀ f t :=
    KiteTailBasics.A₀_subset_wheelSystemA_of_wheelSystem hframe hwsf
  obtain ⟨a, haA⟩ : (wheelSystemA G z A₀ f t).Nonempty := by
    obtain ⟨b, hb⟩ := hframe.1
    exact ⟨b, hA₀At hb⟩
  have hAnoz : ∀ w ∈ wheelSystemA G z A₀ f t, ¬ G.Adj z w := fun w hw =>
    WheelSystemBasics.wheelSystemA_no_nbr hw
  have hAnoc : ∀ w ∈ wheelSystemA G z A₀ f t, ¬ VertexComplete G w (wheelSystemX f t) :=
    fun w hw => WheelSystemBasics.wheelSystemA_no_complete hw
  -- Every `f j` is a neighbour of `z`, hence lies outside `A_t`.
  have hXtnotA : ∀ w ∈ wheelSystemX f t, w ∉ wheelSystemA G z A₀ f t := by
    intro w hw hwA
    obtain ⟨j, hj, rfl⟩ := WheelSystemBasics.mem_wheelSystemX.mp hw
    exact hAnoz _ hwA (hwsf.2.2.2.2.2.2 j hj)
  -- `z` is `X_t`-complete, and so is every member of `Y`.
  have hzXt : VertexComplete G z (wheelSystemX f t) := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := WheelSystemBasics.mem_wheelSystemX.mp hc
    exact hwsf.2.2.2.2.2.2 j hj
  obtain ⟨y₀, hy₀Y⟩ := hYne
  have hy₀Xt : VertexComplete G y₀ (wheelSystemX f t) := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := WheelSystemBasics.mem_wheelSystemX.mp hc
    exact (hallY j hj y₀ hy₀Y).symm
  have hy₀z : y₀ ≠ z := (hYdisj y₀ hy₀Y).2.1
  have hXtne : (wheelSystemX f t).Nonempty := ⟨f 0, ⟨0, by omega, rfl⟩⟩
  have hzXtnot : z ∉ wheelSystemX f t := by
    intro hc
    obtain ⟨j, hj, hzj⟩ := WheelSystemBasics.mem_wheelSystemX.mp hc
    exact (hwsf.2.2.1 j hj).2 hzj.symm
  -- `a` lies outside the separator `X_t ∪ {X_t`-complete`}`.
  have haCompl : a ∈ (wheelSystemX f t ∪
      {w : V | VertexComplete G w (wheelSystemX f t)})ᶜ := by
    rintro (hc | hc)
    · exact hXtnotA a hc haA
    · exact hAnoc a haA hc
  have hanotX : a ∉ wheelSystemX f t := fun hc => hXtnotA a hc haA
  -- ### "From 15.2, there is a path `P` from `z` to `A_t` …"
  have hB : ¬ AnticonnectedSet G (wheelSystemX f t ∪
      {w : V | VertexComplete G w (wheelSystemX f t)}) :=
    SkewPartitionFromSeparator.not_anticonnectedSet_separator_of_nonempty hXtne ⟨z, hzXt⟩
  have hua : ∃ b ∈ (wheelSystemX f t ∪
      {w : V | VertexComplete G w (wheelSystemX f t)})ᶜ, G.Adj z b :=
    SkewPartitionFromSeparator.exists_adj_compl_separator_of_no_skew_partition
      hnoskew hXtne hzXt ⟨y₀, hy₀Xt, hy₀z⟩ ⟨a, haCompl⟩
  obtain ⟨P, hPfrom, hPX, hPint⟩ :=
    SkewPartitionFromSeparator.exists_path_interior_avoiding_of_no_skew_partition
      hnoskew hB hzXtnot hanotX (Or.inr hua) (Or.inl haCompl)
  -- ### "Let `v` be the neighbour of `z` in this path."
  have hnd : P.Nodup := hPfrom.1.2.1
  have hza : z ≠ a := by
    rintro rfl
    exact hAnoc z haA hzXt
  have hlast : ∀ h : P.length - 1 < P.length, P[P.length - 1]'h = a := by
    intro h
    have hg := hPfrom.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem h] at hg
    exact Option.some_injective _ hg
  have hhead : ∀ h : 0 < P.length, P[0]'h = z := by
    intro h
    have hg := hPfrom.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h] at hg
    exact Option.some_injective _ hg
  have hPpos : 0 < P.length := List.length_pos_of_ne_nil hPfrom.1.1
  have hPlen2 : 2 ≤ P.length := by
    by_contra hc
    have h1 : P.length = 1 := by omega
    have e3 : P[0]'hPpos = P[P.length - 1]'(by omega) :=
      hnd.getElem_inj_iff.mpr (by omega)
    exact hza ((hhead hPpos).symm.trans (e3.trans (hlast (by omega))))
  have hP1lt : 1 < P.length := by omega
  have hzv : G.Adj z (P[1]'hP1lt) := by
    have h := PathBasics.path_adj_succ hPfrom.1 (i := 0) (by omega)
    rw [hhead (by omega)] at h
    exact h
  -- `v ∉ A_t` (it is a neighbour of `z`), so `P` has at least three vertices.
  have hvnotA : (P[1]'hP1lt) ∉ wheelSystemA G z A₀ f t := fun hc => hAnoz _ hc hzv
  have hva : (P[1]'hP1lt) ≠ a := fun hc => hvnotA (hc ▸ haA)
  have hPlen3 : 3 ≤ P.length := by
    by_contra hc
    have h2 : P.length = 2 := by omega
    have e1 : P[1]'hP1lt = P[P.length - 1]'(by omega) :=
      hnd.getElem_inj_iff.mpr (by omega)
    exact hva (e1.trans (hlast (by omega)))
  have hP2lt : 2 < P.length := by omega
  -- ### "So `v` has a neighbour in `A_t`" — via `B := A_t ∪ V(P.drop 2)`.
  have hdropmem : ∀ w : V, w ∈ P.drop 2 → ∃ (k : ℕ) (hk : k < P.length), 2 ≤ k ∧ P[k]'hk = w := by
    intro w hw
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
    have hk' : 2 + k < P.length := by
      simp only [List.length_drop] at hk; omega
    refine ⟨2 + k, hk', by omega, ?_⟩
    rw [← hkw]
    simp only [List.getElem_drop]
  have hdropconn : ConnectedSet G {w : V | w ∈ P.drop 2} :=
    KiteTailBasics.connectedSet_of_isPathList (PathBasics.isPathList_drop hPfrom.1 (by omega))
  have hamemdrop : a ∈ P.drop 2 := by
    have hlt : P.length - 1 - 2 < (P.drop 2).length := by
      simp only [List.length_drop]; omega
    have hm := List.getElem_mem hlt
    have heq : (P.drop 2)[P.length - 1 - 2]'hlt = a := by
      have h1 : (P.drop 2)[P.length - 1 - 2]'hlt = P[2 + (P.length - 1 - 2)]'(by omega) := by
        simp only [List.getElem_drop]
      rw [h1]
      have h2 : P[2 + (P.length - 1 - 2)]'(by omega) = P[P.length - 1]'(by omega) :=
        hnd.getElem_inj_iff.mpr (by omega)
      rw [h2]
      exact hlast (by omega)
    rwa [heq] at hm
  have hP2mem : P[2]'hP2lt ∈ P.drop 2 := by
    have hlt : 0 < (P.drop 2).length := by simp only [List.length_drop]; omega
    have hm := List.getElem_mem hlt
    have heq : (P.drop 2)[0]'hlt = P[2]'hP2lt := by
      simp only [List.getElem_drop]
    rwa [heq] at hm
  have hBconn : ConnectedSet G (wheelSystemA G z A₀ f t ∪ {w : V | w ∈ P.drop 2}) :=
    ConnectedSetUnionAttach.connectedSet_union
      (WheelSystemBasics.connectedSet_wheelSystemA hframe.1) hdropconn
      (Or.inl ⟨a, haA, hamemdrop⟩)
  have hBz : ∀ w ∈ (wheelSystemA G z A₀ f t ∪ {w : V | w ∈ P.drop 2}), ¬ G.Adj z w := by
    rintro w (hw | hw)
    · exact hAnoz w hw
    · obtain ⟨k, hk, hk2, rfl⟩ := hdropmem w hw
      intro hadj
      rw [← hhead (by omega)] at hadj
      have := (PathBasics.path_adj_iff hPfrom.1 (by omega) hk).mp hadj
      omega
  have hBX : ∀ w ∈ (wheelSystemA G z A₀ f t ∪ {w : V | w ∈ P.drop 2}),
      ¬ VertexComplete G w (wheelSystemX f t) := by
    rintro w (hw | hw)
    · exact hAnoc w hw
    · by_cases hwa : w = a
      · rw [hwa]; exact hAnoc a haA
      · refine hPint w ?_
        obtain ⟨k, hk, hk2, hkw⟩ := hdropmem w hw
        refine (PathBasics.mem_interior_iff_of_pathFrom hPfrom).mpr ⟨?_, ?_, hwa⟩
        · rw [← hkw]; exact List.getElem_mem hk
        · rw [← hkw, ← hhead (by omega)]
          exact fun hc => absurd (hnd.getElem_inj_iff.mp hc) (by omega)
  have hP2A : P[2]'hP2lt ∈ wheelSystemA G z A₀ f t :=
    WheelSystemBasics.mem_wheelSystemA_of_witness
      (fun w hw => Or.inl (hA₀At hw)) hBconn hBz hBX (Or.inr hP2mem)
  have hvnbr : ∃ b ∈ wheelSystemA G z A₀ f t, G.Adj (P[1]'hP1lt) b :=
    ⟨P[2]'hP2lt, hP2A, PathBasics.path_adj_succ hPfrom.1 (i := 1) (by omega)⟩
  -- `v` is not `X_t`-complete, and lies outside `X_t`.
  have hvnotXt : P[1]'hP1lt ∉ wheelSystemX f t :=
    hPX _ (List.getElem_mem (by omega))
  have hvnotc : ¬ VertexComplete G (P[1]'hP1lt) (wheelSystemX f t) := by
    refine hPint _ ((PathBasics.mem_interior_iff_of_pathFrom hPfrom).mpr
      ⟨List.getElem_mem (by omega), ?_, hva⟩)
    rw [← hhead (by omega)]
    exact fun hc => absurd (hnd.getElem_inj_iff.mp hc) (by omega)
  -- ### "therefore `x₀,…,x_t,v` is a wheel system."
  obtain ⟨f', hf'⟩ : ∃ g : ℕ → V, g = (fun j => if j ≤ t then f j else P[1]'hP1lt) :=
    ⟨_, rfl⟩
  have hf'le : ∀ j ≤ t, f' j = f j := by
    intro j hj
    rw [hf']
    show (if j ≤ t then f j else P[1]'hP1lt) = f j
    rw [if_pos hj]
  have hf'top : f' (t + 1) = P[1]'hP1lt := by
    rw [hf']
    show (if t + 1 ≤ t then f (t + 1) else P[1]'hP1lt) = P[1]'hP1lt
    rw [if_neg (by omega)]
  have hXcongr : ∀ i ≤ t, wheelSystemX f' i = wheelSystemX f i := by
    intro i hi
    exact KiteTailBasics.wheelSystemX_congr (fun j hj => hf'le j (by omega))
  have hAcongr : ∀ i ≤ t, wheelSystemA G z A₀ f' i = wheelSystemA G z A₀ f i := by
    intro i hi
    exact KiteTailBasics.wheelSystemA_congr (fun j hj => hf'le j (by omega))
  have hwsf' : IsWheelSystem G z A₀ f' (t + 1) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- distinctness
      intro j hj k hk he
      rcases (by omega : j ≤ t ∨ t < j) with hjt | hjt <;>
        rcases (by omega : k ≤ t ∨ t < k) with hkt | hkt
      · rw [hf'le j hjt, hf'le k hkt] at he
        exact hwsf.2.1 j hjt k hkt he
      · exfalso
        obtain rfl : k = t + 1 := by omega
        rw [hf'le j hjt, hf'top] at he
        exact hvnotXt ⟨j, hjt, he.symm⟩
      · exfalso
        obtain rfl : j = t + 1 := by omega
        rw [hf'le k hkt, hf'top] at he
        exact hvnotXt ⟨k, hkt, he⟩
      · omega
    · -- outside `A₀`, distinct from `z`
      intro j hj
      rcases (by omega : j ≤ t ∨ t < j) with hjt | hjt
      · rw [hf'le j hjt]; exact hwsf.2.2.1 j hjt
      · obtain rfl : j = t + 1 := by omega
        rw [hf'top]
        exact ⟨fun hc => hAnoz _ (hA₀At hc) hzv, fun hc => G.irrefl (hc ▸ hzv)⟩
    · -- condition 1 (only mentions `f' 0`, `f' 1`)
      rw [hf'le 0 (by omega), hf'le 1 (by omega)]
      exact hwsf.2.2.2.1
    · -- condition 2
      intro i h2 h1
      rcases (by omega : i ≤ t ∨ t < i) with hit | hit
      · obtain ⟨B, hA₀B, hBc, hBn, hBz', hBX'⟩ := hwsf.2.2.2.2.1 i h2 hit
        refine ⟨B, hA₀B, hBc, ?_, hBz', ?_⟩
        · rw [hf'le i hit]; exact hBn
        · rw [hXcongr (i - 1) (by omega)]; exact hBX'
      · obtain rfl : i = t + 1 := by omega
        refine ⟨wheelSystemA G z A₀ f t, hA₀At,
          WheelSystemBasics.connectedSet_wheelSystemA hframe.1, ?_, hAnoz, ?_⟩
        · rw [hf'top]; exact hvnbr
        · rw [show t + 1 - 1 = t from by omega, hXcongr t (le_refl t)]; exact hAnoc
    · -- condition 3
      intro i h1 hi
      rcases (by omega : i ≤ t ∨ t < i) with hit | hit
      · rw [hf'le i hit, hXcongr (i - 1) (by omega)]
        exact hwsf.2.2.2.2.2.1 i h1 hit
      · obtain rfl : i = t + 1 := by omega
        rw [hf'top, show t + 1 - 1 = t from by omega, hXcongr t (le_refl t)]
        exact hvnotc
    · -- `z` is adjacent to every term
      intro j hj
      rcases (by omega : j ≤ t ∨ t < j) with hjt | hjt
      · rw [hf'le j hjt]; exact hwsf.2.2.2.2.2.2 j hjt
      · obtain rfl : j = t + 1 := by omega
        rw [hf'top]; exact hzv
  -- ### "From the maximality of `t` it follows that `v` is not `Y`-complete."
  have hfx' : ∀ i ≤ s, f' i = x i := by
    intro i hi
    rw [hf'le i (by omega)]
    exact hfx i hi
  have hvY : ¬ VertexComplete G (P[1]'hP1lt) Y := by
    intro hc
    have hY' : ∀ i, s < i → i ≤ t + 1 → VertexComplete G (f' i) Y := by
      intro i h1 h2
      rcases (by omega : i ≤ t ∨ t < i) with hit | hit
      · rw [hf'le i hit]; exact hfY i h1 hit
      · obtain rfl : i = t + 1 := by omega
        rw [hf'top]; exact hc
    have hbeat := hmax ⟨f', t + 1⟩ ⟨by omega, hfx', hwsf', hY'⟩
    simp only at hbeat
    omega
  -- ### "and therefore `Y` is a hub for this wheel system."
  refine ⟨f', t, hst, hfx', ?_⟩
  refine ⟨hwsf', ⟨y₀, hy₀Y⟩, hYanti, ?_, hzY, ?_, ?_⟩
  · intro c hc
    exact ⟨(hYdisj c hc).1, (hYdisj c hc).2.1⟩
  · intro i hi
    rw [hf'le i (by omega)]
    exact hallY i (by omega)
  · rw [hf'top]; exact hvY


end SPGT

end Workspace.Statements.S22
