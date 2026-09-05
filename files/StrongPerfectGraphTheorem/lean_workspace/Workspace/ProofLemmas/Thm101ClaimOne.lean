import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm101Assembly
-- extra imports needed by the proof only
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.Thm101LinkOntoTriangle
import Workspace.ProofLemmas.Thm101K4Appearance
import Workspace.Statements.S02.Thm_2_4

/-!
# 10.1, claim (1): the case `n = 1`

Proof of `Workspace.ProofLemmas.Thm101ClaimOne.claim_one`, following `paper/proofs/10_1.md`
sentence by sentence.  The private helpers above the theorem are the paper's `cᵢ`, `dᵢ`, `Cᵢ`,
`Dᵢ` and its five appeals to 2.4; `tri_own_path` and `paths_disjoint` are prism facts that
belong in `PrismSymmetry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm101ClaimOne

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Prism bookkeeping (candidates for `PrismSymmetry`) -/

/-- A triangle vertex of a prism lies only on its own path. -/
theorem tri_own_path {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (i k : Fin 3) (hk : a k ∈ R i) : k = i := by
  obtain ⟨hA, hB, hAB, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp h
  have hthird : ∀ i k : Fin 3, i ≠ k → ∃ m : Fin 3, m ≠ i ∧ m ≠ k := by decide
  by_contra hne
  obtain ⟨m, hmi, hmk⟩ := hthird i k (fun hc => hne hc.symm)
  have hmemA : ∀ j : Fin 3, a j ∈ R j := fun j => PathBasics.head_mem (hp j).2.1
  have h1 := (hedge i m (Ne.symm hmi) (a k) hk (a m) (hmemA m)).mp (hA k m (Ne.symm hmk))
  rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
  · have h2 := hA k i hne
    rw [h1] at h2
    exact G.irrefl h2
  · exact hAB k i h1

/-- The `b`-side version of `tri_own_path`. -/
theorem tri_own_path' {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (i k : Fin 3) (hk : b k ∈ R i) : k = i := by
  obtain ⟨hA, hB, hAB, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp h
  have hthird : ∀ i k : Fin 3, i ≠ k → ∃ m : Fin 3, m ≠ i ∧ m ≠ k := by decide
  by_contra hne
  obtain ⟨m, hmi, hmk⟩ := hthird i k (fun hc => hne hc.symm)
  have hmemB : ∀ j : Fin 3, b j ∈ R j := fun j => PathBasics.getLast_mem (hp j).2.2
  have h1 := (hedge i m (Ne.symm hmi) (b k) hk (b m) (hmemB m)).mp (hB k m (Ne.symm hmk))
  rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hAB i k h1.symm
  · have h2 := hB k i hne
    rw [h1] at h2
    exact G.irrefl h2

/-- Each path of a prism has at least two vertices. -/
theorem two_le_length {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (k : Fin 3) : 2 ≤ (R k).length := by
  obtain ⟨hA, hB, hAB, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp h
  by_contra hcon
  have h1 : (R k) ≠ [] := (hp k).1.1
  have h2 : 0 < (R k).length := List.length_pos_of_ne_nil h1
  have h3 : (R k).length = 1 := by omega
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp h3
  have e1 : (R k).head? = some (a k) := (hp k).2.1
  have e2 : (R k).getLast? = some (b k) := (hp k).2.2
  rw [hc] at e1 e2
  simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at e1 e2
  exact hAB k k (e1.symm.trans e2)

/-- The three paths of a prism are pairwise vertex-disjoint. -/
theorem paths_disjoint {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) {x : V}
    (hxi : x ∈ R i) (hxj : x ∈ R j) : False := by
  obtain ⟨hA, hB, hAB, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp h
  obtain ⟨z, hzj, hxz⟩ : ∃ z : V, z ∈ R j ∧ G.Adj x z := by
    obtain ⟨t, ht, hxt⟩ := List.getElem_of_mem hxj
    have hL := two_le_length h j
    by_cases hc : t + 1 < (R j).length
    · refine ⟨(R j)[t + 1], List.getElem_mem _, ?_⟩
      have hh := (PathBasics.path_adj_iff (hp j).1 ht hc).mpr (Or.inl rfl)
      rw [hxt] at hh
      exact hh
    · have ht1 : 1 ≤ t := by omega
      have hlt : t - 1 < (R j).length := by omega
      refine ⟨(R j)[t - 1], List.getElem_mem _, ?_⟩
      have hh := (PathBasics.path_adj_iff (hp j).1 ht hlt).mpr (Or.inr (by omega))
      rw [hxt] at hh
      exact hh
  rcases (hedge i j hij x hxi z hzj).mp hxz with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hij (tri_own_path h j i (h1 ▸ hxj))
  · exact hij (tri_own_path' h j i (h1 ▸ hxj))

/-! ### The paper's *"`v` can be linked onto the triangle `A`"*, for sub-paths of the prism -/

/-- Three sub-paths `p 0, p 1, p 2` of the three prism paths, each with `a i` as an end, at
most one of which contains its own `b`-end, and each containing a neighbour of `v`, link `v`
onto the triangle `A`.  (`Thm101LinkOntoTriangle.canBeLinkedOntoTriangle_of_prism_segments`
is the special case in which *no* `p i` contains `b i`.) -/
theorem link_onto_A {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2)) (v : V) (p : Fin 3 → List V)
    (hpath : ∀ i : Fin 3, IsPathList G (p i))
    (hsub : ∀ i : Fin 3, ∀ x ∈ p i, x ∈ R i)
    (hend : ∀ i : Fin 3, (p i).head? = some (a i) ∨ (p i).getLast? = some (a i))
    (hb : ∀ i j : Fin 3, i ≠ j → b i ∈ p i → b j ∉ p j)
    (hnbr : ∀ i : Fin 3, ∃ x ∈ p i, G.Adj v x) :
    VertexCanBeLinkedOntoTriangle G v (a 0) (a 1) (a 2) := by
  obtain ⟨hA, hB, hAB, hpp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  refine Thm101LinkOntoTriangle.canBeLinkedOntoTriangle_of_sectors G v a p
    (fun i => {x : V | x ∈ p i}) hA hpath hend (fun i x hx => hx) ?_ ?_ hnbr
  · intro i j hij x hx hxj
    exact paths_disjoint hprism hij (hsub i x hx) (hsub j x hxj)
  · intro i j hij x hx y hy hxy
    rcases (hedge i j hij x (hsub i x hx) y (hsub j y hy)).mp hxy with hcase | hcase
    · exact hcase
    · exact absurd (hcase.2 ▸ hy) (hb i j hij (hcase.1 ▸ hx))

/-! ### The paper's `cᵢ` and `Cᵢ`: the attachment of `v` on `R i` closest to `a i` -/

/-- Least index satisfying a predicate. -/
theorem exists_least {Q : ℕ → Prop} (h : ∃ k, Q k) : ∃ k, Q k ∧ ∀ m, m < k → ¬ Q m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

/-- **The paper's `cᵢ` and `Cᵢ`.**  For a path `p` from `u` to `w` and a vertex `v` with a
neighbour on `p`, `c` is the neighbour of `v` on `p` closest to `u`, and `q = p.take (k+1)`
is the sub-path `u-p-c` (the paper's `Cᵢ`).  The last clause records the paper's
*"`cᵢ = bᵢ` iff `Cᵢ` runs all the way to `bᵢ`"*. -/
theorem first_attach {G : SimpleGraph V} {p : List V} {u w v : V}
    (hp : IsPathFrom G p u w) (hex : ∃ x ∈ p, G.Adj v x) :
    ∃ (k : ℕ) (hk : k < p.length),
      IsPathFrom G (p.take (k + 1)) u (p[k]'hk) ∧
      G.Adj v (p[k]'hk) ∧
      (∀ y ∈ p.take (k + 1), y ∈ p) ∧
      (∀ y ∈ p.take (k + 1), G.Adj v y → y = p[k]'hk) ∧
      (w ∈ p.take (k + 1) ↔ p[k]'hk = w) ∧
      (∀ (t : ℕ) (ht : t < p.length), G.Adj v (p[t]'ht) → k ≤ t) := by
  classical
  have hne : p ≠ [] := hp.1.1
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have hnd : p.Nodup := hp.1.2.1
  obtain ⟨k, ⟨hk, hadj⟩, hmin⟩ :
      ∃ k, (∃ hk : k < p.length, G.Adj v (p[k]'hk)) ∧
        ∀ m, m < k → ¬ (∃ hm : m < p.length, G.Adj v (p[m]'hm)) := by
    refine exists_least ?_
    obtain ⟨x, hxp, hadjx⟩ := hex
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxp
    exact ⟨j, hj, by rw [hjx]; exact hadjx⟩
  have hlast : p[p.length - 1]'(by omega) = w :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hmemtake : ∀ y : V, y ∈ p.take (k + 1) ↔ ∃ (t : ℕ) (ht : t < p.length),
      t ≤ k ∧ p[t]'ht = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨t, ht, hty⟩ := List.getElem_of_mem hy
      have htlen : t < min (k + 1) p.length := by simpa using ht
      have ht' : t < p.length := by omega
      exact ⟨t, ht', by omega, by rw [← hty]; exact (List.getElem_take ..).symm⟩
    · rintro ⟨t, ht, htk, rfl⟩
      have : t < (p.take (k + 1)).length := by
        rw [List.length_take]; omega
      have he : (p.take (k + 1))[t]'this = p[t]'ht := List.getElem_take ..
      rw [← he]
      exact List.getElem_mem _
  refine ⟨k, hk, ?_, hadj, ?_, ?_, ?_, ?_⟩
  · refine ⟨PathBasics.isPathList_take hp.1 (by omega), ?_, ?_⟩
    · obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [List.take_succ_cons]
      simpa using hp.2.1
    · have h := PathBasics.getLast?_slice p (i := 0) (j := k) (by omega) hk
      simpa using h
  · intro y hy
    exact ((hmemtake y).mp hy).choose_spec.choose_spec.2 ▸ List.getElem_mem _
  · intro y hy hadjy
    obtain ⟨t, ht, htk, rfl⟩ := (hmemtake y).mp hy
    rcases Nat.lt_or_ge t k with hlt | hge
    · exact absurd ⟨ht, hadjy⟩ (hmin t hlt)
    · have : t = k := by omega
      subst this
      rfl
  · constructor
    · intro hw
      obtain ⟨t, ht, htk, htw⟩ := (hmemtake w).mp hw
      have hteq : t = p.length - 1 := by
        rw [← hlast] at htw
        exact hnd.getElem_inj_iff.mp htw
      have : k = p.length - 1 := by omega
      subst this
      exact hlast
    · intro hkw
      rw [hmemtake]
      exact ⟨k, hk, le_refl k, hkw⟩
  · intro t ht hadjt
    by_contra hlt
    exact hmin t (by omega) ⟨ht, hadjt⟩

/-- Greatest index below `n` satisfying a predicate. -/
theorem exists_greatest {Q : ℕ → Prop} : ∀ (n : ℕ), (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
  intro n
  induction n with
  | zero => rintro ⟨k, hk, -⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro hex
    by_cases hQ : Q n
    · exact ⟨n, by omega, hQ, fun m hm _ => by omega⟩
    · have hex' : ∃ k, k < n ∧ Q k := by
        obtain ⟨k, hk, hQk⟩ := hex
        refine ⟨k, ?_, hQk⟩
        rcases (by omega : k < n ∨ k = n) with h | h
        · exact h
        · exact absurd (h ▸ hQk) hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      refine ⟨k, by omega, hQk, ?_⟩
      intro m hm hQm
      rcases (by omega : m < n ∨ m = n) with h | h
      · exact hmax m h hQm
      · exact absurd (h ▸ hQm) hQ

/-- **The paper's `dᵢ` and `Dᵢ`.**  Mirror of `first_attach`: `p[k]` is the neighbour of `v`
on `p` closest to `w`, and `p.drop k` is the sub-path `d-p-w`. -/
theorem last_attach {G : SimpleGraph V} {p : List V} {u w v : V}
    (hp : IsPathFrom G p u w) (hex : ∃ x ∈ p, G.Adj v x) :
    ∃ (k : ℕ) (hk : k < p.length),
      IsPathFrom G (p.drop k) (p[k]'hk) w ∧
      G.Adj v (p[k]'hk) ∧
      (∀ y ∈ p.drop k, y ∈ p) ∧
      (∀ y ∈ p.drop k, G.Adj v y → y = p[k]'hk) ∧
      (u ∈ p.drop k ↔ p[k]'hk = u) ∧
      (∀ (t : ℕ) (ht : t < p.length), G.Adj v (p[t]'ht) → t ≤ k) := by
  classical
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have hnd : p.Nodup := hp.1.2.1
  obtain ⟨k, hk, ⟨hk', hadj⟩, hmax⟩ :
      ∃ k, k < p.length ∧ (∃ h : k < p.length, G.Adj v (p[k]'h)) ∧
        ∀ m, m < p.length → (∃ h : m < p.length, G.Adj v (p[m]'h)) → m ≤ k := by
    refine exists_greatest p.length ?_
    obtain ⟨x, hxp, hadjx⟩ := hex
    obtain ⟨jj, hj, hjx⟩ := List.getElem_of_mem hxp
    exact ⟨jj, hj, hj, by rw [hjx]; exact hadjx⟩
  have hfirst : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hmemdrop : ∀ y : V, y ∈ p.drop k ↔ ∃ (s : ℕ) (hs : k + s < p.length),
      p[k + s]'hs = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨t, ht, hty⟩ := List.getElem_of_mem hy
      have htlen : t < p.length - k := by simpa using ht
      exact ⟨t, by omega, by rw [← hty]; exact (List.getElem_drop ..).symm⟩
    · rintro ⟨s, hs, rfl⟩
      have hlt : s < (p.drop k).length := by rw [List.length_drop]; omega
      have he : (p.drop k)[s]'hlt = p[k + s]'hs := List.getElem_drop ..
      rw [← he]
      exact List.getElem_mem _
  refine ⟨k, hk, ⟨PathBasics.isPathList_drop hp.1 hk, ?_, ?_⟩, hadj, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_drop, List.getElem?_eq_getElem hk]
  · rw [List.getLast?_drop, if_neg (by omega)]
    exact hp.2.2
  · intro y hy
    exact List.mem_of_mem_drop hy
  · intro y hy hadjy
    obtain ⟨s, hs, rfl⟩ := (hmemdrop y).mp hy
    have hle := hmax (k + s) hs ⟨hs, hadjy⟩
    have hs0 : s = 0 := by omega
    subst hs0
    simp
  · constructor
    · intro hu
      obtain ⟨s, hs, hsu⟩ := (hmemdrop u).mp hu
      rw [← hfirst] at hsu
      have hks := hnd.getElem_inj_iff.mp hsu
      have hk0 : k = 0 := by omega
      subst hk0
      rw [← hfirst]
    · intro hku
      rw [← hfirst] at hku
      have hk0 : k = 0 := hnd.getElem_inj_iff.mp hku
      subst hk0
      rw [hmemdrop]
      exact ⟨0, by omega, by rw [← hfirst]⟩
  · exact fun t ht hadjt => hmax t ht ⟨ht, hadjt⟩

/-! ### Slice bookkeeping -/

theorem mem_take_iff {p : List V} {k : ℕ} {y : V} :
    y ∈ p.take (k + 1) ↔ ∃ (t : ℕ) (ht : t < p.length), t ≤ k ∧ p[t]'ht = y := by
  constructor
  · intro hy
    obtain ⟨t, ht, hty⟩ := List.getElem_of_mem hy
    have htlen : t < min (k + 1) p.length := by simpa using ht
    exact ⟨t, by omega, by omega, by rw [← hty]; exact (List.getElem_take ..).symm⟩
  · rintro ⟨t, ht, htk, rfl⟩
    have hlt : t < (p.take (k + 1)).length := by rw [List.length_take]; omega
    have he : (p.take (k + 1))[t]'hlt = p[t]'ht := List.getElem_take ..
    rw [← he]
    exact List.getElem_mem _

theorem mem_take_iff' {p : List V} {k : ℕ} {y : V} :
    y ∈ p.take k ↔ ∃ (t : ℕ) (ht : t < p.length), t < k ∧ p[t]'ht = y := by
  constructor
  · intro hy
    obtain ⟨t, ht, hty⟩ := List.getElem_of_mem hy
    have htlen : t < min k p.length := by simpa using ht
    exact ⟨t, by omega, by omega, by rw [← hty]; exact (List.getElem_take ..).symm⟩
  · rintro ⟨t, ht, htk, rfl⟩
    have hlt : t < (p.take k).length := by rw [List.length_take]; omega
    have he : (p.take k)[t]'hlt = p[t]'ht := List.getElem_take ..
    rw [← he]
    exact List.getElem_mem _

theorem mem_drop_iff {p : List V} {k : ℕ} {y : V} :
    y ∈ p.drop k ↔ ∃ (s : ℕ) (hs : k + s < p.length), p[k + s]'hs = y := by
  constructor
  · intro hy
    obtain ⟨t, ht, hty⟩ := List.getElem_of_mem hy
    have htlen : t < p.length - k := by simpa using ht
    exact ⟨t, by omega, by rw [← hty]; exact (List.getElem_drop ..).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hlt : s < (p.drop k).length := by rw [List.length_drop]; omega
    have he : (p.drop k)[s]'hlt = p[k + s]'hs := List.getElem_drop ..
    rw [← he]
    exact List.getElem_mem _

/-- The paper's `Cᵢ`: the initial segment `u-p-p[k]`. -/
theorem take_pathFrom {G : SimpleGraph V} {p : List V} {u w : V} (hp : IsPathFrom G p u w)
    {k : ℕ} (hk : k < p.length) : IsPathFrom G (p.take (k + 1)) u (p[k]'hk) := by
  have hne : p ≠ [] := hp.1.1
  refine ⟨PathBasics.isPathList_take hp.1 (by omega), ?_, ?_⟩
  · obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [List.take_succ_cons]
    simpa using hp.2.1
  · have h := PathBasics.getLast?_slice p (i := 0) (j := k) (by omega) hk
    simpa using h

/-- The paper's `Dᵢ`: the final segment `p[k]-p-w`. -/
theorem drop_pathFrom {G : SimpleGraph V} {p : List V} {u w : V} (hp : IsPathFrom G p u w)
    {k : ℕ} (hk : k < p.length) : IsPathFrom G (p.drop k) (p[k]'hk) w :=
  ⟨PathBasics.isPathList_drop hp.1 hk,
   by rw [List.head?_drop, List.getElem?_eq_getElem hk],
   by rw [List.getLast?_drop, if_neg (by omega)]; exact hp.2.2⟩

/-- `VertexCanBeLinkedOntoTriangle` assembled from the three paths directly: the cross-edge
clauses are only needed in the forward direction, the backward direction being the triangle. -/
theorem link_direct {G : SimpleGraph V} {v a₁ a₂ a₃ : V} {p₁ p₂ p₃ : List V}
    (h1 : IsPathList G p₁) (h2 : IsPathList G p₂) (h3 : IsPathList G p₃)
    (d12 : ∀ x ∈ p₁, x ∉ p₂) (d13 : ∀ x ∈ p₁, x ∉ p₃) (d23 : ∀ x ∈ p₂, x ∉ p₃)
    (e1 : p₁.head? = some a₁ ∨ p₁.getLast? = some a₁)
    (e2 : p₂.head? = some a₂ ∨ p₂.getLast? = some a₂)
    (e3 : p₃.head? = some a₃ ∨ p₃.getLast? = some a₃)
    (t12 : G.Adj a₁ a₂) (t13 : G.Adj a₁ a₃) (t23 : G.Adj a₂ a₃)
    (c12 : ∀ x ∈ p₁, ∀ y ∈ p₂, G.Adj x y → x = a₁ ∧ y = a₂)
    (c13 : ∀ x ∈ p₁, ∀ y ∈ p₃, G.Adj x y → x = a₁ ∧ y = a₃)
    (c23 : ∀ x ∈ p₂, ∀ y ∈ p₃, G.Adj x y → x = a₂ ∧ y = a₃)
    (n1 : ∃ x ∈ p₁, G.Adj v x) (n2 : ∃ x ∈ p₂, G.Adj v x) (n3 : ∃ x ∈ p₃, G.Adj v x) :
    VertexCanBeLinkedOntoTriangle G v a₁ a₂ a₃ :=
  ⟨p₁, p₂, p₃, ⟨h1, h2, h3⟩, ⟨d12, d13, d23⟩, ⟨e1, e2, e3⟩,
    ⟨fun x hx y hy => ⟨c12 x hx y hy, by rintro ⟨rfl, rfl⟩; exact t12⟩,
     fun x hx y hy => ⟨c13 x hx y hy, by rintro ⟨rfl, rfl⟩; exact t13⟩,
     fun x hx y hy => ⟨c23 x hx y hy, by rintro ⟨rfl, rfl⟩; exact t23⟩⟩,
    ⟨n1, n2, n3⟩⟩

/-! ### Small combinatorial facts about `Fin 3` -/

theorem fin3_cases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem fin3_third : ∀ i j : Fin 3, i ≠ j → ∃ m : Fin 3, m ≠ i ∧ m ≠ j := by decide

theorem fin3_cover : ∀ i j m p : Fin 3, i ≠ j → m ≠ i → m ≠ j → (p = i ∨ p = j ∨ p = m) := by
  decide

theorem perm_of_three : ∀ i j m : Fin 3, i ≠ j → i ≠ m → j ≠ m →
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j ∧ σ 2 = m := by decide

/-! ### Claim (1), second linking: `c₁` nonadjacent to `d₁` -/

/-- PAPER (proof of 10.1, claim (1)): *"Suppose that `c₁` is nonadjacent to `d₁`.  Then since
`f₁` is not major, we may assume it has at most one neighbour in `A`, by exchanging `A` and `B`
if necessary; but it can be linked onto `A`, via `f₁-c₁-C₁-a₁`, `f₁-c₂-C₂-a₂` and
`f₁-d₁-D₁-b₁-b₃-R₃-a₃`, contrary to 2.4."*

`k0`, `k0'` are the indices on `R 0` of `c₁` and `d₁`, and `k1` the index on `R 1` of `c₂`.
`hgap` is *"`c₁` is nonadjacent to `d₁`"* (with `c₁ ≠ d₁`), and `hb1` is the `c₂ ≠ b₂` the
printed proof has already established. -/
theorem link_nonadjacent {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hA1 : ∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (a i) ∧ G.Adj v (a j)))
    {k0 k0' k1 : ℕ} (hk0 : k0 < (R 0).length) (hk0' : k0' < (R 0).length)
    (hk1 : k1 < (R 1).length)
    (hc0 : G.Adj v ((R 0)[k0]'hk0)) (hd0 : G.Adj v ((R 0)[k0']'hk0'))
    (hc1 : G.Adj v ((R 1)[k1]'hk1))
    (hgap : k0 + 1 < k0')
    (hb1 : (R 1)[k1]'hk1 ≠ b 1) : False := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  -- `b₁ ∉ C₁`, `a₁ ∉ D₁`, `b₂ ∉ C₂`
  have hb0nt : b 0 ∉ (R 0).take (k0 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 0).length - 1 := hnd0.getElem_inj_iff.mp (by rw [hte, hlast0])
    omega
  have ha0nd : a 0 ∉ (R 0).drop k0' := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : k0' + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have hb1nt : b 1 ∉ (R 1).take (k1 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 1).length - 1 := hnd1.getElem_inj_iff.mp (by rw [hte, hlast1])
    exact hb1 ((hnd1.getElem_inj_iff.mpr (by omega : k1 = t)).trans hte)
  have hdisjTD : ∀ y ∈ (R 0).take (k0 + 1), y ∉ (R 0).drop k0' := by
    intro y hy hy'
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hy
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hy'
    have heq : t = k0' + s := hnd0.getElem_inj_iff.mp (by rw [hte, hse])
    omega
  -- `D₁-b₁-b₃-R₃-a₃`
  have hdisjD2 : ∀ x ∈ (R 0).drop k0', x ∉ (R 2).reverse := by
    intro x hx hx2
    rw [List.mem_reverse] at hx2
    exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) hx2
  have hcrossD : ∀ x ∈ (R 0).drop k0', ∀ y ∈ (R 2).reverse,
      (G.Adj x y ↔ (x = b 0 ∧ y = b 2)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    rw [hedge 0 2 (by decide) x (List.mem_of_mem_drop hx) y hy]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact absurd (h1 ▸ hx) ha0nd
      · exact h
    · intro h; exact Or.inr h
  have hP3 : IsPathFrom G ((R 0).drop k0' ++ (R 2).reverse) ((R 0)[k0']'hk0') (a 2) :=
    PathGlue.glue_path (drop_pathFrom (hp 0) hk0')
      (PathBasics.isPathFrom_reverse (hp 2)) hdisjD2 hcrossD
  have hmemP3 : ∀ y : V, y ∈ (R 0).drop k0' ++ (R 2).reverse ↔
      (y ∈ (R 0).drop k0' ∨ y ∈ R 2) := by
    intro y; rw [List.mem_append, List.mem_reverse]
  -- the three cross-edge clauses
  have c12 : ∀ x ∈ (R 0).take (k0 + 1), ∀ y ∈ (R 1).take (k1 + 1),
      G.Adj x y → x = a 0 ∧ y = a 1 := by
    intro x hx y hy hadj
    rcases (hedge 0 1 (by decide) x (List.mem_of_mem_take hx) y
      (List.mem_of_mem_take hy)).mp hadj with h | h
    · exact h
    · exact absurd (h.1 ▸ hx) hb0nt
  have c13 : ∀ x ∈ (R 0).take (k0 + 1), ∀ y ∈ (R 0).drop k0' ++ (R 2).reverse,
      G.Adj x y → x = a 0 ∧ y = a 2 := by
    intro x hx y hy hadj
    rcases (hmemP3 y).mp hy with hyD | hy2
    · exfalso
      obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hx
      obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hyD
      have hh := (PathBasics.path_adj_iff (hp 0).1 ht hs).mp hadj
      omega
    · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_take hx) y hy2).mp hadj with h | h
      · exact h
      · exact absurd (h.1 ▸ hx) hb0nt
  have c23 : ∀ x ∈ (R 1).take (k1 + 1), ∀ y ∈ (R 0).drop k0' ++ (R 2).reverse,
      G.Adj x y → x = a 1 ∧ y = a 2 := by
    intro x hx y hy hadj
    rcases (hmemP3 y).mp hy with hyD | hy2
    · exfalso
      rcases (hedge 1 0 (by decide) x (List.mem_of_mem_take hx) y
        (List.mem_of_mem_drop hyD)).mp hadj with h | h
      · exact ha0nd (h.2 ▸ hyD)
      · exact hb1nt (h.1 ▸ hx)
    · rcases (hedge 1 2 (by decide) x (List.mem_of_mem_take hx) y hy2).mp hadj with h | h
      · exact h
      · exact absurd (h.1 ▸ hx) hb1nt
  have hlink := link_direct (v := v)
    (take_pathFrom (hp 0) hk0).1 (take_pathFrom (hp 1) hk1).1 hP3.1
    (fun x hx hx2 => paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
      (List.mem_of_mem_take hx) (List.mem_of_mem_take hx2))
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · exact hdisjTD x hx h
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) h)
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 0) (List.mem_of_mem_take hx)
          (List.mem_of_mem_drop h)
      · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) h)
    (Or.inl (take_pathFrom (hp 0) hk0).2.1) (Or.inl (take_pathFrom (hp 1) hk1).2.1)
    (Or.inr hP3.2.2)
    (hAtri 0 1 (by decide)) (hAtri 0 2 (by decide)) (hAtri 1 2 (by decide))
    c12 c13 c23
    ⟨(R 0)[k0]'hk0, PathBasics.getLast_mem (take_pathFrom (hp 0) hk0).2.2, hc0⟩
    ⟨(R 1)[k1]'hk1, PathBasics.getLast_mem (take_pathFrom (hp 1) hk1).2.2, hc1⟩
    ⟨(R 0)[k0']'hk0', (hmemP3 _).mpr
      (Or.inl (PathBasics.head_mem (drop_pathFrom (hp 0) hk0').2.1)), hd0⟩
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG v (a 0) (a 1) (a 2) hlink with h | h | h
  exacts [hA1 0 1 (by decide) h, hA1 0 2 (by decide) h, hA1 1 2 (by decide) h]

/-- The mirror image of `link_nonadjacent` under *"by exchanging `A` and `B` if necessary"*:
the linking of `f₁` onto `B` via `f₁-d₁-D₁-b₁`, `f₁-d₂-D₂-b₂` and `f₁-c₁-C₁-a₁-a₃-R₃-b₃`. -/
theorem link_nonadjacent_mirror {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hB1 : ∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (b i) ∧ G.Adj v (b j)))
    {k0 k0' k1' : ℕ} (hk0 : k0 < (R 0).length) (hk0' : k0' < (R 0).length)
    (hk1' : k1' < (R 1).length)
    (hc0 : G.Adj v ((R 0)[k0]'hk0)) (hd0 : G.Adj v ((R 0)[k0']'hk0'))
    (hd1 : G.Adj v ((R 1)[k1']'hk1'))
    (hgap : k0 + 1 < k0')
    (ha1 : (R 1)[k1']'hk1' ≠ a 1) : False := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hfirst1 : (R 1)[0]'(by have := hlen2 1; omega) = a 1 :=
    PathBasics.getElem_zero_of_head? (hp 1).2.1 (by have := hlen2 1; omega)
  have hk1pos : 1 ≤ k1' := by
    by_contra hcon
    exact ha1 ((hnd1.getElem_inj_iff.mpr (by omega : k1' = 0)).trans hfirst1)
  have ha0nd : a 0 ∉ (R 0).drop k0' := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : k0' + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have ha1nd : a 1 ∉ (R 1).drop k1' := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : k1' + s = 0 := hnd1.getElem_inj_iff.mp (by rw [hse, hfirst1])
    omega
  have hb0nt : b 0 ∉ (R 0).take (k0 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 0).length - 1 := hnd0.getElem_inj_iff.mp (by rw [hte, hlast0])
    omega
  have hdisjT2 : ∀ x ∈ ((R 0).take (k0 + 1)).reverse, x ∉ R 2 := by
    intro x hx hx2
    rw [List.mem_reverse] at hx
    exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) hx2
  have hcrossT2 : ∀ x ∈ ((R 0).take (k0 + 1)).reverse, ∀ y ∈ R 2,
      (G.Adj x y ↔ (x = a 0 ∧ y = a 2)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hx
    rw [hedge 0 2 (by decide) x (List.mem_of_mem_take hx) y hy]
    exact ⟨fun h => h.elim id (fun h1 => absurd (h1.1 ▸ hx) hb0nt), fun h => Or.inl h⟩
  have hP3 : IsPathFrom G (((R 0).take (k0 + 1)).reverse ++ R 2) ((R 0)[k0]'hk0) (b 2) :=
    PathGlue.glue_path (PathBasics.isPathFrom_reverse (take_pathFrom (hp 0) hk0))
      (hp 2) hdisjT2 hcrossT2
  have hmemP3 : ∀ y : V, y ∈ ((R 0).take (k0 + 1)).reverse ++ R 2 ↔
      (y ∈ (R 0).take (k0 + 1) ∨ y ∈ R 2) := by
    intro y; rw [List.mem_append, List.mem_reverse]
  have hlink := link_direct (v := v)
    (drop_pathFrom (hp 0) hk0').1 (drop_pathFrom (hp 1) hk1').1 hP3.1
    (fun x hx hx2 => paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
      (List.mem_of_mem_drop hx) (List.mem_of_mem_drop hx2))
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hx
        obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp h
        have heq : k0' + s = t := hnd0.getElem_inj_iff.mp (by rw [hse, hte])
        omega
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) h)
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 0)
          (List.mem_of_mem_drop hx) (List.mem_of_mem_take h)
      · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) h)
    (Or.inr (drop_pathFrom (hp 0) hk0').2.2) (Or.inr (drop_pathFrom (hp 1) hk1').2.2)
    (Or.inr hP3.2.2)
    (hBtri 0 1 (by decide)) (hBtri 0 2 (by decide)) (hBtri 1 2 (by decide))
    (fun x hx y hy hadj => by
      rcases (hedge 0 1 (by decide) x (List.mem_of_mem_drop hx) y
        (List.mem_of_mem_drop hy)).mp hadj with hh | hh
      · exact absurd (hh.1 ▸ hx) ha0nd
      · exact hh)
    (fun x hx y hy hadj => by
      rcases (hmemP3 y).mp hy with h | h
      · exfalso
        obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hx
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp h
        have hh := (PathBasics.path_adj_iff (hp 0).1 hs ht).mp hadj
        omega
      · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_drop hx) y h).mp hadj with hh | hh
        · exact absurd (hh.1 ▸ hx) ha0nd
        · exact hh)
    (fun x hx y hy hadj => by
      rcases (hmemP3 y).mp hy with h | h
      · exfalso
        rcases (hedge 1 0 (by decide) x (List.mem_of_mem_drop hx) y
          (List.mem_of_mem_take h)).mp hadj with hh | hh
        · exact ha1nd (hh.1 ▸ hx)
        · exact hb0nt (hh.2 ▸ h)
      · rcases (hedge 1 2 (by decide) x (List.mem_of_mem_drop hx) y h).mp hadj with hh | hh
        · exact absurd (hh.1 ▸ hx) ha1nd
        · exact hh)
    ⟨(R 0)[k0']'hk0', PathBasics.head_mem (drop_pathFrom (hp 0) hk0').2.1, hd0⟩
    ⟨(R 1)[k1']'hk1', PathBasics.head_mem (drop_pathFrom (hp 1) hk1').2.1, hd1⟩
    ⟨(R 0)[k0]'hk0, PathBasics.head_mem hP3.2.1, hc0⟩
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG v (b 0) (b 1) (b 2) hlink with h | h | h
  exacts [hB1 0 1 (by decide) h, hB1 0 2 (by decide) h, hB1 1 2 (by decide) h]

/-! ### Claim (1), first linking: `c₁ = d₁` -/

/-- PAPER (proof of 10.1, claim (1)): *"Suppose that `c₁ = d₁`.  Then we may assume that
`c₁ ∉ A` and `c₂ ≠ b₂`, by exchanging `A` and `B` if necessary; but then `c₁` can be linked
onto the triangle `A`, via the paths `c₁-C₁-a₁`, `c₁-f₁-c₂-C₂-a₂`, and `c₁-D₁-b₁-b₃-R₃-a₃`,
contrary to 2.4, since `c₁` has at most one neighbour in `A`."*

`c₁ = d₁` is `honly0`: `(R 0)[j0+1]` is the *only* attachment of `v` on `R 0`.  `hj0` is the
paper's `c₁ ∉ A`, and `hb1` its `c₂ ≠ b₂`. -/
theorem link_equal {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hvK : ∀ i : Fin 3, v ∉ R i)
    {j0 k1 : ℕ} (hk0 : j0 + 1 < (R 0).length) (hk1 : k1 < (R 1).length)
    (hc0 : G.Adj v ((R 0)[j0 + 1]'hk0)) (hc1 : G.Adj v ((R 1)[k1]'hk1))
    (honly0 : ∀ (t : ℕ) (ht : t < (R 0).length), G.Adj v ((R 0)[t]'ht) → t = j0 + 1)
    (hmin1 : ∀ (t : ℕ) (ht : t < (R 1).length), G.Adj v ((R 1)[t]'ht) → k1 ≤ t)
    (hno2 : ∀ x ∈ R 2, ¬ G.Adj v x)
    (hb1 : (R 1)[k1]'hk1 ≠ b 1) : False := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hj0 : j0 < (R 0).length := by omega
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  -- the linked vertex is `c₁ = (R 0)[j0+1]`
  have hb0nt : b 0 ∉ (R 0).take (j0 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 0).length - 1 := hnd0.getElem_inj_iff.mp (by rw [hte, hlast0])
    omega
  have ha0nd : a 0 ∉ (R 0).drop (j0 + 2) := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : j0 + 2 + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have hb1nt : b 1 ∉ (R 1).take (k1 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 1).length - 1 := hnd1.getElem_inj_iff.mp (by rw [hte, hlast1])
    exact hb1 ((hnd1.getElem_inj_iff.mpr (by omega : k1 = t)).trans hte)
  -- `v` has no neighbour on `C₁` and none on `D₁`
  have hvC1 : ∀ x ∈ (R 0).take (j0 + 1), ¬ G.Adj v x := by
    intro x hx hadj
    obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hx
    have := honly0 t ht hadj
    omega
  have hvD1 : ∀ x ∈ (R 0).drop (j0 + 2), ¬ G.Adj v x := by
    intro x hx hadj
    obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hx
    have := honly0 (j0 + 2 + s) hs hadj
    omega
  -- `P₂ = c₁-f₁-c₂-C₂-a₂` without its first vertex: `f₁-c₂-C₂-a₂`
  have hC1rev : IsPathFrom G (((R 1).take (k1 + 1)).reverse) ((R 1)[k1]'hk1) (a 1) :=
    PathBasics.isPathFrom_reverse (take_pathFrom (hp 1) hk1)
  have hP2 : IsPathFrom G (v :: ((R 1).take (k1 + 1)).reverse) v (a 1) := by
    refine PathAttach.isPathFrom_cons hC1rev hc1 ?_ ?_
    · rw [List.mem_reverse]
      exact fun hc => hvK 1 (List.mem_of_mem_take hc)
    · intro x hx hxne hadj
      rw [List.mem_reverse] at hx
      obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hx
      exact hxne ((hnd1.getElem_inj_iff.mpr (by have := hmin1 t ht hadj; omega : t = k1)))
  have hmemP2 : ∀ x : V, x ∈ v :: ((R 1).take (k1 + 1)).reverse ↔
      (x = v ∨ x ∈ (R 1).take (k1 + 1)) := by
    intro x; rw [List.mem_cons, List.mem_reverse]
  -- `P₃ = D₁-b₁-b₃-R₃-a₃` without its first vertex
  have hdisjD2 : ∀ x ∈ (R 0).drop (j0 + 2), x ∉ (R 2).reverse := by
    intro x hx hx2
    rw [List.mem_reverse] at hx2
    exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) hx2
  have hcrossD : ∀ x ∈ (R 0).drop (j0 + 2), ∀ y ∈ (R 2).reverse,
      (G.Adj x y ↔ (x = b 0 ∧ y = b 2)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    rw [hedge 0 2 (by decide) x (List.mem_of_mem_drop hx) y hy]
    exact ⟨fun h => h.elim (fun h1 => absurd (h1.1 ▸ hx) ha0nd) id, fun h => Or.inr h⟩
  have hmemP3 : ∀ y : V, y ∈ (R 0).drop (j0 + 2) ++ (R 2).reverse ↔
      (y ∈ (R 0).drop (j0 + 2) ∨ y ∈ R 2) := by
    intro y; rw [List.mem_append, List.mem_reverse]
  obtain ⟨hP3l, hP3e, hP3n⟩ :
      IsPathList G ((R 0).drop (j0 + 2) ++ (R 2).reverse) ∧
      ((R 0).drop (j0 + 2) ++ (R 2).reverse).getLast? = some (a 2) ∧
      (∃ x ∈ (R 0).drop (j0 + 2) ++ (R 2).reverse, G.Adj ((R 0)[j0 + 1]'hk0) x) := by
    by_cases hlt : j0 + 2 < (R 0).length
    · have hg := PathGlue.glue_path (drop_pathFrom (hp 0) hlt)
        (PathBasics.isPathFrom_reverse (hp 2)) hdisjD2 hcrossD
      refine ⟨hg.1, hg.2.2, ⟨(R 0)[j0 + 2]'hlt, ?_, ?_⟩⟩
      · rw [hmemP3]
        exact Or.inl (mem_drop_iff.mpr ⟨0, by omega, by congr 1⟩)
      · exact PathBasics.path_adj_succ (hp 0).1 hlt
    · have hnil : (R 0).drop (j0 + 2) = [] := List.drop_eq_nil_of_le (by omega)
      have hb0 : (R 0)[j0 + 1]'hk0 = b 0 :=
        (hnd0.getElem_inj_iff.mpr (by omega : j0 + 1 = (R 0).length - 1)).trans hlast0
      rw [hnil, List.nil_append]
      refine ⟨(PathBasics.isPathFrom_reverse (hp 2)).1,
        (PathBasics.isPathFrom_reverse (hp 2)).2.2, ⟨b 2, ?_, ?_⟩⟩
      · rw [List.mem_reverse]
        exact PathBasics.getLast_mem (hp 2).2.2
      · rw [hb0]
        exact hBtri 0 2 (by decide)
  -- the linkage of `c₁` onto `A`
  have hlink := link_direct (v := (R 0)[j0 + 1]'hk0)
    (take_pathFrom (hp 0) hj0).1 hP2.1 hP3l
    (fun x hx hx2 => by
      rcases (hmemP2 x).mp hx2 with rfl | h
      · exact hvK 0 (List.mem_of_mem_take hx)
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
          (List.mem_of_mem_take hx) (List.mem_of_mem_take h))
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hx
        obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp h
        have heq : t = j0 + 2 + s := hnd0.getElem_inj_iff.mp (by rw [hte, hse])
        omega
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) h)
    (fun x hx hx3 => by
      rcases (hmemP2 x).mp hx with rfl | hx1
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact hvK 0 (List.mem_of_mem_drop h)
        · exact hvK 2 h
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 0)
            (List.mem_of_mem_take hx1) (List.mem_of_mem_drop h)
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2)
            (List.mem_of_mem_take hx1) h)
    (Or.inl (take_pathFrom (hp 0) hj0).2.1) (Or.inr hP2.2.2) (Or.inr hP3e)
    (hAtri 0 1 (by decide)) (hAtri 0 2 (by decide)) (hAtri 1 2 (by decide))
    (fun x hx y hy hadj => by
      rcases (hmemP2 y).mp hy with rfl | h
      · exact absurd (hvC1 x hx hadj.symm) not_false
      · rcases (hedge 0 1 (by decide) x (List.mem_of_mem_take hx) y
          (List.mem_of_mem_take h)).mp hadj with hh | hh
        · exact hh
        · exact absurd (hh.1 ▸ hx) hb0nt)
    (fun x hx y hy hadj => by
      rcases (hmemP3 y).mp hy with h | h
      · exfalso
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hx
        obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp h
        have hh := (PathBasics.path_adj_iff (hp 0).1 ht hs).mp hadj
        omega
      · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_take hx) y h).mp hadj with hh | hh
        · exact hh
        · exact absurd (hh.1 ▸ hx) hb0nt)
    (fun x hx y hy hadj => by
      rcases (hmemP2 x).mp hx with rfl | hx1
      · exfalso
        rcases (hmemP3 y).mp hy with h | h
        · exact hvD1 y h hadj
        · exact hno2 y h hadj
      · rcases (hmemP3 y).mp hy with h | h
        · exfalso
          rcases (hedge 1 0 (by decide) x (List.mem_of_mem_take hx1) y
            (List.mem_of_mem_drop h)).mp hadj with hh | hh
          · exact ha0nd (hh.2 ▸ h)
          · exact hb1nt (hh.1 ▸ hx1)
        · rcases (hedge 1 2 (by decide) x (List.mem_of_mem_take hx1) y h).mp hadj with hh | hh
          · exact hh
          · exact absurd (hh.1 ▸ hx1) hb1nt)
    ⟨(R 0)[j0]'hj0, PathBasics.getLast_mem (take_pathFrom (hp 0) hj0).2.2,
      (PathBasics.path_adj_succ (hp 0).1 hk0).symm⟩
    ⟨v, (hmemP2 v).mpr (Or.inl rfl), hc0.symm⟩
    hP3n
  -- `c₁` has at most one neighbour in `A`, contrary to 2.4
  have hnotA : ∀ i : Fin 3, i ≠ 0 → ¬ G.Adj ((R 0)[j0 + 1]'hk0) (a i) := by
    intro i hi hadj
    have hai : a i ∈ R i := PathBasics.head_mem (hp i).2.1
    rcases (hedge 0 i (Ne.symm hi) _ (List.getElem_mem hk0) (a i) hai).mp hadj with hh | hh
    · have h0 : (R 0)[j0 + 1]'hk0 = (R 0)[0]'(by omega) := by rw [hh.1, hfirst0]
      have := hnd0.getElem_inj_iff.mp h0
      omega
    · exact hABne i i hh.2
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG ((R 0)[j0 + 1]'hk0) (a 0) (a 1) (a 2) hlink
    with h | h | h
  exacts [hnotA 1 (by decide) h.2, hnotA 2 (by decide) h.2, hnotA 1 (by decide) h.1]

/-- The mirror image of `link_equal` under the paper's *"by exchanging `A` and `B` if
necessary"*: the same linking, run with the two triangles interchanged (so the three paths are
`c₁-D₁-b₁`, `c₁-f₁-d₂-D₂-b₂` and `c₁-C₁-a₁-a₃-R₃-b₃`, and the triangle is `B`). -/
theorem link_equal_mirror {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hvK : ∀ i : Fin 3, v ∉ R i)
    {m0 k1 : ℕ} (hm0lt : m0 < (R 0).length) (hm0 : m0 + 1 < (R 0).length)
    (hk1 : k1 < (R 1).length)
    (hc0 : G.Adj v ((R 0)[m0]'hm0lt)) (hc1 : G.Adj v ((R 1)[k1]'hk1))
    (honly0 : ∀ (t : ℕ) (ht : t < (R 0).length), G.Adj v ((R 0)[t]'ht) → t = m0)
    (hmax1 : ∀ (t : ℕ) (ht : t < (R 1).length), G.Adj v ((R 1)[t]'ht) → t ≤ k1)
    (hno2 : ∀ x ∈ R 2, ¬ G.Adj v x)
    (ha1 : (R 1)[k1]'hk1 ≠ a 1) : False := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hfirst1 : (R 1)[0]'(by have := hlen2 1; omega) = a 1 :=
    PathBasics.getElem_zero_of_head? (hp 1).2.1 (by have := hlen2 1; omega)
  have hk1pos : 1 ≤ k1 := by
    by_contra hcon
    exact ha1 ((hnd1.getElem_inj_iff.mpr (by omega : k1 = 0)).trans hfirst1)
  have ha0nd : a 0 ∉ (R 0).drop (m0 + 1) := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : m0 + 1 + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have ha1nd : a 1 ∉ (R 1).drop k1 := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : k1 + s = 0 := hnd1.getElem_inj_iff.mp (by rw [hse, hfirst1])
    omega
  have hb0nt : b 0 ∉ (R 0).take m0 := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff'.mp hmem
    have heq : t = (R 0).length - 1 := hnd0.getElem_inj_iff.mp (by rw [hte, hlast0])
    omega
  have hvT0 : ∀ x ∈ (R 0).take m0, ¬ G.Adj v x := by
    intro x hx hadj
    obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff'.mp hx
    have := honly0 t ht hadj
    omega
  have hvD0 : ∀ x ∈ (R 0).drop (m0 + 1), ¬ G.Adj v x := by
    intro x hx hadj
    obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hx
    have := honly0 (m0 + 1 + s) hs hadj
    omega
  -- `P₂ = f₁-d₂-D₂-b₂`
  have hP2 : IsPathFrom G (v :: (R 1).drop k1) v (b 1) := by
    refine PathAttach.isPathFrom_cons (drop_pathFrom (hp 1) hk1) hc1 ?_ ?_
    · exact fun hc => hvK 1 (List.mem_of_mem_drop hc)
    · intro x hx hxne hadj
      obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hx
      exact hxne (hnd1.getElem_inj_iff.mpr (by have := hmax1 (k1 + s) hs hadj; omega))
  have hmemP2 : ∀ x : V, x ∈ v :: (R 1).drop k1 ↔ (x = v ∨ x ∈ (R 1).drop k1) := by
    intro x; rw [List.mem_cons]
  -- `P₃ = C₁-a₁-a₃-R₃-b₃`
  have hmemP3 : ∀ y : V, y ∈ ((R 0).take m0).reverse ++ R 2 ↔
      (y ∈ (R 0).take m0 ∨ y ∈ R 2) := by
    intro y; rw [List.mem_append, List.mem_reverse]
  obtain ⟨hP3l, hP3e, hP3n⟩ :
      IsPathList G (((R 0).take m0).reverse ++ R 2) ∧
      (((R 0).take m0).reverse ++ R 2).getLast? = some (b 2) ∧
      (∃ x ∈ ((R 0).take m0).reverse ++ R 2, G.Adj ((R 0)[m0]'hm0lt) x) := by
    by_cases hpos : 1 ≤ m0
    · obtain ⟨i0, rfl⟩ : ∃ i0, m0 = i0 + 1 := ⟨m0 - 1, by omega⟩
      have hi0lt : i0 < (R 0).length := by omega
      have hrev : IsPathFrom G (((R 0).take (i0 + 1)).reverse) ((R 0)[i0]'hi0lt) (a 0) :=
        PathBasics.isPathFrom_reverse (take_pathFrom (hp 0) hi0lt)
      have hdisjT2 : ∀ x ∈ ((R 0).take (i0 + 1)).reverse, x ∉ R 2 := by
        intro x hx hx2
        rw [List.mem_reverse] at hx
        exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) hx2
      have hcrossT2 : ∀ x ∈ ((R 0).take (i0 + 1)).reverse, ∀ y ∈ R 2,
          (G.Adj x y ↔ (x = a 0 ∧ y = a 2)) := by
        intro x hx y hy
        rw [List.mem_reverse] at hx
        rw [hedge 0 2 (by decide) x (List.mem_of_mem_take hx) y hy]
        exact ⟨fun h => h.elim id (fun h1 => absurd (h1.1 ▸ hx) hb0nt), fun h => Or.inl h⟩
      have hg := PathGlue.glue_path hrev (hp 2) hdisjT2 hcrossT2
      refine ⟨hg.1, hg.2.2, ⟨(R 0)[i0]'hi0lt, ?_, ?_⟩⟩
      · rw [hmemP3]
        exact Or.inl (mem_take_iff'.mpr ⟨i0, hi0lt, by omega, rfl⟩)
      · exact (PathBasics.path_adj_succ (hp 0).1 hm0lt).symm
    · have hnil : (R 0).take m0 = [] := by
        rw [show m0 = 0 by omega]; simp
      have ha0 : (R 0)[m0]'hm0lt = a 0 :=
        (hnd0.getElem_inj_iff.mpr (by omega : m0 = 0)).trans hfirst0
      rw [hnil]
      simp only [List.reverse_nil, List.nil_append]
      exact ⟨(hp 2).1, (hp 2).2.2,
        ⟨a 2, PathBasics.head_mem (hp 2).2.1, by rw [ha0]; exact hAtri 0 2 (by decide)⟩⟩
  -- the linkage of `c₁` onto `B`
  have hlink := link_direct (v := (R 0)[m0]'hm0lt)
    (drop_pathFrom (hp 0) hm0).1 hP2.1 hP3l
    (fun x hx hx2 => by
      rcases (hmemP2 x).mp hx2 with rfl | h
      · exact hvK 0 (List.mem_of_mem_drop hx)
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
          (List.mem_of_mem_drop hx) (List.mem_of_mem_drop h))
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hx
        obtain ⟨t, ht, htk, hte⟩ := mem_take_iff'.mp h
        have heq : m0 + 1 + s = t := hnd0.getElem_inj_iff.mp (by rw [hse, hte])
        omega
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) h)
    (fun x hx hx3 => by
      rcases (hmemP2 x).mp hx with rfl | hx1
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact hvK 0 (List.mem_of_mem_take h)
        · exact hvK 2 h
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 0)
            (List.mem_of_mem_drop hx1) (List.mem_of_mem_take h)
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2)
            (List.mem_of_mem_drop hx1) h)
    (Or.inr (drop_pathFrom (hp 0) hm0).2.2) (Or.inr hP2.2.2) (Or.inr hP3e)
    (hBtri 0 1 (by decide)) (hBtri 0 2 (by decide)) (hBtri 1 2 (by decide))
    (fun x hx y hy hadj => by
      rcases (hmemP2 y).mp hy with rfl | h
      · exact absurd (hvD0 x hx hadj.symm) not_false
      · rcases (hedge 0 1 (by decide) x (List.mem_of_mem_drop hx) y
          (List.mem_of_mem_drop h)).mp hadj with hh | hh
        · exact absurd (hh.1 ▸ hx) ha0nd
        · exact hh)
    (fun x hx y hy hadj => by
      rcases (hmemP3 y).mp hy with h | h
      · exfalso
        obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hx
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff'.mp h
        have hh := (PathBasics.path_adj_iff (hp 0).1 hs ht).mp hadj
        omega
      · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_drop hx) y h).mp hadj with hh | hh
        · exact absurd (hh.1 ▸ hx) ha0nd
        · exact hh)
    (fun x hx y hy hadj => by
      rcases (hmemP2 x).mp hx with rfl | hx1
      · exfalso
        rcases (hmemP3 y).mp hy with h | h
        · exact hvT0 y h hadj
        · exact hno2 y h hadj
      · rcases (hmemP3 y).mp hy with h | h
        · exfalso
          rcases (hedge 1 0 (by decide) x (List.mem_of_mem_drop hx1) y
            (List.mem_of_mem_take h)).mp hadj with hh | hh
          · exact ha1nd (hh.1 ▸ hx1)
          · exact hb0nt (hh.2 ▸ h)
        · rcases (hedge 1 2 (by decide) x (List.mem_of_mem_drop hx1) y h).mp hadj with hh | hh
          · exact absurd (hh.1 ▸ hx1) ha1nd
          · exact hh)
    ⟨(R 0)[m0 + 1]'hm0, PathBasics.head_mem (drop_pathFrom (hp 0) hm0).2.1,
      PathBasics.path_adj_succ (hp 0).1 hm0⟩
    ⟨v, (hmemP2 v).mpr (Or.inl rfl), hc0.symm⟩
    hP3n
  have hnotB : ∀ i : Fin 3, i ≠ 0 → ¬ G.Adj ((R 0)[m0]'hm0lt) (b i) := by
    intro i hi hadj
    have hbi : b i ∈ R i := PathBasics.getLast_mem (hp i).2.2
    rcases (hedge 0 i (Ne.symm hi) _ (List.getElem_mem hm0lt) (b i) hbi).mp hadj with hh | hh
    · exact hABne i i hh.2.symm
    · have h0 : (R 0)[m0]'hm0lt = (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) := by
        rw [hh.1, hlast0]
      have := hnd0.getElem_inj_iff.mp h0
      omega
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG ((R 0)[m0]'hm0lt) (b 0) (b 1) (b 2) hlink
    with h | h | h
  exacts [hnotB 1 (by decide) h.2, hnotB 2 (by decide) h.2, hnotB 1 (by decide) h.1]

/-! ### Case B of claim (1): `X` meets all three paths -/

/-- PAPER (proof of 10.1, claim (1)): *"So we may assume that `X` meets all three of
`R₁, R₂, R₃`.  Since `f₁` is not major, we may assume that it has at most one neighbour in `A`,
by exchanging `A` and `B` if necessary, and therefore cannot be linked onto `A`.  Since it has
neighbours in all three of `R₁, R₂, R₃`, it follows that for at least two of these paths, the
only neighbour of `f₁` in this path is in `B`.  We may assume therefore that `c₁ = b₁` and
`c₂ = b₂`.  Since `X` is not local, `c₃ ≠ b₃`; but then statement 4 of the theorem holds."*

`hA1` is the *"at most one neighbour in `A`"* that the printed proof arranges by exchanging
`A` and `B`; the caller discharges that symmetry. -/
theorem case_all_three {G : SimpleGraph V} (hG : Berge G) {a b : Fin 3 → V} {R : Fin 3 → List V}
    {K X : Set V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {x : V | x ∈ R 0} ∪ {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2})
    (hXdef : ∀ x : V, x ∈ X ↔ (x ∈ K ∧ G.Adj x v))
    (hXloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) X)
    (hA1 : ∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (a i) ∧ G.Adj v (a j)))
    (hmeet : ∀ i : Fin 3, ∃ x ∈ R i, G.Adj v x) :
    _root_.Workspace.ProofLemmas.Thm101Assembly.Concl G a b R K [v] v v := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 : ∀ i : Fin 3, 2 ≤ (R i).length := two_le_length hprism
  have hRK : ∀ i : Fin 3, ∀ x : V, x ∈ R i → x ∈ K := by
    intro i x hx
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hKR : ∀ x : V, x ∈ K → ∃ i : Fin 3, x ∈ R i := by
    intro x hx
    rw [hK] at hx
    simp only [Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  choose k hk hCpath hCadj hCsub hCmin hCb hCglob using
    fun i : Fin 3 => first_attach (hp i) (hmeet i)
  -- if `cᵢ = bᵢ` then `bᵢ` is the *only* attachment of `v` on `Rᵢ`
  have honly : ∀ i : Fin 3, (R i)[k i]'(hk i) = b i → ∀ y ∈ R i, G.Adj v y → y = b i := by
    intro i hbi y hy hadj
    have hlast : (R i)[(R i).length - 1]'(by have := hlen2 i; omega) = b i :=
      PathBasics.getElem_last_of_getLast? (hp i).2.2 (by have := hlen2 i; omega)
    have heq : (R i)[k i]'(hk i) = (R i)[(R i).length - 1]'(by have := hlen2 i; omega) := by
      rw [hbi, hlast]
    have hkeq : k i = (R i).length - 1 := (hp i).1.2.1.getElem_inj_iff.mp heq
    have hteq : (R i).take (k i + 1) = R i := by
      rw [show k i + 1 = (R i).length by have := hlen2 i; omega]
      exact List.take_length
    rw [← hbi]
    exact hCmin i y (by rw [hteq]; exact hy) hadj
  -- at least two of the three paths have `bᵢ` as their only attachment
  have htwo : ∃ i j : Fin 3, i ≠ j ∧
      (R i)[k i]'(hk i) = b i ∧ (R j)[k j]'(hk j) = b j := by
    by_contra hcon
    have hb : ∀ i j : Fin 3, i ≠ j →
        b i ∈ (R i).take (k i + 1) → b j ∉ (R j).take (k j + 1) := by
      intro i j hij hbi hbj
      exact hcon ⟨i, j, hij, (hCb i).mp hbi, (hCb j).mp hbj⟩
    have hlink := link_onto_A hprism v (fun i => (R i).take (k i + 1))
      (fun i => PathBasics.isPathList_take (hp i).1 (by omega))
      (fun i y hy => hCsub i y hy)
      (fun i => Or.inl (hCpath i).2.1) hb
      (fun i => ⟨(R i)[k i]'(hk i), PathBasics.getLast_mem (hCpath i).2.2, hCadj i⟩)
    rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG v (a 0) (a 1) (a 2) hlink with
        h | h | h
    exacts [hA1 0 1 (by decide) h, hA1 0 2 (by decide) h, hA1 1 2 (by decide) h]
  obtain ⟨i, j, hij, hbi, hbj⟩ := htwo
  obtain ⟨m, hmi, hmj⟩ := fin3_third i j hij
  have hvb : ∀ t : Fin 3, (R t)[k t]'(hk t) = b t → G.Adj v (b t) := by
    intro t ht
    obtain ⟨x, hx, hadjx⟩ := hmeet t
    rw [← honly t ht x hx hadjx]
    exact hadjx
  -- "Since X is not local, c₃ ≠ b₃"
  obtain ⟨y, hyR, hyadj, hyne⟩ : ∃ y : V, y ∈ R m ∧ G.Adj v y ∧ y ≠ b m := by
    by_contra hcon
    apply hXloc
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    intro x hxX
    obtain ⟨hxK, hxadj⟩ := (hXdef x).mp hxX
    obtain ⟨t, hxt⟩ := hKR x hxK
    have hxb : x = b t := by
      rcases fin3_cover i j m t hij hmi hmj with rfl | rfl | rfl
      · exact honly t hbi x hxt hxadj.symm
      · exact honly t hbj x hxt hxadj.symm
      · by_contra hne
        exact hcon ⟨x, hxt, hxadj.symm, hne⟩
    rw [hxb]
    rcases fin3_cases t with rfl | rfl | rfl <;> simp
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := perm_of_three i j m hij (Ne.symm hmi) (Ne.symm hmj)
  refine ⟨fun t => b (σ t), fun t => a (σ t), fun t => R (σ t), σ, rfl,
    Or.inr ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ⟨?_, ?_, ⟨y, ?_, ?_, ?_⟩, ?_⟩))⟩
  · show G.Adj v (b (σ 0)); rw [hσ0]; exact hvb i hbi
  · show G.Adj v (b (σ 1)); rw [hσ1]; exact hvb j hbj
  · show y ∈ R (σ 2); rw [hσ2]; exact hyR
  · show y ≠ b (σ 2); rw [hσ2]; exact hyne
  · exact hyadj
  · intro x hx kk hkkK hkkne hadj
    have hxv : x = v := by simpa using hx
    subst hxv
    obtain ⟨t, hkt⟩ := hKR kk hkkK
    rcases fin3_cover i j m t hij hmi hmj with rfl | rfl | rfl
    · refine Or.inl ⟨rfl, Or.inl ?_⟩
      show kk = b (σ 0)
      rw [hσ0]
      exact honly t hbi kk hkt hadj
    · refine Or.inl ⟨rfl, Or.inr ?_⟩
      show kk = b (σ 1)
      rw [hσ1]
      exact honly t hbj kk hkt hadj
    · refine Or.inr ⟨rfl, ?_⟩
      show kk ∈ R (σ 2)
      rw [hσ2]
      exact hkt

/-! ### Case A of claim (1): `X` meets exactly two of the three paths -/

/-- PAPER (proof of 10.1, claim (1)): *"Suppose that `c₁ = d₁`.  Then we may assume that
`c₁ ∉ A` and `c₂ ≠ b₂`, by exchanging `A` and `B` if necessary; but then `c₁` can be linked
onto the triangle `A` … contrary to 2.4.  So `c₁` is different from `d₁`."*

Conclusion: `v` has **two distinct** attachments on `R 0`. -/
theorem two_attachments {G : SimpleGraph V} (hG : Berge G) {a b : Fin 3 → V}
    {R : Fin 3 → List V} {K X : Set V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {x : V | x ∈ R 0} ∪ {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2})
    (hXdef : ∀ x : V, x ∈ X ↔ (x ∈ K ∧ G.Adj x v))
    (hXloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) X)
    (hvK : ∀ i : Fin 3, v ∉ R i)
    (hmeet0 : ∃ x ∈ R 0, G.Adj v x) (hmeet1 : ∃ x ∈ R 1, G.Adj v x)
    (hno2 : ∀ x ∈ R 2, ¬ G.Adj v x) :
    ∃ x ∈ R 0, ∃ y ∈ R 0, x ≠ y ∧ G.Adj v x ∧ G.Adj v y := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst1 : (R 1)[0]'(by have := hlen2 1; omega) = a 1 :=
    PathBasics.getElem_zero_of_head? (hp 1).2.1 (by have := hlen2 1; omega)
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  have hKR : ∀ x : V, x ∈ K → ∃ i : Fin 3, x ∈ R i := by
    intro x hx
    rw [hK] at hx
    simp only [Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hXR : ∀ x : V, x ∈ X → (x ∈ R 0 ∨ x ∈ R 1) ∧ G.Adj v x := by
    intro x hxX
    obtain ⟨hxK, hxadj⟩ := (hXdef x).mp hxX
    obtain ⟨i, hxi⟩ := hKR x hxK
    refine ⟨?_, hxadj.symm⟩
    rcases fin3_cases i with rfl | rfl | rfl
    · exact Or.inl hxi
    · exact Or.inr hxi
    · exact absurd hxadj.symm (hno2 x hxi)
  have hne : ∀ (S : List V) (m m' : ℕ) (hm : m < S.length) (hm' : m' < S.length),
      m = m' → S[m]'hm = S[m']'hm' := by
    intro S m m' hm hm' h; subst h; rfl
  obtain ⟨k0, hk0, hC0path, hc0adj, hC0sub, hC0min, hC0b, hk0min⟩ := first_attach (hp 0) hmeet0
  obtain ⟨k0', hk0', hD0path, hd0adj, hD0sub, hD0min, hD0a, hk0max⟩ := last_attach (hp 0) hmeet0
  obtain ⟨k1, hk1, hC1path, hc1adj, hC1sub, hC1min, hC1b, hk1min⟩ := first_attach (hp 1) hmeet1
  obtain ⟨k1', hk1', hD1path, hd1adj, hD1sub, hD1min, hD1a, hk1max⟩ := last_attach (hp 1) hmeet1
  have hk0le : k0 ≤ k0' := hk0min k0' hk0' hd0adj
  have hk1le : k1 ≤ k1' := hk1min k1' hk1' hd1adj
  rcases Nat.lt_or_ge k0 k0' with hlt | hge
  · exact ⟨(R 0)[k0]'hk0, List.getElem_mem _, (R 0)[k0']'hk0', List.getElem_mem _,
      fun hc => absurd (hnd0.getElem_inj_iff.mp hc) (by omega), hc0adj, hd0adj⟩
  exfalso
  have heq : k0 = k0' := by omega
  have honly0 : ∀ (t : ℕ) (ht : t < (R 0).length), G.Adj v ((R 0)[t]'ht) → t = k0 := by
    intro t ht hadj
    have h1 := hk0min t ht hadj
    have h2 := hk0max t ht hadj
    omega
  have honlyR0 : ∀ x ∈ R 0, G.Adj v x → x = (R 0)[k0]'hk0 := by
    intro x hx hadj
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    exact hnd0.getElem_inj_iff.mpr (honly0 t ht hadj)
  by_cases hbr1 : 1 ≤ k0 ∧ (R 1)[k1]'hk1 ≠ b 1
  · obtain ⟨j0, hj0⟩ : ∃ j0, k0 = j0 + 1 := ⟨k0 - 1, by omega⟩
    subst hj0
    exact link_equal hG hprism hvK hk0 hk1 hc0adj hc1adj honly0 hk1min hno2 hbr1.2
  by_cases hbr2 : k0 + 1 < (R 0).length ∧ (R 1)[k1']'hk1' ≠ a 1
  · exact link_equal_mirror hG hprism hvK hk0 hbr2.1 hk1' hc0adj hd1adj honly0 hk1max hno2
      hbr2.2
  apply hXloc
  rcases Nat.eq_zero_or_pos k0 with hk00 | hk0pos
  · have hd1a : (R 1)[k1']'hk1' = a 1 := by
      by_contra hcon
      exact hbr2 ⟨by have := hlen2 0; omega, hcon⟩
    have hk1'0 : k1' = 0 := hnd1.getElem_inj_iff.mp (by rw [hd1a, hfirst1])
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    intro x hxX
    obtain ⟨hx01, hxadj⟩ := hXR x hxX
    rcases hx01 with hx0 | hx1
    · rw [honlyR0 x hx0 hxadj, hne (R 0) k0 0 hk0 (by have := hlen2 0; omega) hk00, hfirst0]
      simp
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx1
      have := hk1max t ht hxadj
      rw [hne (R 1) t 0 ht (by have := hlen2 1; omega) (by omega), hfirst1]
      simp
  · have hc1b : (R 1)[k1]'hk1 = b 1 := by
      by_contra hcon
      exact hbr1 ⟨hk0pos, hcon⟩
    have hk1eq : k1 = (R 1).length - 1 := hnd1.getElem_inj_iff.mp (by rw [hc1b, hlast1])
    have hk0end : k0 + 1 = (R 0).length := by
      by_contra hcon
      refine hbr2 ⟨by omega, ?_⟩
      intro hd1a
      have hk1'0 : k1' = 0 := hnd1.getElem_inj_iff.mp (by rw [hd1a, hfirst1])
      have := hlen2 1
      omega
    have hc0b : (R 0)[k0]'hk0 = b 0 := by
      rw [hne (R 0) k0 ((R 0).length - 1) hk0 (by have := hlen2 0; omega) (by omega), hlast0]
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    intro x hxX
    obtain ⟨hx01, hxadj⟩ := hXR x hxX
    rcases hx01 with hx0 | hx1
    · rw [honlyR0 x hx0 hxadj, hc0b]
      simp
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx1
      have := hk1min t ht hxadj
      rw [hne (R 1) t ((R 1).length - 1) ht (by have := hlen2 1; omega) (by omega), hlast1]
      simp

/-- PAPER (proof of 10.1, claim (1)): *"Suppose that `c₁` is nonadjacent to `d₁`. … contrary to
2.4.  So `c₁, d₁` are adjacent."*  `k0`/`k0'` index `c₁`/`d₁` on `R 0`, `k1`/`k1'` index
`c₂`/`d₂` on `R 1`; `hk1lt` is the already-established `c₂ ≠ d₂`. -/
theorem ends_adjacent {G : SimpleGraph V} (hG : Berge G) {a b : Fin 3 → V}
    {R : Fin 3 → List V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hmajsplit : (∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (a i) ∧ G.Adj v (a j))) ∨
      (∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (b i) ∧ G.Adj v (b j))))
    {k0 k0' k1 k1' : ℕ} (hk0 : k0 < (R 0).length) (hk0' : k0' < (R 0).length)
    (hk1 : k1 < (R 1).length) (hk1' : k1' < (R 1).length)
    (hc0adj : G.Adj v ((R 0)[k0]'hk0)) (hd0adj : G.Adj v ((R 0)[k0']'hk0'))
    (hc1adj : G.Adj v ((R 1)[k1]'hk1)) (hd1adj : G.Adj v ((R 1)[k1']'hk1'))
    (hk1lt : k1 < k1') : k0' ≤ k0 + 1 := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hfirst1 : (R 1)[0]'(by have := hlen2 1; omega) = a 1 :=
    PathBasics.getElem_zero_of_head? (hp 1).2.1 (by have := hlen2 1; omega)
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  by_contra hcon
  have hgap : k0 + 1 < k0' := by omega
  have hc1neb : (R 1)[k1]'hk1 ≠ b 1 := by
    intro h
    have := hnd1.getElem_inj_iff.mp (h.trans hlast1.symm)
    omega
  have hd1nea : (R 1)[k1']'hk1' ≠ a 1 := by
    intro h
    have := hnd1.getElem_inj_iff.mp (h.trans hfirst1.symm)
    omega
  rcases hmajsplit with hA1 | hB1
  · exact link_nonadjacent hG hprism hA1 hk0 hk0' hk1 hc0adj hd0adj hc1adj hgap hc1neb
  · exact link_nonadjacent_mirror hG hprism hB1 hk0 hk0' hk1' hc0adj hd0adj hd1adj hgap hd1nea

/-- **Case A of claim (1)**: PAPER *"suppose it only meets `R₁` and `R₂`. … So `c₁, d₁` are
adjacent, and similarly so are `c₂, d₂`, but then statement 1 of the theorem holds."* -/
theorem case_two_paths {G : SimpleGraph V} (hG : Berge G) {a b : Fin 3 → V}
    {R : Fin 3 → List V} {K X : Set V} {v : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {x : V | x ∈ R 0} ∪ {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2})
    (hXdef : ∀ x : V, x ∈ X ↔ (x ∈ K ∧ G.Adj x v))
    (hXloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) X)
    (hvK : ∀ i : Fin 3, v ∉ R i)
    (hmaj : ¬ MajorForPrism G a b v)
    (hmeet0 : ∃ x ∈ R 0, G.Adj v x) (hmeet1 : ∃ x ∈ R 1, G.Adj v x)
    (hno2 : ∀ x ∈ R 2, ¬ G.Adj v x) :
    _root_.Workspace.ProofLemmas.Thm101Assembly.Concl G a b R K [v] v v := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hKR : ∀ x : V, x ∈ K → ∃ i : Fin 3, x ∈ R i := by
    intro x hx
    rw [hK] at hx
    simp only [Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  -- "since `f₁` is not major, we may assume it has at most one neighbour in `A`"
  have hmajsplit : (∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (a i) ∧ G.Adj v (a j))) ∨
      (∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (b i) ∧ G.Adj v (b j))) := by
    rcases not_and_or.mp hmaj with h | h
    · refine Or.inl (fun i j hij hcon => h ?_)
      have hsub : ({a i, a j} : Set V) ⊆ ({a 0, a 1, a 2} : Set V) ∩ G.neighborSet v := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨by rcases fin3_cases i with rfl | rfl | rfl <;> simp, hcon.1⟩
        · exact ⟨by rcases fin3_cases j with rfl | rfl | rfl <;> simp, hcon.2⟩
      calc 2 = ({a i, a j} : Set V).ncard := (Set.ncard_pair (hAtri i j hij).ne).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    · refine Or.inr (fun i j hij hcon => h ?_)
      have hsub : ({b i, b j} : Set V) ⊆ ({b 0, b 1, b 2} : Set V) ∩ G.neighborSet v := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨by rcases fin3_cases i with rfl | rfl | rfl <;> simp, hcon.1⟩
        · exact ⟨by rcases fin3_cases j with rfl | rfl | rfl <;> simp, hcon.2⟩
      calc 2 = ({b i, b j} : Set V).ncard := (Set.ncard_pair (hBtri i j hij).ne).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  -- the swapped labelling, used to run each step on `R 1` as well as on `R 0`
  have hs0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have hs1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have hs2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have hprism' := PrismSymmetry.formPrism_perm hprism (Equiv.swap (0 : Fin 3) 1)
  have hK' : K = {x : V | x ∈ R ((Equiv.swap (0 : Fin 3) 1) 0)} ∪
      {x : V | x ∈ R ((Equiv.swap (0 : Fin 3) 1) 1)} ∪
      {x : V | x ∈ R ((Equiv.swap (0 : Fin 3) 1) 2)} := by
    rw [hK]
    exact (PrismSymmetry.prismVertices_perm R (Equiv.swap (0 : Fin 3) 1)).symm
  have hXloc' : ¬ LocalForPrism (fun i => a ((Equiv.swap (0 : Fin 3) 1) i))
      (fun i => b ((Equiv.swap (0 : Fin 3) 1) i))
      (R ((Equiv.swap (0 : Fin 3) 1) 0)) (R ((Equiv.swap (0 : Fin 3) 1) 1))
      (R ((Equiv.swap (0 : Fin 3) 1) 2)) X :=
    fun h => hXloc ((PrismSymmetry.localForPrism_perm (Equiv.swap (0 : Fin 3) 1)).mp h)
  have hvK' : ∀ i : Fin 3, v ∉ R ((Equiv.swap (0 : Fin 3) 1) i) :=
    fun i => hvK ((Equiv.swap (0 : Fin 3) 1) i)
  -- the paper's `c₁, d₁, c₂, d₂`
  obtain ⟨k0, hk0, hC0path, hc0adj, hC0sub, hC0min, hC0b, hk0min⟩ := first_attach (hp 0) hmeet0
  obtain ⟨k0', hk0', hD0path, hd0adj, hD0sub, hD0min, hD0a, hk0max⟩ := last_attach (hp 0) hmeet0
  obtain ⟨k1, hk1, hC1path, hc1adj, hC1sub, hC1min, hC1b, hk1min⟩ := first_attach (hp 1) hmeet1
  obtain ⟨k1', hk1', hD1path, hd1adj, hD1sub, hD1min, hD1a, hk1max⟩ := last_attach (hp 1) hmeet1
  -- "So `c₁` is different from `d₁`, and similarly `c₂` is different from `d₂`"
  have hk0lt : k0 < k0' := by
    obtain ⟨x, hx, y, hy, hxy, hax, hay⟩ :=
      two_attachments hG hprism hK hXdef hXloc hvK hmeet0 hmeet1 hno2
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    have h1 := hk0min s hs hax
    have h2 := hk0max s hs hax
    have h3 := hk0min t ht hay
    have h4 := hk0max t ht hay
    rcases Nat.lt_or_ge k0 k0' with h | h
    · exact h
    · exact absurd (hnd0.getElem_inj_iff.mpr (by omega : s = t)) hxy
  have hk1lt : k1 < k1' := by
    obtain ⟨x, hx, y, hy, hxy, hax, hay⟩ :=
      two_attachments hG hprism' hK' hXdef hXloc' hvK'
        (by rw [hs0]; exact hmeet1) (by rw [hs1]; exact hmeet0)
        (by rw [hs2]; exact hno2)
    rw [hs0] at hx hy
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    have h1 := hk1min s hs hax
    have h2 := hk1max s hs hax
    have h3 := hk1min t ht hay
    have h4 := hk1max t ht hay
    rcases Nat.lt_or_ge k1 k1' with h | h
    · exact h
    · exact absurd (hnd1.getElem_inj_iff.mpr (by omega : s = t)) hxy
  -- "So `c₁, d₁` are adjacent, and similarly so are `c₂, d₂`"
  have hk0succ : k0' = k0 + 1 := by
    have := ends_adjacent hG hprism hmajsplit hk0 hk0' hk1 hk1' hc0adj hd0adj hc1adj hd1adj hk1lt
    omega
  have hmajsplit' : (∀ i j : Fin 3, i ≠ j →
        ¬ (G.Adj v ((fun i => a ((Equiv.swap (0 : Fin 3) 1) i)) i) ∧
           G.Adj v ((fun i => a ((Equiv.swap (0 : Fin 3) 1) i)) j))) ∨
      (∀ i j : Fin 3, i ≠ j →
        ¬ (G.Adj v ((fun i => b ((Equiv.swap (0 : Fin 3) 1) i)) i) ∧
           G.Adj v ((fun i => b ((Equiv.swap (0 : Fin 3) 1) i)) j))) := by
    rcases hmajsplit with h | h
    · exact Or.inl fun i j hij => h _ _ fun hc => hij ((Equiv.swap (0 : Fin 3) 1).injective hc)
    · exact Or.inr fun i j hij => h _ _ fun hc => hij ((Equiv.swap (0 : Fin 3) 1).injective hc)
  have hk1succ : k1' = k1 + 1 := by
    have h := ends_adjacent (R := fun i => R ((Equiv.swap (0 : Fin 3) 1) i))
      hG hprism' hmajsplit' hk1 hk1' hk0 hk0'
      hc1adj hd1adj hc0adj hd0adj hk0lt
    omega
  subst hk0succ
  subst hk1succ
  -- "but then statement 1 of the theorem holds"
  have hvnotK : v ∉ K := by
    intro hc
    obtain ⟨i, hi⟩ := hKR v hc
    exact hvK i hi
  have hf : IsPathFrom G [v] v v :=
    ⟨PathBasics.isPathList_singleton G v, by simp, by simp⟩
  have hno : ∀ x ∈ [v], ∀ k ∈ K, G.Adj x k →
      (x = v ∧ (k = (R 0)[k0]'hk0 ∨ k = (R 0)[k0 + 1]'hk0')) ∨
      (x = v ∧ (k = (R 1)[k1]'hk1 ∨ k = (R 1)[k1 + 1]'hk1')) := by
    intro x hx kk hkkK hadj
    have hxv : x = v := by simpa using hx
    subst hxv
    obtain ⟨i, hki⟩ := hKR kk hkkK
    rcases fin3_cases i with rfl | rfl | rfl
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hki
      have h1 := hk0min t ht hadj
      have h2 := hk0max t ht hadj
      rcases (by omega : t = k0 ∨ t = k0 + 1) with h | h
      · exact Or.inl ⟨rfl, Or.inl (hnd0.getElem_inj_iff.mpr h)⟩
      · exact Or.inl ⟨rfl, Or.inr (hnd0.getElem_inj_iff.mpr h)⟩
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hki
      have h1 := hk1min t ht hadj
      have h2 := hk1max t ht hadj
      rcases (by omega : t = k1 ∨ t = k1 + 1) with h | h
      · exact Or.inr ⟨rfl, Or.inl (hnd1.getElem_inj_iff.mpr h)⟩
      · exact Or.inr ⟨rfl, Or.inr (hnd1.getElem_inj_iff.mpr h)⟩
    · exact absurd hadj (hno2 kk hki)
  refine ⟨a, b, R, Equiv.refl (Fin 3), rfl, Or.inl ⟨rfl, rfl⟩,
    Or.inl ⟨(R 0)[k0]'hk0, (R 0)[k0 + 1]'hk0', List.getElem_mem _, List.getElem_mem _,
      PathBasics.path_adj_succ (hp 0).1 hk0', hc0adj, hd0adj,
      (R 1)[k1]'hk1, (R 1)[k1 + 1]'hk1', List.getElem_mem _, List.getElem_mem _,
      PathBasics.path_adj_succ (hp 1).1 hk1', hc1adj, hd1adj, hno, ?_⟩⟩
  exact _root_.Workspace.ProofLemmas.Thm101K4Appearance.appears_K4_of_case_one G hG a b R K [v] v v
    ((R 0)[k0]'hk0) ((R 0)[k0 + 1]'hk0') ((R 1)[k1]'hk1) ((R 1)[k1 + 1]'hk1')
    hprism hK hf (by
      intro x hx
      have hxv : x = v := by simpa using hx
      subst hxv
      simpa using hvnotK)
    (List.getElem_mem _) (List.getElem_mem _) (PathBasics.path_adj_succ (hp 0).1 hk0')
    hc0adj hd0adj
    (List.getElem_mem _) (List.getElem_mem _) (PathBasics.path_adj_succ (hp 1).1 hk1')
    hc1adj hd1adj hno

/-! ### Claim (1) itself -/

/-- *"we may assume it has at most one neighbour in `A`, by exchanging `A` and `B` if
necessary"* — the disjunction the exchange chooses between. -/
theorem maj_split {G : SimpleGraph V} {a b : Fin 3 → V} {v : V}
    (hAtri : ∀ i j : Fin 3, i ≠ j → G.Adj (a i) (a j))
    (hBtri : ∀ i j : Fin 3, i ≠ j → G.Adj (b i) (b j))
    (hmaj : ¬ MajorForPrism G a b v) :
    (∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (a i) ∧ G.Adj v (a j))) ∨
    (∀ i j : Fin 3, i ≠ j → ¬ (G.Adj v (b i) ∧ G.Adj v (b j))) := by
  rcases not_and_or.mp hmaj with h | h
  · refine Or.inl (fun i j hij hcon => h ?_)
    have hsub : ({a i, a j} : Set V) ⊆ ({a 0, a 1, a 2} : Set V) ∩ G.neighborSet v := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨by rcases fin3_cases i with rfl | rfl | rfl <;> simp, hcon.1⟩
      · exact ⟨by rcases fin3_cases j with rfl | rfl | rfl <;> simp, hcon.2⟩
    calc 2 = ({a i, a j} : Set V).ncard := (Set.ncard_pair (hAtri i j hij).ne).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  · refine Or.inr (fun i j hij hcon => h ?_)
    have hsub : ({b i, b j} : Set V) ⊆ ({b 0, b 1, b 2} : Set V) ∩ G.neighborSet v := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨by rcases fin3_cases i with rfl | rfl | rfl <;> simp, hcon.1⟩
      · exact ⟨by rcases fin3_cases j with rfl | rfl | rfl <;> simp, hcon.2⟩
    calc 2 = ({b i, b j} : Set V).ncard := (Set.ncard_pair (hBtri i j hij).ne).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- *"by exchanging `A` and `B` if necessary"*, at the level of the packaged conclusion. -/
theorem concl_swap_rev (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K : Set V) (f : List V) (f₁ fn : V)
    (h : _root_.Workspace.ProofLemmas.Thm101Assembly.Concl G b a (fun i => (R i).reverse) K f f₁ fn) :
    _root_.Workspace.ProofLemmas.Thm101Assembly.Concl G a b R K f f₁ fn := by
  obtain ⟨a', b', R', σ, hR', hab, hcase⟩ := h
  subst hR'
  exact ⟨a', b', fun i => R (σ i), σ, rfl, hab.symm, by
    simpa only [List.mem_reverse] using hcase⟩

/-- **10.1, claim (1)**: *"If `n = 1` then the theorem holds."* -/
theorem claim_one (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K F : Set V) (v : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFsingle : F = {v}) :
    Thm101Assembly.Concl G a b R K [v] v v := by
  classical
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hvF : v ∈ F := by rw [hFsingle]; rfl
  have hmajv : ¬ MajorForPrism G a b v := hFmaj v hvF
  have hvnotK : v ∉ K := hFK hvF
  have hRK : ∀ i : Fin 3, ∀ x : V, x ∈ R i → x ∈ K := by
    intro i x hx
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hKR : ∀ x : V, x ∈ K → ∃ i : Fin 3, x ∈ R i := by
    intro x hx
    rw [hK] at hx
    simp only [Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hvK : ∀ i : Fin 3, v ∉ R i := fun i hc => hvnotK (hRK i v hc)
  have hXdef : ∀ x : V, x ∈ attachments G F K ↔ (x ∈ K ∧ G.Adj x v) := by
    intro x
    constructor
    · rintro ⟨hxK, w, hw, hadj⟩
      rw [hFsingle] at hw
      exact ⟨hxK, by rwa [show w = v from hw] at hadj⟩
    · rintro ⟨hxK, hadj⟩
      exact ⟨hxK, v, hvF, hadj⟩
  have hmajsplit := maj_split hAtri hBtri hmajv
  -- "Since `X` is not local it meets at least two of the paths"
  have hone : ∀ i : Fin 3, (∀ j : Fin 3, j ≠ i → ∀ x ∈ R j, ¬ G.Adj v x) → False := by
    intro i hj
    apply hFloc
    have hsub : attachments G F K ⊆ {x : V | x ∈ R i} := by
      intro x hx
      obtain ⟨hxK, hadj⟩ := (hXdef x).mp hx
      obtain ⟨q, hq⟩ := hKR x hxK
      rcases eq_or_ne q i with rfl | hne
      · exact hq
      · exact absurd hadj.symm (hj q hne x hq)
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl hsub, Or.inr (Or.inl hsub), Or.inr (Or.inr (Or.inl hsub))]
  -- the "exactly two" branch, for any labelling of the three indices
  have hcase2 : ∀ σ : Equiv.Perm (Fin 3),
      (∃ x ∈ R (σ 0), G.Adj v x) → (∃ x ∈ R (σ 1), G.Adj v x) →
      (∀ x ∈ R (σ 2), ¬ G.Adj v x) →
      _root_.Workspace.ProofLemmas.Thm101Assembly.Concl G a b R K [v] v v := by
    intro σ hm0 hm1 hn2
    refine _root_.Workspace.ProofLemmas.Thm101Assembly.concl_perm σ ?_
    exact case_two_paths hG (PrismSymmetry.formPrism_perm hprism σ)
      (by rw [hK]; exact (PrismSymmetry.prismVertices_perm R σ).symm)
      hXdef (fun h => hFloc ((PrismSymmetry.localForPrism_perm σ).mp h))
      (fun i => hvK (σ i))
      (fun h => hmajv ((PrismSymmetry.majorForPrism_perm σ).mp h))
      hm0 hm1 hn2
  -- the "all three" branch
  have hcase3 : (∀ i : Fin 3, ∃ x ∈ R i, G.Adj v x) →
      _root_.Workspace.ProofLemmas.Thm101Assembly.Concl G a b R K [v] v v := by
    intro hm
    rcases hmajsplit with hA1 | hB1
    · exact case_all_three hG hprism hK hXdef hFloc hA1 hm
    · refine concl_swap_rev G a b R K [v] v v ?_
      exact case_all_three hG (PrismSymmetry.formPrism_swap hprism)
        (by rw [hK]; exact (PrismSymmetry.prismVertices_reverse (R 0) (R 1) (R 2)).symm)
        hXdef (fun h => hFloc (PrismSymmetry.localForPrism_swap.mp h)) hB1
        (fun i => by
          obtain ⟨x, hx, hadj⟩ := hm i
          exact ⟨x, List.mem_reverse.mpr hx, hadj⟩)
  by_cases h0 : ∃ x ∈ R 0, G.Adj v x
  · by_cases h1 : ∃ x ∈ R 1, G.Adj v x
    · by_cases h2 : ∃ x ∈ R 2, G.Adj v x
      · refine hcase3 (fun i => ?_)
        rcases fin3_cases i with rfl | rfl | rfl
        exacts [h0, h1, h2]
      · refine hcase2 (Equiv.refl (Fin 3)) h0 h1 ?_
        intro x hx hadj
        exact h2 ⟨x, hx, hadj⟩
    · by_cases h2 : ∃ x ∈ R 2, G.Adj v x
      · refine hcase2 (Equiv.swap (1 : Fin 3) 2)
          (by rw [show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide]; exact h0)
          (by rw [show (Equiv.swap (1 : Fin 3) 2) 1 = 2 from by decide]; exact h2) ?_
        rw [show (Equiv.swap (1 : Fin 3) 2) 2 = 1 from by decide]
        intro x hx hadj
        exact h1 ⟨x, hx, hadj⟩
      · exact absurd (fun j hj x hx hadj => by
          rcases fin3_cases j with rfl | rfl | rfl
          · exact hj rfl
          · exact h1 ⟨x, hx, hadj⟩
          · exact h2 ⟨x, hx, hadj⟩) (fun h => hone 0 h)
  · by_cases h1 : ∃ x ∈ R 1, G.Adj v x
    · by_cases h2 : ∃ x ∈ R 2, G.Adj v x
      · refine hcase2 (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (by rw [show (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 0 = 1 from by
            decide]; exact h1)
          (by rw [show (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 1 = 2 from by
            decide]; exact h2) ?_
        rw [show (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 2 = 0 from by decide]
        intro x hx hadj
        exact h0 ⟨x, hx, hadj⟩
      · exact absurd (fun j hj x hx hadj => by
          rcases fin3_cases j with rfl | rfl | rfl
          · exact h0 ⟨x, hx, hadj⟩
          · exact hj rfl
          · exact h2 ⟨x, hx, hadj⟩) (fun h => hone 1 h)
    · exact absurd (fun j hj x hx hadj => by
        rcases fin3_cases j with rfl | rfl | rfl
        · exact h0 ⟨x, hx, hadj⟩
        · exact h1 ⟨x, hx, hadj⟩
        · exact hj rfl) (fun h => hone 2 h)

end Workspace.ProofLemmas.Thm101ClaimOne
