import Mathlib
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.PriorWorkProofs.Tutte.Basic

/-!
# Tutte's group-flow theorem, Part II — the ℤ/k ⇔ integer k-flow equivalence

This file proves **Theorem II.1** of the group-flow theorem: for `k ≥ 1` and a finite
multigraph `G` with a fixed orientation `O`,

  `G` has a nowhere-zero `(ℤ/k)`-flow  ⟺  `G` has a nowhere-zero integer `k`-flow.

It is independent of Part I (the deletion–contraction / group-independence half).

## Structure

* `IntFlowReducesToZk` (Lemma 8, the easy `⇐`): reducing an integer `k`-flow mod `k`
  gives a nowhere-zero `(ℤ/k)`-flow.
* `ZkFlowLiftsToIntFlow` (Lemmas 9–11, the hard `⇒`): the finite-descent construction of
  an integer `k`-flow from a `(ℤ/k)`-flow.
* `zk_iff_int_k_flow` (Lemma 12): the equivalence, assembled from the two directions.
-/

open Graph Workspace.Types.Orientation
open scoped Graph

namespace Workspace.PriorWorkProofs.Tutte

variable {α β : Type*} {G : Graph α β} {O : Orientation G}

/-! ## Lemma 8 (`IntFlowReducesToZk`): mod-`k` reduction of an integer `k`-flow

`Int.cast : ℤ → ZMod k` is an additive homomorphism, so it pushes through the Kirchhoff
out/in sums; and `0 < |φ e| < k` forces `(φ e : ZMod k) ≠ 0`. -/

/-- **Lemma 8 (⇐ direction).** If `φ` is an integer `k`-flow of `G` w.r.t. `O`, then its
mod-`k` reduction `e ↦ (φ e : ZMod k)` is a nowhere-zero `(ℤ/k)`-flow of `G` w.r.t. `O`. -/
theorem IntFlowReducesToZk {k : ℕ} (hE : E(G).Finite) (O : Orientation G)
    (φ : β → ℤ) (hφ : G.IsIntegerKFlow O φ (k : ℤ)) :
    G.IsFlow O (fun e => ((φ e : ZMod k))) ∧ G.IsNowhereZero (fun e => ((φ e : ZMod k))) := by
  classical
  obtain ⟨hflow, hbound⟩ := hφ
  refine ⟨?_, ?_⟩
  · rw [Graph.isFlow_iff_finset_sum hE]
    rw [Graph.isFlow_iff_finset_sum hE] at hflow
    intro v hv
    have hv' := hflow v hv
    calc (∑ e ∈ hE.toFinset with O.tail e = v, ((φ e : ZMod k)))
        = (((∑ e ∈ hE.toFinset with O.tail e = v, φ e : ℤ)) : ZMod k) := by
            rw [Int.cast_sum]
      _ = (((∑ e ∈ hE.toFinset with O.head e = v, φ e : ℤ)) : ZMod k) := by rw [hv']
      _ = (∑ e ∈ hE.toFinset with O.head e = v, ((φ e : ZMod k))) := by rw [Int.cast_sum]
  · intro e he
    simp only
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have h1 : 0 < |φ e| := (hbound e he).1
    have h2 : |φ e| < (k : ℤ) := (hbound e he).2
    have hk : (k : ℤ) ∣ |φ e| := (dvd_abs _ _).mpr hdvd
    have := Int.le_of_dvd h1 hk
    omega

/-! ## Lemma B0′ (`IntFlowOrientationReversal`): single-edge reversal invariance

Reversing one edge `e₀` and negating its value (`twist`) sends an integer `k`-flow to an
integer `k`-flow for the reversed orientation: conservation is preserved by
`isFlow_reverseEdge_twist_iff`, and `|−x| = |x|` keeps the bound `0 < |·| < k`. -/

/-- **Lemma B0′ (single-edge form).** `twist e₀ φ` is an integer `k`-flow for `reverseEdge O e₀`
whenever `φ` is one for `O`. -/
theorem IntFlowReverseEdgeInvariance [DecidableEq β] {k : ℤ} (hE : E(G).Finite) (e₀ : β)
    (φ : β → ℤ) (hφ : G.IsIntegerKFlow O φ k) :
    G.IsIntegerKFlow (reverseEdge O e₀) (twist e₀ φ) k := by
  obtain ⟨hflow, hb⟩ := hφ
  refine ⟨(isFlow_reverseEdge_twist_iff hE e₀ φ).mpr hflow, ?_⟩
  intro e he
  have habs : |twist e₀ φ e| = |φ e| := by
    by_cases h : e = e₀ <;> simp [twist, h, abs_neg]
  rw [habs]
  exact hb e he

/-! ## Lemma 9 (`ZkFlowRepresentativeClaim`): positive integer representatives

Take `g e := (f e).val : ℤ`, the canonical representative in `[0, k-1]`. Since `f` is
nowhere-zero, `(f e).val ≠ 0`, so `g e ∈ [1, k-1]`, and `g e ≡ f e (mod k)` by construction. -/

/-- The canonical positive integer representative of a `(ZMod k)`-valued map: `e ↦ (f e).val`. -/
def zkRep {k : ℕ} (f : β → ZMod k) : β → ℤ := fun e => ((f e).val : ℤ)

/-- **Lemma 9.** For a nowhere-zero `(ℤ/k)`-flow `f` (`k ≥ 1`), the representative `zkRep f`
takes values in `[1, k-1]` on every edge and reduces mod `k` back to `f`. -/
theorem ZkFlowRepresentativeClaim {k : ℕ} (hk : 1 ≤ k) (f : β → ZMod k)
    (hnz : G.IsNowhereZero f) (e : β) (he : e ∈ E(G)) :
    1 ≤ zkRep f e ∧ zkRep f e ≤ (k : ℤ) - 1 ∧ ((zkRep f e : ℤ) : ZMod k) = f e := by
  haveI : NeZero k := ⟨by omega⟩
  have hval_lt : (f e).val < k := ZMod.val_lt (f e)
  have hne : f e ≠ 0 := hnz e he
  have hval_ne : (f e).val ≠ 0 := fun h => hne ((ZMod.val_eq_zero (f e)).mp h)
  refine ⟨?_, ?_, ?_⟩
  · simp only [zkRep]; omega
  · simp only [zkRep]; omega
  · simp only [zkRep]
    push_cast
    exact ZMod.natCast_zmod_val (f e)

/-! ## Integer imbalance and its mod-`k` vanishing (Lemma 9, second half)

The integer imbalance `b(v) := (out-sum of g at v) − (in-sum of g at v)`. For `g = zkRep f`
with `f` a `(ℤ/k)`-flow, every `b(v)` is a multiple of `k`, because `g` reduces to `f` mod `k`
on `E(G)` and `f` conserves at every vertex. -/

/-- The integer imbalance of `g` at `v`: net out-flow `out-sum − in-sum`. -/
noncomputable def imbalance (O : Orientation G) (g : β → ℤ) (v : α) : ℤ :=
  G.outSum O g v - G.inSum O g v

/-- **Lemma 9 (imbalance ≡ 0 (mod k)).** For a nowhere-zero `(ℤ/k)`-flow `f`, the integer
imbalance of `zkRep f` at any vertex is divisible by `k`. -/
theorem imbalance_dvd {k : ℕ} (hk : 1 ≤ k) (hE : E(G).Finite) (O : Orientation G)
    (f : β → ZMod k) (hflow : G.IsFlow O f) (hnz : G.IsNowhereZero f) (v : α) (hv : v ∈ V(G)) :
    (k : ℤ) ∣ imbalance O (zkRep f) v := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hout : ((G.outSum O (zkRep f) v : ℤ) : ZMod k) = G.outSum O f v := by
    rw [Graph.outSum_eq_finset_sum hE, Graph.outSum_eq_finset_sum hE, Int.cast_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Set.Finite.mem_toFinset] at he
    exact (ZkFlowRepresentativeClaim hk f hnz e (Graph.outEdgeSet_subset_edgeSet he)).2.2
  have hin : ((G.inSum O (zkRep f) v : ℤ) : ZMod k) = G.inSum O f v := by
    rw [Graph.inSum_eq_finset_sum hE, Graph.inSum_eq_finset_sum hE, Int.cast_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Set.Finite.mem_toFinset] at he
    exact (ZkFlowRepresentativeClaim hk f hnz e (Graph.inEdgeSet_subset_edgeSet he)).2.2
  simp only [imbalance, Int.cast_sub, hout, hin]
  rw [sub_eq_zero]
  exact hflow v hv

/-! ## Rerouting infrastructure for the finite-descent construction (Lemmas 9–11)

The following private development proves `ZkFlowLiftsToIntFlow` by the fixed-orientation
`g ↦ g − k` reroute: positive/negative integer representatives with `|g e| ∈ [1,k-1]`, a
sign-oriented reachability, a telescoping reroute that strictly decreases `Φ := ∑_v |b(v)|`,
and a finite descent to `Φ = 0`. -/

section Bal
variable [DecidableEq α]

/-- Integer imbalance in finite-sum form. -/
private noncomputable def bal (O : Orientation G) (hE : E(G).Finite) (g : β → ℤ) (v : α) : ℤ :=
  (∑ e ∈ hE.toFinset with O.tail e = v, g e) - (∑ e ∈ hE.toFinset with O.head e = v, g e)

/-- Single-edge update change to `bal`. -/
private lemma bal_update [DecidableEq β] (hE : E(G).Finite) (g : β → ℤ) (e₀ : β) (he₀ : e₀ ∈ E(G))
    (c : ℤ) (p : α) :
    bal O hE (Function.update g e₀ c) p
      = bal O hE g p
        + (if O.tail e₀ = p then c - g e₀ else 0)
        - (if O.head e₀ = p then c - g e₀ else 0) := by
  have hmem : e₀ ∈ hE.toFinset := (Set.Finite.mem_toFinset hE).mpr he₀
  have key : ∀ (t : β → α),
      (∑ e ∈ hE.toFinset with t e = p, Function.update g e₀ c e)
        = (∑ e ∈ hE.toFinset with t e = p, g e) + (if t e₀ = p then c - g e₀ else 0) := by
    intro t
    have step : ∀ e ∈ hE.toFinset.filter (fun e => t e = p),
        Function.update g e₀ c e = g e + (if e = e₀ then c - g e₀ else 0) := by
      intro e _
      by_cases h : e = e₀
      · subst h; rw [Function.update_self, if_pos rfl]; ring
      · rw [Function.update_of_ne h, if_neg h, add_zero]
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (hE.toFinset.filter (fun e => t e = p)) e₀ (fun _ => c - g e₀)]
    congr 1
    by_cases ht : t e₀ = p
    · rw [if_pos (by simp [Finset.mem_filter, hmem, ht]), if_pos ht]
    · rw [if_neg (by simp [Finset.mem_filter, ht]), if_neg ht]
  rw [bal, bal, key O.tail, key O.head]
  abel

end Bal

/-! ## Sign-oriented reroute -/

/-- Flip a nonzero integer across the modulus `k`: positive values drop by `k`,
negative values rise by `k`. Preserves `|·| ∈ [1,k-1]` and the class mod `k`. -/
private def rrVal (k : ℤ) (x : ℤ) : ℤ := if 0 < x then x - k else x + k

/-- Reroute the edges in `es` (each once) by `rrVal`. -/
private def reroute [DecidableEq β] (k : ℤ) (es : List β) (g : β → ℤ) : β → ℤ :=
  fun e => if e ∈ es then rrVal k (g e) else g e

/-- One sign-oriented step along edge `e` from `p` to `q`: either `e` is a positive edge
traversed tail→head, or a negative edge traversed head→tail. -/
private def SStepE (O : Orientation G) (g : β → ℤ) (e : β) (p q : α) : Prop :=
  e ∈ E(G) ∧ ((0 < g e ∧ O.tail e = p ∧ O.head e = q) ∨ (g e < 0 ∧ O.head e = p ∧ O.tail e = q))

/-- A sign-oriented walk: a chain of `SStepE` steps from `u` to `w` recording its edges. -/
private inductive SWalk (O : Orientation G) (g : β → ℤ) : α → List β → α → Prop
  | nil (u : α) : SWalk O g u [] u
  | cons {u v w : α} {e : β} {es : List β} :
      SStepE O g e u v → SWalk O g v es w → SWalk O g u (e :: es) w

/-- **Telescoping.** Rerouting an edge-distinct sign-oriented walk from `u` to `w` shifts
imbalance by `-k` at `u` and `+k` at `w`, leaving every other vertex unchanged. -/
private lemma walk_bal [DecidableEq α] (hE : E(G).Finite) [DecidableEq β] (k : ℤ) (g : β → ℤ)
    {u : α} {es : List β} {w : α} (hw : SWalk O g u es w) :
    ∀ p, es.Nodup → bal O hE (reroute k es g) p
      = bal O hE g p + k * ((if w = p then (1:ℤ) else 0) - (if u = p then 1 else 0)) := by
  induction hw with
  | nil u =>
    intro p _
    have : reroute k ([] : List β) g = g := by
      funext e; simp [reroute]
    rw [this]; ring
  | @cons u v w e es' hstep hrest ih =>
    intro p hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨hnotin, hndes'⟩ := hnd
    have hdecomp : reroute k (e :: es') g
        = Function.update (reroute k es' g) e (rrVal k (g e)) := by
      funext e'
      by_cases h : e' = e
      · subst h; simp [reroute, Function.update_self]
      · simp only [reroute, Function.update_of_ne h, List.mem_cons, h, false_or]
    have he : e ∈ E(G) := hstep.1
    have hge : (reroute k es' g) e = g e := by simp [reroute, hnotin]
    rw [hdecomp, bal_update hE (reroute k es' g) e he (rrVal k (g e)) p, hge, ih p hndes']
    rcases hstep.2 with ⟨hpos, htail, hhead⟩ | ⟨hneg, hhead, htail⟩
    · rw [htail, hhead]
      simp only [rrVal, if_pos hpos]
      split_ifs <;> ring
    · rw [htail, hhead]
      simp only [rrVal, if_neg (not_lt.mpr hneg.le)]
      split_ifs <;> ring

/-! ## The potential Φ -/

/-- The total imbalance potential `Φ(g) = ∑_v |b(v)|`. -/
private noncomputable def Phi [DecidableEq α] (O : Orientation G) (hV : V(G).Finite) (hE : E(G).Finite)
    (g : β → ℤ) : ℕ :=
  ∑ v ∈ hV.toFinset, (bal O hE g v).natAbs

/-- If `Φ(g) = 0` then `g` is a flow. -/
private lemma flow_of_phi_zero [DecidableEq α] (hV : V(G).Finite) (hE : E(G).Finite) (g : β → ℤ)
    (h : Phi O hV hE g = 0) : G.IsFlow O g := by
  have hz : ∀ v ∈ hV.toFinset, (bal O hE g v).natAbs = 0 :=
    Finset.sum_eq_zero_iff.mp h
  rw [Graph.isFlow_iff_finset_sum hE]
  intro v hv
  have hvf : v ∈ hV.toFinset := (Set.Finite.mem_toFinset hV).mpr hv
  have : bal O hE g v = 0 := Int.natAbs_eq_zero.mp (hz v hvf)
  rw [bal, sub_eq_zero] at this
  exact this

/-- **Φ strictly decreases** on rerouting an edge-distinct walk from a positive-imbalance
vertex `u` to a negative-imbalance vertex `w` (both imbalances multiples of `k`). -/
private lemma reroute_decreases_phi [DecidableEq α] [DecidableEq β] (hV : V(G).Finite) (hE : E(G).Finite)
    (k : ℤ) (g : β → ℤ) {u : α} {es : List β} {w : α} (hw : SWalk O g u es w) (hnd : es.Nodup)
    (huV : u ∈ V(G)) (hwV : w ∈ V(G)) (hne : u ≠ w) (hk : 1 ≤ k)
    (hbu : 0 < bal O hE g u) (hbw : bal O hE g w < 0)
    (hdu : k ∣ bal O hE g u) (hdw : k ∣ bal O hE g w) :
    Phi O hV hE (reroute k es g) < Phi O hV hE g := by
  set s := hV.toFinset with hs
  have huf : u ∈ s := (Set.Finite.mem_toFinset hV).mpr huV
  have hwf : w ∈ s := (Set.Finite.mem_toFinset hV).mpr hwV
  have hwf' : w ∈ s.erase u := Finset.mem_erase.mpr ⟨hne.symm, hwf⟩
  -- values at u and w after rerouting
  have hbu' : bal O hE (reroute k es g) u = bal O hE g u - k := by
    rw [walk_bal hE k g hw u hnd]; rw [if_neg hne.symm, if_pos rfl]; ring
  have hbw' : bal O hE (reroute k es g) w = bal O hE g w + k := by
    rw [walk_bal hE k g hw w hnd]; rw [if_pos rfl, if_neg hne]; ring
  -- tail (off {u,w}) unchanged
  have htail : ∀ v ∈ (s.erase u).erase w,
      (bal O hE (reroute k es g) v).natAbs = (bal O hE g v).natAbs := by
    intro v hv
    rw [Finset.mem_erase, Finset.mem_erase] at hv
    obtain ⟨hvw, hvu, _⟩ := hv
    rw [walk_bal hE k g hw v hnd, if_neg (fun h => hvw h.symm), if_neg (fun h => hvu h.symm)]
    ring_nf
  -- expand Φ at u then w
  have expand : ∀ (f : α → ℕ),
      ∑ v ∈ s, f v = f u + (f w + ∑ v ∈ (s.erase u).erase w, f v) := by
    intro f
    rw [← Finset.add_sum_erase s f huf, ← Finset.add_sum_erase (s.erase u) f hwf']
  rw [Phi, Phi, expand (fun v => (bal O hE (reroute k es g) v).natAbs),
    expand (fun v => (bal O hE g v).natAbs)]
  rw [Finset.sum_congr rfl htail]
  -- reduce to the two endpoints
  have hkle_u : k ≤ bal O hE g u := Int.le_of_dvd hbu hdu
  have hkle_w : k ≤ -bal O hE g w := Int.le_of_dvd (by omega) ((dvd_neg).mpr hdw)
  simp only [hbu', hbw']
  omega

/-! ## The invariant INV -/

/-- The rerouting invariant: `g` reduces to `f` mod `k` on edges, has `|g e| ∈ [1,k-1]` there,
and vanishes off `E(G)`. -/
private def INV (O : Orientation G) (k : ℕ) (f : β → ZMod k) (g : β → ℤ) : Prop :=
  (∀ e ∈ E(G), 1 ≤ |g e| ∧ |g e| ≤ (k:ℤ) - 1 ∧ ((g e : ℤ) : ZMod k) = f e) ∧ (∀ e ∉ E(G), g e = 0)

/-- Every edge of a sign-oriented walk is an edge of `G`. -/
private lemma SWalk_edges_mem (g : β → ℤ) {u : α} {es : List β} {w : α} (hw : SWalk O g u es w) :
    ∀ e ∈ es, e ∈ E(G) := by
  induction hw with
  | nil u => intro e he; simp at he
  | @cons u v w e es' hstep hrest ih =>
    intro e' he'
    rw [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact hstep.1
    · exact ih e' he'

/-- Rerouting preserves INV (each rerouted edge's value flips across the modulus). -/
private lemma reroute_INV [DecidableEq β] (k : ℕ) (hk : 1 ≤ k) (f : β → ZMod k) (g : β → ℤ)
    (hinv : INV O k f g) (es : List β) (hes : ∀ e ∈ es, e ∈ E(G)) :
    INV O k f (reroute (k:ℤ) es g) := by
  have hk' : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
  obtain ⟨hon, hoff⟩ := hinv
  constructor
  · intro e he
    by_cases hmem : e ∈ es
    · simp only [reroute, if_pos hmem]
      obtain ⟨h1, h2, h3⟩ := hon e he
      have hne : g e ≠ 0 := by rintro h; rw [h] at h1; norm_num at h1
      have hb1 : -((k:ℤ) - 1) ≤ g e := (abs_le.mp h2).1
      have hb2 : g e ≤ (k:ℤ) - 1 := (abs_le.mp h2).2
      have hbound : 1 ≤ |rrVal (k:ℤ) (g e)| ∧ |rrVal (k:ℤ) (g e)| ≤ (k:ℤ) - 1 := by
        rw [rrVal]
        split_ifs with hp
        · rw [abs_of_nonpos (by omega)]; omega
        · rw [abs_of_nonneg (by omega)]; omega
      refine ⟨hbound.1, hbound.2, ?_⟩
      have hcl : ((rrVal (k:ℤ) (g e) : ℤ) : ZMod k) = ((g e : ℤ) : ZMod k) := by
        rw [rrVal]; split_ifs <;> push_cast <;> simp [ZMod.natCast_self]
      rw [hcl]; exact h3
    · simp only [reroute, if_neg hmem]; exact hon e he
  · intro e he
    simp only [reroute, if_neg (fun hmem => he (hes e hmem))]
    exact hoff e he

/-! ## Divisibility and vanishing of the total imbalance -/

/-- Every vertex imbalance of an INV-map is a multiple of `k`. -/
private lemma bal_dvd [DecidableEq α] (hE : E(G).Finite) (k : ℕ) (f : β → ZMod k)
    (hflow : G.IsFlow O f) (g : β → ℤ) (hclass : ∀ e ∈ E(G), ((g e : ℤ) : ZMod k) = f e)
    (v : α) (hv : v ∈ V(G)) : (k:ℤ) ∣ bal O hE g v := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [bal]
  have htail : ((∑ e ∈ hE.toFinset with O.tail e = v, g e : ℤ) : ZMod k)
      = ∑ e ∈ hE.toFinset with O.tail e = v, f e := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at he
    exact hclass e he.1
  have hhead : ((∑ e ∈ hE.toFinset with O.head e = v, g e : ℤ) : ZMod k)
      = ∑ e ∈ hE.toFinset with O.head e = v, f e := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at he
    exact hclass e he.1
  rw [Int.cast_sub, htail, hhead, sub_eq_zero]
  exact (Graph.isFlow_iff_finset_sum hE).mp hflow v hv

/-- The total imbalance over all vertices vanishes. -/
private lemma sum_bal_zero [DecidableEq α] (hV : V(G).Finite) (hE : E(G).Finite) (g : β → ℤ) :
    ∑ v ∈ hV.toFinset, bal O hE g v = 0 := by
  simp only [bal, Finset.sum_sub_distrib]
  have htail : ∑ v ∈ hV.toFinset, ∑ e ∈ hE.toFinset with O.tail e = v, g e
      = ∑ e ∈ hE.toFinset, g e := by
    apply Finset.sum_fiberwise_of_maps_to
    intro e he
    rw [Set.Finite.mem_toFinset] at he ⊢
    exact O.tail_mem he
  have hhead : ∑ v ∈ hV.toFinset, ∑ e ∈ hE.toFinset with O.head e = v, g e
      = ∑ e ∈ hE.toFinset, g e := by
    apply Finset.sum_fiberwise_of_maps_to
    intro e he
    rw [Set.Finite.mem_toFinset] at he ⊢
    exact O.head_mem he
  rw [htail, hhead, sub_self]

/-! ## Sign-oriented reachability -/

/-- Two sign-oriented walks concatenate. -/
private lemma SWalk.append (g : β → ℤ) {u v w : α} {es₁ es₂ : List β}
    (h1 : SWalk O g u es₁ v) (h2 : SWalk O g v es₂ w) :
    SWalk O g u (es₁ ++ es₂) w := by
  induction h1 with
  | nil u => simpa using h2
  | cons hstep hrest ih => exact SWalk.cons hstep (ih h2)

/-- Sign-oriented reachability: existence of some walk. -/
private def SReach (O : Orientation G) (g : β → ℤ) (u w : α) : Prop := ∃ es, SWalk O g u es w

private lemma SReach.refl (O : Orientation G) (g : β → ℤ) (u : α) : SReach O g u u := ⟨[], SWalk.nil u⟩

private lemma SReach.step {g : β → ℤ} {e : β} {u v : α} (h : SStepE O g e u v) : SReach O g u v :=
  ⟨[e], SWalk.cons h (SWalk.nil v)⟩

private lemma SReach.trans {g : β → ℤ} {u v w : α} (h1 : SReach O g u v) (h2 : SReach O g v w) :
    SReach O g u w := by
  obtain ⟨es₁, hw₁⟩ := h1
  obtain ⟨es₂, hw₂⟩ := h2
  exact ⟨_, hw₁.append g hw₂⟩

/-- **Min-cut / augmenting reachability.** From a vertex `u` with positive imbalance there is a
sign-oriented path to some vertex `w` with negative imbalance. -/
private lemma exists_neg_reachable [DecidableEq α] (hV : V(G).Finite) (hE : E(G).Finite) (g : β → ℤ)
    (u : α) (huV : u ∈ V(G)) (hbu : 0 < bal O hE g u) :
    ∃ w, w ∈ V(G) ∧ SReach O g u w ∧ bal O hE g w < 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  set X := hV.toFinset.filter (fun w => SReach O g u w) with hX
  have hnonneg : ∀ v ∈ X, 0 ≤ bal O hE g v := by
    intro v hv
    rw [hX, Finset.mem_filter, Set.Finite.mem_toFinset] at hv
    exact hcon v hv.1 hv.2
  have huX : u ∈ X := by
    rw [hX, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨huV, SReach.refl O g u⟩
  have hpos : 0 < ∑ v ∈ X, bal O hE g v :=
    lt_of_lt_of_le hbu (Finset.single_le_sum hnonneg huX)
  have hsum_le : ∑ v ∈ X, bal O hE g v ≤ 0 := by
    have e1 : ∑ v ∈ X, bal O hE g v
        = (∑ e ∈ hE.toFinset with O.tail e ∈ X, g e)
          - ∑ e ∈ hE.toFinset with O.head e ∈ X, g e := by
      simp only [bal, Finset.sum_sub_distrib]
      rw [Finset.sum_fiberwise_eq_sum_filter hE.toFinset X O.tail g,
          Finset.sum_fiberwise_eq_sum_filter hE.toFinset X O.head g]
    rw [e1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonpos
    intro e he
    rw [Set.Finite.mem_toFinset] at he
    by_cases htX : O.tail e ∈ X <;> by_cases hhX : O.head e ∈ X
    · simp [htX, hhX]
    · rw [if_pos htX, if_neg hhX, sub_zero]
      by_contra hgpos
      push_neg at hgpos
      apply hhX
      have hru : SReach O g u (O.tail e) := (Finset.mem_filter.mp htX).2
      have hstep : SStepE O g e (O.tail e) (O.head e) := ⟨he, Or.inl ⟨hgpos, rfl, rfl⟩⟩
      rw [hX, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨O.head_mem he, hru.trans (SReach.step hstep)⟩
    · rw [if_neg htX, if_pos hhX, zero_sub, neg_nonpos]
      by_contra hgneg
      push_neg at hgneg
      apply htX
      have hru : SReach O g u (O.head e) := (Finset.mem_filter.mp hhX).2
      have hstep : SStepE O g e (O.head e) (O.tail e) := ⟨he, Or.inr ⟨hgneg, rfl, rfl⟩⟩
      rw [hX, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨O.tail_mem he, hru.trans (SReach.step hstep)⟩
    · simp [htX, hhX]
  exact absurd hpos (not_lt.mpr hsum_le)

/-! ## Extracting an edge-distinct walk -/

/-- A sign-oriented step's endpoints are determined by the edge (the sign fixes the direction). -/
private lemma SStepE_det {g : β → ℤ} {e : β} {a b a' b' : α}
    (h1 : SStepE O g e a b) (h2 : SStepE O g e a' b') : a = a' ∧ b = b' := by
  rcases h1.2 with ⟨hp, ht, hh⟩ | ⟨hn, hh, ht⟩ <;>
    rcases h2.2 with ⟨hp', ht', hh'⟩ | ⟨hn', hh', ht'⟩
  · exact ⟨ht.symm.trans ht', hh.symm.trans hh'⟩
  · exact absurd hp (by omega)
  · exact absurd hp' (by omega)
  · exact ⟨hh.symm.trans hh', ht.symm.trans ht'⟩

/-- A walk containing edge `e` splits around `e`. -/
private lemma SWalk_split {g : β → ℤ} {v w : α} {es : List β} (hw : SWalk O g v es w) {e : β}
    (he : e ∈ es) :
    ∃ (es₁ es₂ : List β) (a b : α), es = es₁ ++ e :: es₂ ∧ SWalk O g v es₁ a ∧
      SStepE O g e a b ∧ SWalk O g b es₂ w := by
  revert he
  induction hw with
  | nil u => intro he; simp at he
  | @cons u v' w e0 es0 hstep hrest ih =>
    intro he
    rw [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨[], es0, u, v', by simp, SWalk.nil u, hstep, hrest⟩
    · obtain ⟨es₁, es₂, a, b, hsplit, hw₁, hstep', hw₂⟩ := ih he
      exact ⟨e0 :: es₁, es₂, a, b, by rw [hsplit, List.cons_append], SWalk.cons hstep hw₁,
        hstep', hw₂⟩

/-- A walk with a repeated edge can be strictly shortened. -/
private lemma SWalk_shorten {g : β → ℤ} {u w : α} {es : List β} (hw : SWalk O g u es w)
    (hnd : ¬ es.Nodup) :
    ∃ es', SWalk O g u es' w ∧ es'.length < es.length := by
  induction hw with
  | nil u => simp at hnd
  | @cons u v w e es0 hstep hrest ih =>
    by_cases he : e ∈ es0
    · obtain ⟨es₁, es₂, a, b, hsplit, hw₁, hstep', hw₂⟩ := SWalk_split hrest he
      obtain ⟨rfl, rfl⟩ := SStepE_det hstep' hstep
      refine ⟨e :: es₂, SWalk.cons hstep hw₂, ?_⟩
      rw [hsplit]
      simp only [List.length_cons, List.length_append]
      omega
    · have hnd0 : ¬ es0.Nodup := fun h => hnd (List.nodup_cons.mpr ⟨he, h⟩)
      obtain ⟨es', hw', hlt⟩ := ih hnd0
      exact ⟨e :: es', SWalk.cons hstep hw', by simp only [List.length_cons]; omega⟩

/-- Reachability yields an edge-distinct walk (minimal length). -/
private lemma exists_nodup_walk {g : β → ℤ} {u w : α} (h : SReach O g u w) :
    ∃ es, SWalk O g u es w ∧ es.Nodup := by
  classical
  obtain ⟨es0, hw0⟩ := h
  have hP : ∃ n, ∃ es, SWalk O g u es w ∧ es.length = n := ⟨es0.length, es0, hw0, rfl⟩
  obtain ⟨es, hw, hlen⟩ := Nat.find_spec hP
  refine ⟨es, hw, ?_⟩
  by_contra hnd
  obtain ⟨es', hw', hlt⟩ := SWalk_shorten hw hnd
  exact Nat.find_min hP (hlen ▸ hlt) ⟨es', hw', rfl⟩

/-! ## The augmenting step and finite descent -/

/-- **Augment.** If `Φ(g) > 0` there is an INV-map with strictly smaller potential. -/
private lemma augment [DecidableEq α] [DecidableEq β] (hV : V(G).Finite) (hE : E(G).Finite)
    (k : ℕ) (hk : 1 ≤ k) (f : β → ZMod k) (hflow : G.IsFlow O f) (g : β → ℤ)
    (hinv : INV O k f g) (hpos : 0 < Phi O hV hE g) :
    ∃ g', INV O k f g' ∧ Phi O hV hE g' < Phi O hV hE g := by
  have hclass : ∀ e ∈ E(G), ((g e : ℤ) : ZMod k) = f e := fun e he => (hinv.1 e he).2.2
  have hdvd : ∀ v ∈ V(G), (k:ℤ) ∣ bal O hE g v := fun v hv => bal_dvd hE k f hflow g hclass v hv
  have hex_pos : ∃ u ∈ V(G), 0 < bal O hE g u := by
    obtain ⟨v, hvf, hvne⟩ : ∃ v ∈ hV.toFinset, bal O hE g v ≠ 0 := by
      by_contra h
      push_neg at h
      have : Phi O hV hE g = 0 := by
        rw [Phi]; apply Finset.sum_eq_zero; intro v hv; rw [h v hv]; rfl
      omega
    by_contra hcon
    push_neg at hcon
    have hall_le : ∀ x ∈ hV.toFinset, bal O hE g x ≤ 0 :=
      fun x hx => hcon x ((Set.Finite.mem_toFinset hV).mp hx)
    have hvneg : bal O hE g v < 0 := lt_of_le_of_ne (hall_le v hvf) hvne
    have hsum0 : ∑ x ∈ hV.toFinset, bal O hE g x = 0 := sum_bal_zero hV hE g
    have hlt : ∑ x ∈ hV.toFinset, bal O hE g x < ∑ _x ∈ hV.toFinset, (0:ℤ) :=
      Finset.sum_lt_sum hall_le ⟨v, hvf, hvneg⟩
    rw [Finset.sum_const_zero] at hlt
    omega
  obtain ⟨u, huV, hbu⟩ := hex_pos
  obtain ⟨w, hwV, hreach, hbw⟩ := exists_neg_reachable hV hE g u huV hbu
  obtain ⟨es, hwalk, hnd⟩ := exists_nodup_walk hreach
  have hne : u ≠ w := by intro h; rw [h] at hbu; omega
  have hk' : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
  refine ⟨reroute (k:ℤ) es g, reroute_INV k hk f g hinv es (SWalk_edges_mem g hwalk), ?_⟩
  exact reroute_decreases_phi hV hE (k:ℤ) g hwalk hnd huV hwV hne hk' hbu hbw
    (hdvd u huV) (hdvd w hwV)

/-- **Finite descent.** From any INV-map one reaches an INV-map of potential `0`. -/
private lemma descent [DecidableEq α] [DecidableEq β] (hV : V(G).Finite) (hE : E(G).Finite)
    (k : ℕ) (hk : 1 ≤ k) (f : β → ZMod k) (hflow : G.IsFlow O f) :
    ∀ n g, INV O k f g → Phi O hV hE g = n → ∃ g', INV O k f g' ∧ Phi O hV hE g' = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hinv hphi
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact ⟨g, hinv, by rw [hphi, hn]⟩
    · have hpos : 0 < Phi O hV hE g := by rw [hphi]; exact hn
      obtain ⟨g', hinv', hlt⟩ := augment hV hE k hk f hflow g hinv hpos
      exact ih (Phi O hV hE g') (hphi ▸ hlt) g' hinv' rfl

/-! ## Lemmas 9–11 (`ZkFlowLiftsToIntFlow`): the hard `⇒` direction

From a nowhere-zero `(ℤ/k)`-flow, build an integer `k`-flow by the finite-descent argument:
choose positive representatives `g ∈ [1, k-1]` with all vertex imbalances `≡ 0 (mod k)`, then
repeatedly reroute along a directed `P⁺ → P⁻` path to strictly decrease `Φ := ∑_v |b(v)|`
until `Φ = 0`, at which point `g` is an honest integer `k`-flow. -/

/-- **Lemmas 9–11 (⇒ direction).** From a nowhere-zero `(ℤ/k)`-flow of `G` w.r.t. `O`, there is
an integer `k`-flow of `G` w.r.t. `O`, built by the finite-descent construction above
(positive representatives → sign-oriented reroute strictly decreasing `Φ` → `Φ = 0`). -/
theorem ZkFlowLiftsToIntFlow {k : ℕ} (hk : 1 ≤ k) (hV : V(G).Finite) (hE : E(G).Finite)
    (O : Orientation G) (f : β → ZMod k) (hflow : G.IsFlow O f) (hnz : G.IsNowhereZero f) :
    ∃ φ : β → ℤ, G.IsIntegerKFlow O φ (k : ℤ) := by
  classical
  set g₀ : β → ℤ := fun e => if e ∈ E(G) then zkRep f e else 0 with hg₀
  have hinv₀ : INV O k f g₀ := by
    constructor
    · intro e he
      simp only [hg₀, if_pos he]
      obtain ⟨h1, h2, h3⟩ := ZkFlowRepresentativeClaim hk f hnz e he
      rw [abs_of_pos (by omega : (0:ℤ) < zkRep f e)]
      exact ⟨h1, h2, h3⟩
    · intro e he; simp only [hg₀, if_neg he]
  obtain ⟨g', hinv', hphi0⟩ :=
    descent hV hE k hk f hflow (Phi O hV hE g₀) g₀ hinv₀ rfl
  refine ⟨g', flow_of_phi_zero hV hE g' hphi0, fun e he => ?_⟩
  obtain ⟨h1, h2, _⟩ := hinv'.1 e he
  exact ⟨by omega, by omega⟩

/-! ## Lemma 12 (`ZkIffIntKFlow`): the equivalence -/

/-- **Theorem II.1 / Lemma 12.** For `k ≥ 1` and a finite multigraph `G` with orientation `O`,
`G` has a nowhere-zero `(ℤ/k)`-flow iff it has a nowhere-zero integer `k`-flow. -/
theorem zk_iff_int_k_flow {k : ℕ} (hk : 1 ≤ k) (hV : V(G).Finite) (hE : E(G).Finite)
    (O : Orientation G) :
    (∃ f : β → ZMod k, G.IsFlow O f ∧ G.IsNowhereZero f) ↔
      (∃ φ : β → ℤ, G.IsIntegerKFlow O φ (k : ℤ)) := by
  constructor
  · rintro ⟨f, hflow, hnz⟩
    exact ZkFlowLiftsToIntFlow hk hV hE O f hflow hnz
  · rintro ⟨φ, hφ⟩
    exact ⟨fun e => ((φ e : ZMod k)), IntFlowReducesToZk hE O φ hφ⟩

end Workspace.PriorWorkProofs.Tutte
