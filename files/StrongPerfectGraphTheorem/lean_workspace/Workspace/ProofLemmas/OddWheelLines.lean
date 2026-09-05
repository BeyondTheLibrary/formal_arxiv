import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.WheelConverse
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.Statements.S16.Thm_16_1

/-!
# The second half of claim (1) in the proof of 16.3 — the "lines" argument

PAPER (printed p. 101, inside the proof of 16.3, claim (1)):

> *"So there is no odd `Y ∪ {v}`-segment in `C`.  Define a "line" to be a maximal subpath of
> `C` with no internal vertex adjacent to `v`.  It follows that every edge of `C` is in a
> unique line.  Let `C` have vertices `p₁, …, pₙ` in order, and let `S` be an odd `Y`-segment.
> Since there are no odd `Y ∪ {v}`-segments, it follows that an even number of edges of `S`
> are `Y ∪ {v}`-complete.  Hence an odd number are not, and therefore there is a line `L`
> containing an odd number of edges of `S` that are not `Y ∪ {v}`-complete.  In particular it
> contains at least one edge that is `Y`-complete and not `Y ∪ {v}`-complete, so `L` has
> length > 1.  Let the ends of `L` be `p, q`.  By 16.1, `p` and `q` have the same wheel-parity
> with respect to `(C,Y)`, and so `L` contains an odd number of edges of some other
> `Y`-segment `S' ≠ S`.  In particular, there are two disjoint `Y`-complete edges in the hole
> `v-p-L-q-v` ( = `H` say); so `H` has length ≥ 6 (because `v` is not `Y`-complete) and so
> `(H,Y)` is a wheel.  Moreover it is an odd wheel, for it contains an odd number of edges of
> `S`, and those edges form either one or two `Y`-segments in `H`, and one of these segments is
> odd.  Since there is a `Y ∪ {v}`-complete edge in `C` (by 16.1, since `v` has neighbours in
> `C` of opposite wheel-parity) which therefore does not belong to `L`, this contradicts the
> optimality of `(C,Y)`.  This proves (1)."*

The first sentence is `OddWheelNoOddExtSegment.no_odd_ext_segment` (Case A); this module is
everything after it.

## The encoding

Everything happens on *cyclic positions* of the rim, as in `WheelParity` / `SegmentBasics`:
`CycVert G Y C m` says position `m` of `C` is `Y`-complete, `CycEdge G Y C m` says the cyclic
edge from position `m` to position `m+1` is `Y`-complete.  Writing `Nbr m` for
`CycVert G {v} C m` (*"the vertex at position `m` is adjacent to `v`"* — note
`VertexComplete G u {v}` unfolds to `G.Adj u v`), a **line** is a block `k, …, k+M` with
`Nbr k`, `Nbr (k+M)` and no `Nbr` strictly inside.  *"Every edge of `C` is in a unique line"*
is then the statement that the lines tile any window `[c₀, c₀+n)` whose ends are `Nbr`
positions, which is what `exists_line_odd` uses.

Two abstract counting engines do all the work, and are stated for an arbitrary predicate on
`ℕ`:

* `pair_parity` — in a block flanked by two `¬w` positions, **if every maximal run of `w` has
  odd length then an even number of consecutive pairs are both `w`.**  Used twice, in both
  directions: once with `w = ` "`Y ∪ {v}`-complete position" to get *"an even number of edges
  of `S` are `Y ∪ {v}`-complete"*, and once (contrapositively) with `w = ` "position of `H`
  lying in `S`" to get *"one of these segments is odd"*.
* `exists_line_odd` — **a window whose two ends are `Nbr` positions is tiled by lines, so if a
  weight function has odd total over the window then some line carries an odd total.**  This
  is *"there is a line `L` containing an odd number of edges of `S` that are not
  `Y ∪ {v}`-complete"*.

Nothing in this module corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.OddWheelLines

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

attribute [local instance] Classical.propDecidable

/-! ### Engine 1 — the parity of the consecutive-pair count of a flanked block -/

/-- The indicator of *"positions `t` and `t+1` both satisfy `w`"*. -/
private noncomputable def pairInd (w : ℕ → Prop) (t : ℕ) : ℕ := if w t ∧ w (t + 1) then 1 else 0

private theorem pairInd_eq_zero_left {w : ℕ → Prop} {t : ℕ} (h : ¬ w t) : pairInd w t = 0 := by
  simp only [pairInd]
  exact if_neg (fun hc => h hc.1)

private theorem pairInd_eq_zero_right {w : ℕ → Prop} {t : ℕ} (h : ¬ w (t + 1)) :
    pairInd w t = 0 := by
  simp only [pairInd]
  exact if_neg (fun hc => h hc.2)

private theorem pairInd_eq_one {w : ℕ → Prop} {t : ℕ} (h1 : w t) (h2 : w (t + 1)) :
    pairInd w t = 1 := by
  simp only [pairInd]
  exact if_pos ⟨h1, h2⟩

private theorem pair_parity_aux (w : ℕ → Prop) :
    ∀ (d a b : ℕ), b - a ≤ d → a ≤ b → ¬ w a → ¬ w b →
      (∀ k M : ℕ, a < k → 1 ≤ M → k + M ≤ b → (∀ t, t < M → w (k + t)) → ¬ w (k + M) →
        ¬ w (k - 1) → Odd M) →
      Even (∑ t ∈ Finset.Ico a b, pairInd w t) := by
  intro d
  induction d with
  | zero =>
      intro a b hd hab ha hb hodd
      have hE : a = b := by omega
      subst hE
      simp
  | succ d ih =>
      intro a b hd hab ha hb hodd
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      have hsplit1 : ∑ t ∈ Finset.Ico a b, pairInd w t
          = pairInd w a + ∑ t ∈ Finset.Ico (a + 1) b, pairInd w t :=
        Finset.sum_eq_sum_Ico_succ_bot hlt _
      by_cases h1 : w (a + 1)
      · -- a maximal run starts at `a+1`
        have hb2 : a + 2 ≤ b := by
          rcases Nat.lt_or_ge (a + 1) b with h | h
          · omega
          · exact absurd (show w b by rw [show b = a + 1 from by omega]; exact h1) hb
        have hex : ∃ j, ¬ w (a + 1 + (j + 1)) := by
          refine ⟨b - a - 2, ?_⟩
          have he : a + 1 + (b - a - 2 + 1) = b := by omega
          rw [he]; exact hb
        classical
        obtain ⟨M, hM1, hrun, hstop⟩ :
            ∃ M : ℕ, 1 ≤ M ∧ (∀ t, t < M → w (a + 1 + t)) ∧ ¬ w (a + 1 + M) := by
          refine ⟨Nat.find hex + 1, by omega, ?_, Nat.find_spec hex⟩
          intro t ht
          rcases Nat.eq_zero_or_pos t with rfl | hpos
          · simpa using h1
          · obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
            have hj : j < Nat.find hex := by omega
            exact not_not.mp (Nat.find_min hex hj)
        have hMle : a + 1 + M ≤ b := by
          by_contra hcon
          have hlt2 : b - (a + 1) < M := by omega
          have hw : w (a + 1 + (b - (a + 1))) := hrun _ hlt2
          rw [show a + 1 + (b - (a + 1)) = b from by omega] at hw
          exact hb hw
        have hoddM : Odd M :=
          hodd (a + 1) M (by omega) hM1 hMle hrun hstop (by simpa using ha)
        obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
        -- the block `[a, a+1+M)` contributes `M'`, which is even
        have hblock : ∑ t ∈ Finset.Ico a (a + 1 + (M' + 1)), pairInd w t = M' := by
          have hre : ∑ t ∈ Finset.Ico a (a + 1 + (M' + 1)), pairInd w t
              = ∑ i ∈ Finset.range (M' + 2), pairInd w (a + i) := by
            rw [Finset.sum_Ico_eq_sum_range, show a + 1 + (M' + 1) - a = M' + 2 from by omega]
          rw [hre, Finset.sum_range_succ' (fun i => pairInd w (a + i)) (M' + 1),
            Finset.sum_range_succ (fun i => pairInd w (a + (i + 1))) M']
          have e0 : pairInd w (a + 0) = 0 := pairInd_eq_zero_left (by simpa using ha)
          have e2 : pairInd w (a + (M' + 1)) = 0 := by
            refine pairInd_eq_zero_right ?_
            have he : a + (M' + 1) + 1 = a + 1 + (M' + 1) := by omega
            rw [he]; exact hstop
          have e1 : ∀ i ∈ Finset.range M', pairInd w (a + (i + 1)) = 1 := by
            intro i hi
            rw [Finset.mem_range] at hi
            refine pairInd_eq_one ?_ ?_
            · have he : a + (i + 1) = a + 1 + i := by omega
              rw [he]; exact hrun i (by omega)
            · have he : a + (i + 1) + 1 = a + 1 + (i + 1) := by omega
              rw [he]; exact hrun (i + 1) (by omega)
          rw [Finset.sum_congr rfl e1, e0, e2]
          simp
        have hrest : Even (∑ t ∈ Finset.Ico (a + 1 + (M' + 1)) b, pairInd w t) := by
          refine ih (a + 1 + (M' + 1)) b (by omega) hMle hstop hb ?_
          intro k Mk hk hM1' hkb hkrun hkstop hkprev
          exact hodd k Mk (by omega) hM1' hkb hkrun hkstop hkprev
        have hcons : ∑ t ∈ Finset.Ico a (a + 1 + (M' + 1)), pairInd w t
            + ∑ t ∈ Finset.Ico (a + 1 + (M' + 1)) b, pairInd w t
            = ∑ t ∈ Finset.Ico a b, pairInd w t :=
          Finset.sum_Ico_consecutive _ (by omega) hMle
        rw [← hcons, hblock]
        have hM'even : Even M' := by
          rcases hoddM with ⟨r, hr⟩
          exact ⟨r, by omega⟩
        exact hM'even.add hrest
      · -- nothing starts at `a+1`
        rw [hsplit1, pairInd_eq_zero_left ha, Nat.zero_add]
        refine ih (a + 1) b (by omega) (by omega) h1 hb ?_
        intro k Mk hk hM1 hkb hkrun hkstop hkprev
        exact hodd k Mk (by omega) hM1 hkb hkrun hkstop hkprev

/-- **Engine 1.**  In a block whose two ends fail `w`, if every maximal run of `w` inside the
block has odd length, then an even number of positions `t` of the block have both `t` and `t+1`
satisfying `w`. -/
private theorem pair_parity (w : ℕ → Prop) (a b : ℕ) (hab : a ≤ b)
    (ha : ¬ w a) (hb : ¬ w b)
    (hodd : ∀ k M : ℕ, a < k → 1 ≤ M → k + M ≤ b → (∀ t, t < M → w (k + t)) → ¬ w (k + M) →
      ¬ w (k - 1) → Odd M) :
    Even (∑ t ∈ Finset.Ico a b, pairInd w t) :=
  pair_parity_aux w (b - a) a b le_rfl hab ha hb hodd

/-- The contrapositive form of Engine 1: an odd consecutive-pair count forces a run of even
length. -/
private theorem exists_even_run (w : ℕ → Prop) (a b : ℕ) (hab : a ≤ b)
    (ha : ¬ w a) (hb : ¬ w b)
    (hsum : ¬ Even (∑ t ∈ Finset.Ico a b, pairInd w t)) :
    ∃ k M : ℕ, a < k ∧ 1 ≤ M ∧ k + M ≤ b ∧ (∀ t, t < M → w (k + t)) ∧ ¬ w (k + M) ∧
      ¬ w (k - 1) ∧ Even M := by
  by_contra hcon
  refine hsum (pair_parity w a b hab ha hb ?_)
  intro k M hk hM1 hkb hrun hstop hprev
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro hev
  exact hcon ⟨k, M, hk, hM1, hkb, hrun, hstop, hprev, hev⟩

/-! ### Engine 2 — the lines tile a window, so some line carries an odd weight -/

private theorem exists_line_odd_aux (Nbr : ℕ → Prop) (f : ℕ → ℕ) (B : ℕ) (hB : Nbr B)
    (hnext : ∀ k : ℕ, ∃ M : ℕ, 1 ≤ M ∧ Nbr (k + M) ∧ ∀ t, 0 < t → t < M → ¬ Nbr (k + t)) :
    ∀ (d c : ℕ), B - c ≤ d → Nbr c → c ≤ B → ¬ Even (∑ t ∈ Finset.Ico c B, f t) →
      ∃ c' M : ℕ, c ≤ c' ∧ 1 ≤ M ∧ c' + M ≤ B ∧ Nbr c' ∧ Nbr (c' + M) ∧
        (∀ t, 0 < t → t < M → ¬ Nbr (c' + t)) ∧ ¬ Even (∑ t ∈ Finset.Ico c' (c' + M), f t) := by
  intro d
  induction d with
  | zero =>
      intro c hd hc hcB hsum
      have : c = B := by omega
      subst this
      simp at hsum
  | succ d ih =>
      intro c hd hc hcB hsum
      rcases eq_or_lt_of_le hcB with rfl | hlt
      · simp at hsum
      obtain ⟨M, hM1, hNb, hint⟩ := hnext c
      have hMB : c + M ≤ B := by
        by_contra hcon
        exact hint (B - c) (by omega) (by omega) (by
          have he : c + (B - c) = B := by omega
          rw [he]; exact hB)
      have hcons : ∑ t ∈ Finset.Ico c (c + M), f t + ∑ t ∈ Finset.Ico (c + M) B, f t
          = ∑ t ∈ Finset.Ico c B, f t :=
        Finset.sum_Ico_consecutive _ (by omega) hMB
      by_cases hfirst : Even (∑ t ∈ Finset.Ico c (c + M), f t)
      · have hsecond : ¬ Even (∑ t ∈ Finset.Ico (c + M) B, f t) := by
          intro hev
          exact hsum (by rw [← hcons]; exact hfirst.add hev)
        obtain ⟨c', M', hle, hM1', hMB', hNb', hNbM', hint', hodd'⟩ :=
          ih (c + M) (by omega) hNb hMB hsecond
        exact ⟨c', M', by omega, hM1', hMB', hNb', hNbM', hint', hodd'⟩
      · exact ⟨c, M, le_rfl, hM1, hMB, hc, hNb, hint, hfirst⟩

/-- **Engine 2.**  *"Every edge of `C` is in a unique line"*: a window whose two ends are
`Nbr` positions is tiled by lines, so if a weight function has odd total over the window then
some line inside it carries an odd total. -/
private theorem exists_line_odd (Nbr : ℕ → Prop) (f : ℕ → ℕ) (c₀ B : ℕ)
    (hc₀ : Nbr c₀) (hB : Nbr B) (hle : c₀ ≤ B)
    (hnext : ∀ k : ℕ, ∃ M : ℕ, 1 ≤ M ∧ Nbr (k + M) ∧ ∀ t, 0 < t → t < M → ¬ Nbr (k + t))
    (hsum : ¬ Even (∑ t ∈ Finset.Ico c₀ B, f t)) :
    ∃ c M : ℕ, c₀ ≤ c ∧ 1 ≤ M ∧ c + M ≤ B ∧ Nbr c ∧ Nbr (c + M) ∧
      (∀ t, 0 < t → t < M → ¬ Nbr (c + t)) ∧ ¬ Even (∑ t ∈ Finset.Ico c (c + M), f t) :=
  exists_line_odd_aux Nbr f B hB hnext (B - c₀) c₀ le_rfl hc₀ hle hsum

/-! ### A sum over one full period does not depend on where the period starts -/

private theorem periodic_sum_shift_one {g : ℕ → ℕ} {n : ℕ} (hper : ∀ t, g (t + n) = g t)
    (K : ℕ) : ∑ s ∈ Finset.range n, g (K + s) = ∑ s ∈ Finset.range n, g (K + 1 + s) := by
  have h1 : ∑ s ∈ Finset.range (n + 1), g (K + s)
      = ∑ s ∈ Finset.range n, g (K + s) + g (K + n) := Finset.sum_range_succ _ _
  have h2 : ∑ s ∈ Finset.range (n + 1), g (K + s)
      = (∑ s ∈ Finset.range n, g (K + (s + 1))) + g (K + 0) := Finset.sum_range_succ' _ _
  have h3 : ∀ s, g (K + (s + 1)) = g (K + 1 + s) := by intro s; congr 1; omega
  rw [Finset.sum_congr rfl (fun s _ => h3 s)] at h2
  have h4 : g (K + n) = g K := by rw [show K + n = K + n from rfl]; exact hper K
  rw [h4] at h1
  simp only [Nat.add_zero] at h2
  omega

private theorem periodic_sum_shift {g : ℕ → ℕ} {n : ℕ} (hper : ∀ t, g (t + n) = g t) :
    ∀ (j K : ℕ), ∑ s ∈ Finset.range n, g (K + s) = ∑ s ∈ Finset.range n, g (K + j + s) := by
  intro j
  induction j with
  | zero => intro K; simp
  | succ j ih =>
      intro K
      rw [ih K, periodic_sum_shift_one hper (K + j)]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      congr 1

/-- The sum of a `n`-periodic weight over any window of length `n` is the same. -/
private theorem periodic_window_sum {g : ℕ → ℕ} {n : ℕ} (hper : ∀ t, g (t + n) = g t)
    (K K' : ℕ) :
    ∑ s ∈ Finset.range n, g (K + s) = ∑ s ∈ Finset.range n, g (K' + s) := by
  rcases le_total K K' with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, K' = K + j := ⟨K' - K, by omega⟩
    exact periodic_sum_shift hper j K
  · obtain ⟨j, rfl⟩ : ∃ j, K = K' + j := ⟨K - K', by omega⟩
    exact (periodic_sum_shift hper j K').symm

/-! ### Positions of the rim adjacent to `v` -/

section Rim

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V} {v : V}

/-- *"The vertex at cyclic position `m` of `C` is adjacent to `v`."*  Since
`VertexComplete G u {v}` unfolds to `G.Adj u v`, this is literally `CycVert` for the singleton
hub `{v}`, so all of `SegmentBasics`' congruence machinery applies to it. -/
private def Nbr (G : SimpleGraph V) (C : List V) (v : V) (m : ℕ) : Prop :=
  SegmentBasics.CycVert G ({v} : Set V) C m

private theorem vertexComplete_singleton {u : V} :
    VertexComplete G u ({v} : Set V) ↔ G.Adj u v := by
  constructor
  · intro h; exact h v rfl
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h

private theorem vertexComplete_union {u : V} :
    VertexComplete G u (Y ∪ {v}) ↔ (VertexComplete G u Y ∧ G.Adj u v) := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), h v (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact h2

private theorem nbr_congr {m m' : ℕ} (h : m % C.length = m' % C.length) :
    Nbr G C v m ↔ Nbr G C v m' :=
  SegmentBasics.cycVert_congr (G := G) (Y := ({v} : Set V)) (C := C) h

private theorem nbr_periodic (m : ℕ) : Nbr G C v (m + C.length) ↔ Nbr G C v m :=
  nbr_congr (Nat.add_mod_right _ _)

/-- The `Y ∪ {v}`-complete positions are exactly the `Y`-complete positions adjacent to `v`. -/
private theorem cycVert_union_iff (m : ℕ) :
    SegmentBasics.CycVert G (Y ∪ {v}) C m ↔
      (SegmentBasics.CycVert G Y C m ∧ Nbr G C v m) := by
  constructor
  · rintro ⟨u, hu, hcu⟩
    rw [vertexComplete_union] at hcu
    exact ⟨⟨u, hu, hcu.1⟩, ⟨u, hu, vertexComplete_singleton.mpr hcu.2⟩⟩
  · rintro ⟨⟨u, hu, hcu⟩, ⟨u', hu', hcu'⟩⟩
    refine ⟨u, hu, vertexComplete_union.mpr ⟨hcu, ?_⟩⟩
    have : u' = u := Option.some_injective _ (hu'.symm.trans hu)
    subst this
    exact vertexComplete_singleton.mp hcu'

/-- Reading `Nbr` off the list. -/
private theorem nbr_getElem_iff (hn : 0 < C.length) (m : ℕ) :
    Nbr G C v m ↔ G.Adj (C[m % C.length]'(Nat.mod_lt _ hn)) v := by
  constructor
  · rintro ⟨u, hu, hcu⟩
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hu
    rw [Option.some_injective _ hu]
    exact vertexComplete_singleton.mp hcu
  · intro h
    exact ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hn), vertexComplete_singleton.mpr h⟩

/-- **The next `Nbr` position after `k`.**  Every position has one, since `v` has at least one
neighbour on the rim and `Nbr` is periodic; taking the least such gives the line starting at
`k` when `k` is itself a `Nbr` position. -/
private theorem exists_next_nbr (hn : 0 < C.length) {i₀ : ℕ} (hi₀ : Nbr G C v i₀) (k : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ Nbr G C v (k + M) ∧ ∀ t, 0 < t → t < M → ¬ Nbr G C v (k + t) := by
  classical
  have hex : ∃ j : ℕ, Nbr G C v (k + (j + 1)) := by
    have hT : k + 1 ≤ i₀ + C.length * (k + 1) := by
      have : k + 1 ≤ C.length * (k + 1) := Nat.le_mul_of_pos_left _ hn
      omega
    refine ⟨i₀ + C.length * (k + 1) - k - 1, ?_⟩
    have he : k + (i₀ + C.length * (k + 1) - k - 1 + 1) = i₀ + C.length * (k + 1) := by omega
    rw [he]
    refine (nbr_congr ?_).mp hi₀
    rw [Nat.add_mul_mod_self_left]
  refine ⟨Nat.find hex + 1, by omega, Nat.find_spec hex, ?_⟩
  intro t ht0 htM
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
  exact Nat.find_min hex (by omega)

/-- Every `Nbr` position is congruent to `c + t` for a unique `t < n`, and — inside a line
starting at `c` — that `t` is either `0` or at least the length of the line. -/
private theorem nbr_offset_of_line (hn : 0 < C.length) {c M : ℕ}
    (hint : ∀ t, 0 < t → t < M → ¬ Nbr G C v (c + t))
    {i : ℕ} (hi : Nbr G C v i) :
    ∃ t, t < C.length ∧ (t = 0 ∨ M ≤ t) ∧ (c + t) % C.length = i % C.length := by
  have hcm : c % C.length < C.length := Nat.mod_lt _ hn
  have hkey : (c + (i + C.length - c % C.length) % C.length) % C.length = i % C.length := by
    have s1 : (c + (i + C.length - c % C.length) % C.length) % C.length
        = (c % C.length + (i + C.length - c % C.length) % C.length) % C.length :=
      (Nat.mod_add_mod c C.length _).symm
    have s2 : (c % C.length + (i + C.length - c % C.length) % C.length) % C.length
        = (c % C.length + (i + C.length - c % C.length)) % C.length :=
      Nat.add_mod_mod _ _ _
    have s3 : c % C.length + (i + C.length - c % C.length) = i + C.length := by omega
    rw [s1, s2, s3, Nat.add_mod_right]
  refine ⟨(i + C.length - c % C.length) % C.length, Nat.mod_lt _ hn, ?_, hkey⟩
  by_contra hcon
  push Not at hcon
  exact hint _ (by omega) (by omega) ((nbr_congr hkey).mpr hi)

/-- A line is shorter than the whole rim: a line of length `C.length` would contain, strictly
inside, a position congruent to the second of the two `Nbr` residues. -/
private theorem line_length_lt (hn : 0 < C.length) {c M : ℕ} (hc : Nbr G C v c)
    (hint : ∀ t, 0 < t → t < M → ¬ Nbr G C v (c + t))
    {i₁ i₂ : ℕ} (h₁ : Nbr G C v i₁) (h₂ : Nbr G C v i₂)
    (hne : i₁ % C.length ≠ i₂ % C.length) :
    M < C.length := by
  have hMle : M ≤ C.length := by
    by_contra hcon
    exact hint C.length hn (by omega) ((nbr_periodic c).mpr hc)
  rcases Nat.lt_or_ge M C.length with h | h
  · exact h
  have hM : M = C.length := by omega
  obtain ⟨t₁, ht₁, hc₁, he₁⟩ := nbr_offset_of_line hn hint h₁
  obtain ⟨t₂, ht₂, hc₂, he₂⟩ := nbr_offset_of_line hn hint h₂
  have e₁ : t₁ = 0 := by rcases hc₁ with h' | h' <;> omega
  have e₂ : t₂ = 0 := by rcases hc₂ with h' | h' <;> omega
  subst e₁; subst e₂
  exact absurd (he₁.symm.trans he₂) hne

/-! ### The segment `S`, read as a set of cyclic positions -/

/-- Position `m` of the rim lies on the segment whose run is `kS, …, kS+LS-1`. -/
private def InSeg (C : List V) (kS LS m : ℕ) : Prop :=
  ∃ s, s < LS ∧ (kS + s) % C.length = m % C.length

/-- The cyclic edge at position `m` is an edge of that segment. -/
private def SegEdge (C : List V) (kS LS m : ℕ) : Prop :=
  ∃ s, s + 1 < LS ∧ (kS + s) % C.length = m % C.length

private noncomputable def segEdgeInd (C : List V) (kS LS m : ℕ) : ℕ :=
  if SegEdge C kS LS m then 1 else 0

private noncomputable def lineWeight (G : SimpleGraph V) (C : List V) (Y : Set V) (v : V)
    (kS LS m : ℕ) : ℕ :=
  if SegEdge C kS LS m ∧ ¬ WheelParity.CycEdge G (Y ∪ {v}) C m then 1 else 0

private theorem segEdge_congr {kS LS m m' : ℕ} (h : m % C.length = m' % C.length) :
    SegEdge C kS LS m ↔ SegEdge C kS LS m' := by
  simp only [SegEdge, h]

private theorem inSeg_congr {kS LS m m' : ℕ} (h : m % C.length = m' % C.length) :
    InSeg C kS LS m ↔ InSeg C kS LS m' := by
  simp only [InSeg, h]

/-- An edge of the segment is a pair of consecutive positions of the segment. -/
private theorem segEdge_iff_inSeg (hn : 0 < C.length) {kS LS m : ℕ} (hLS : LS + 1 ≤ C.length) :
    SegEdge C kS LS m ↔ (InSeg C kS LS m ∧ InSeg C kS LS (m + 1)) := by
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨⟨s, by omega, he⟩, ⟨s + 1, by omega, by
      rw [show kS + (s + 1) = (kS + s) + 1 from by omega]
      exact SegmentBasics.add_mod_congr he 1⟩⟩
  · rintro ⟨⟨s, hs, he⟩, ⟨s', hs', he'⟩⟩
    refine ⟨s, ?_, he⟩
    have h1 : (kS + s + 1) % C.length = (m + 1) % C.length := SegmentBasics.add_mod_congr he 1
    have h2 : (kS + s') % C.length = (kS + s + 1) % C.length := he'.trans h1.symm
    have h3 : (kS + s') % C.length = (kS + (s + 1)) % C.length := h2
    have hcancel : s' % C.length = (s + 1) % C.length := Nat.ModEq.add_left_cancel' kS h3
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcancel
    omega

/-- A position of the segment is `Y`-complete. -/
private theorem cycVert_of_inSeg {kS LS m : ℕ}
    (hallS : ∀ t, t < LS → SegmentBasics.CycVert G Y C (kS + t))
    (h : InSeg C kS LS m) : SegmentBasics.CycVert G Y C m := by
  obtain ⟨s, hs, he⟩ := h
  exact (SegmentBasics.cycVert_congr he).mp (hallS s hs)

/-- The position just past the right end of the segment is not `Y`-complete. -/
private theorem not_cycVert_of_inSeg_right {kS LS m : ℕ}
    (hnextS : ¬ SegmentBasics.CycVert G Y C (kS + LS))
    (h1 : InSeg C kS LS m) (h2 : ¬ InSeg C kS LS (m + 1)) :
    ¬ SegmentBasics.CycVert G Y C (m + 1) := by
  obtain ⟨s, hs, he⟩ := h1
  have hstep : (kS + (s + 1)) % C.length = (m + 1) % C.length := by
    rw [show kS + (s + 1) = (kS + s) + 1 from by omega]
    exact SegmentBasics.add_mod_congr he 1
  have hsLS : s + 1 = LS := by
    by_contra hcon
    exact h2 ⟨s + 1, by omega, hstep⟩
  intro hcv
  refine hnextS ((SegmentBasics.cycVert_congr ?_).mpr hcv)
  rw [← hsLS]
  exact hstep

/-- The position just before the left end of the segment is not `Y`-complete. -/
private theorem not_cycVert_of_inSeg_left (hn : 0 < C.length) {kS LS m : ℕ}
    (hprevS : ¬ SegmentBasics.CycVert G Y C (kS + (C.length - 1)))
    (h1 : InSeg C kS LS (m + 1)) (h2 : ¬ InSeg C kS LS m) :
    ¬ SegmentBasics.CycVert G Y C m := by
  obtain ⟨s, hs, he⟩ := h1
  have hs0 : s = 0 := by
    by_contra hcon
    refine h2 ⟨s - 1, by omega, ?_⟩
    have hstep : (kS + (s - 1) + 1) % C.length = (m + 1) % C.length := by
      rw [show kS + (s - 1) + 1 = kS + s from by omega]
      exact he
    exact Nat.ModEq.add_right_cancel' 1 hstep
  subst hs0
  intro hcv
  refine hprevS ((SegmentBasics.cycVert_congr ?_).mpr hcv)
  have he0 : kS % C.length = (m + 1) % C.length := by simpa using he
  have hstep : (kS + (C.length - 1)) % C.length = (m + 1 + (C.length - 1)) % C.length :=
    SegmentBasics.add_mod_congr he0 (C.length - 1)
  rw [hstep, show m + 1 + (C.length - 1) = m + C.length from by omega, Nat.add_mod_right]

/-- Position `j` of the hole `H = v-p-L-q-v` (whose length is `M + 2`, with `v` last) lies on
the segment `S`. -/
private def OnSegH (C : List V) (kS LS c M j : ℕ) : Prop :=
  j % (M + 2) ≠ M + 1 ∧ InSeg C kS LS (c + j % (M + 2))

/-- Reading a `Y`-complete cyclic edge as an `EdgeComplete` fact about the two vertices. -/
private theorem edgeComplete_of_cycEdge (hn : 0 < C.length) {W : Set V} {m : ℕ}
    (h : WheelParity.CycEdge G W C m) :
    EdgeComplete G W (C[m % C.length]'(Nat.mod_lt _ hn))
      (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) := by
  obtain ⟨x, y, hx, hy, hE⟩ := h
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hx hy
  rw [Option.some_injective _ hx, Option.some_injective _ hy]
  exact hE

/-- `pairInd` of the `Y`-completeness predicate is the indicator of a `Y`-complete cyclic
edge. -/
private theorem pairInd_cycVert (hC : IsHoleList G C) (W : Set V) (m : ℕ) :
    pairInd (SegmentBasics.CycVert G W C) m = if WheelParity.CycEdge G W C m then 1 else 0 := by
  by_cases h : WheelParity.CycEdge G W C m
  · obtain ⟨h1, h2⟩ := (YEdgeConfiguration.cycEdge_iff hC).mp h
    rw [pairInd_eq_one h1 h2, if_pos h]
  · have hn : ¬ (SegmentBasics.CycVert G W C m ∧ SegmentBasics.CycVert G W C (m + 1)) :=
      fun hc => h ((YEdgeConfiguration.cycEdge_iff hC).mpr hc)
    simp only [pairInd, if_neg hn, if_neg h]

/-- **Steps 3 and 4 of the printed paragraph.**

PAPER: *"Since there are no odd `Y ∪ {v}`-segments, it follows that an even number of edges of
`S` are `Y ∪ {v}`-complete.  Hence an odd number are not, and therefore there is a line `L`
containing an odd number of edges of `S` that are not `Y ∪ {v}`-complete.  In particular it
contains at least one edge that is `Y`-complete and not `Y ∪ {v}`-complete, so `L` has length
> 1."*

The last sentence is the `2 ≤ M` in the conclusion; and since a line of length `> 1` carries
no `Y ∪ {v}`-complete edge at all, *"an odd number of edges of `S` that are not
`Y ∪ {v}`-complete"* is the same as *"an odd number of edges of `S`"*, which is what the
conclusion records. -/
private theorem exists_odd_line
    (hC : IsHoleList G C)
    {ia ib : ℕ} (hia : Nbr G C v ia) (hib : Nbr G C v ib)
    (hres : ia % C.length ≠ ib % C.length)
    (hnoseg : ¬ ∃ S : List V, IsSegment G C (Y ∪ {v}) S ∧ Odd (pathLength S))
    {kS LS : ℕ} (hLS1 : 1 ≤ LS) (hLS2 : LS + 1 ≤ C.length) (hLSeven : Even LS)
    (hallS : ∀ t, t < LS → SegmentBasics.CycVert G Y C (kS + t))
    (hnextS : ¬ SegmentBasics.CycVert G Y C (kS + LS))
    (hprevS : ¬ SegmentBasics.CycVert G Y C (kS + (C.length - 1))) :
    ∃ c M : ℕ, 2 ≤ M ∧ M < C.length ∧ Nbr G C v c ∧ Nbr G C v (c + M) ∧
      (∀ t, 0 < t → t < M → ¬ Nbr G C v (c + t)) ∧
      ¬ Even (∑ t ∈ Finset.Ico c (c + M), segEdgeInd C kS LS t) := by
  classical
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  obtain ⟨LS', rfl⟩ : ∃ LS', LS = LS' + 1 := ⟨LS - 1, by omega⟩
  -- the two flanks of the run of `S` are not `Y ∪ {v}`-complete either
  have hAw : ¬ SegmentBasics.CycVert G (Y ∪ {v}) C (kS + (C.length - 1)) :=
    fun h => hprevS ((cycVert_union_iff _).mp h).1
  have hBw : ¬ SegmentBasics.CycVert G (Y ∪ {v}) C
      (kS + (C.length - 1) + (LS' + 1 + 1)) := by
    intro h
    refine hnextS ((cycVert_union_iff _).mp ((SegmentBasics.cycVert_congr ?_).mp h)).1
    rw [show kS + (C.length - 1) + (LS' + 1 + 1) = (kS + (LS' + 1)) + C.length from by omega,
      Nat.add_mod_right]
  -- Engine 1: every maximal run of `Y ∪ {v}`-complete positions is odd, so an even number of
  -- edges of `S` are `Y ∪ {v}`-complete
  have hpar : Even (∑ t ∈ Finset.Ico (kS + (C.length - 1))
      (kS + (C.length - 1) + (LS' + 1 + 1)),
      pairInd (SegmentBasics.CycVert G (Y ∪ {v}) C) t) := by
    refine pair_parity _ _ _ (by omega) hAw hBw ?_
    intro k M hk hM1 hkb hrun hstop hprev
    have hMn : M + 1 ≤ C.length := by omega
    have hprev' : ¬ SegmentBasics.CycVert G (Y ∪ {v}) C (k + (C.length - 1)) := by
      intro h
      refine hprev ((SegmentBasics.cycVert_congr ?_).mp h)
      rw [show k + (C.length - 1) = (k - 1) + C.length from by omega, Nat.add_mod_right]
    have hseg := SegmentBasics.isSegment_of_run (Y := (Y ∪ {v} : Set V)) hC hM1 hMn hrun hstop
      hprev'
    have hlen : ((C.rotate k).take M).length = M := by
      simp only [List.length_take, List.length_rotate]; omega
    rw [Nat.odd_iff, ← Nat.not_even_iff]
    intro hev
    refine hnoseg ⟨(C.rotate k).take M, hseg, ?_⟩
    rw [SegmentBasics.odd_pathLength_iff_even_length (by rw [hlen]; exact hM1), hlen]
    exact hev
  -- read that sum off as the number of `Y ∪ {v}`-complete edges of `S`
  have hsumB : ∑ t ∈ Finset.Ico (kS + (C.length - 1)) (kS + (C.length - 1) + (LS' + 1 + 1)),
        pairInd (SegmentBasics.CycVert G (Y ∪ {v}) C) t
      = ∑ s ∈ Finset.range LS',
          (if WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0) := by
    rw [Finset.sum_Ico_eq_sum_range,
      show kS + (C.length - 1) + (LS' + 1 + 1) - (kS + (C.length - 1)) = LS' + 2 from by omega,
      Finset.sum_range_succ'
        (fun s => pairInd (SegmentBasics.CycVert G (Y ∪ {v}) C) (kS + (C.length - 1) + s))
        (LS' + 1),
      Finset.sum_range_succ
        (fun s => pairInd (SegmentBasics.CycVert G (Y ∪ {v}) C) (kS + (C.length - 1) + (s + 1)))
        LS']
    have e0 : pairInd (SegmentBasics.CycVert G (Y ∪ {v}) C) (kS + (C.length - 1) + 0) = 0 :=
      pairInd_eq_zero_left (by simpa using hAw)
    have e2 : pairInd (SegmentBasics.CycVert G (Y ∪ {v}) C)
        (kS + (C.length - 1) + (LS' + 1)) = 0 := by
      refine pairInd_eq_zero_right ?_
      rw [show kS + (C.length - 1) + (LS' + 1) + 1 = kS + (C.length - 1) + (LS' + 1 + 1)
        from by omega]
      exact hBw
    have e1 : ∀ s ∈ Finset.range LS',
        pairInd (SegmentBasics.CycVert G (Y ∪ {v}) C) (kS + (C.length - 1) + (s + 1))
          = (if WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0) := by
      intro s hs
      have hiff : WheelParity.CycEdge G (Y ∪ {v}) C (kS + (C.length - 1) + (s + 1))
          ↔ WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) := by
        rw [show kS + (C.length - 1) + (s + 1) = (kS + s) + C.length from by omega]
        exact WheelParity.cycEdge_periodic (kS + s)
      rw [pairInd_cycVert hC]
      by_cases h : WheelParity.CycEdge G (Y ∪ {v}) C (kS + s)
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
    rw [Finset.sum_congr rfl e1, e0, e2]
    simp
  -- hence an odd number of edges of `S` are not `Y ∪ {v}`-complete
  have hnonW : ¬ Even (∑ s ∈ Finset.range LS',
      (if ¬ WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0)) := by
    have hsplit : (∑ s ∈ Finset.range LS',
          (if ¬ WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0))
        + (∑ s ∈ Finset.range LS',
          (if WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0)) = LS' := by
      have hone : ∀ s ∈ Finset.range LS',
          (if ¬ WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0)
            + (if WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0) = 1 := by
        intro s _
        by_cases h : WheelParity.CycEdge G (Y ∪ {v}) C (kS + s)
        · rw [if_neg (not_not_intro h), if_pos h]
        · rw [if_pos h, if_neg h]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hone]
      simp
    have hWeven : Even (∑ s ∈ Finset.range LS',
        (if WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0)) := by
      rw [← hsumB]; exact hpar
    obtain ⟨r, hr⟩ := hWeven
    obtain ⟨q, hq⟩ := hLSeven
    intro hev
    obtain ⟨p, hp⟩ := hev
    omega
  -- the weight `[edge of `S` and not `Y ∪ {v}`-complete]`, periodic in the rim
  have hper : ∀ t, lineWeight G C Y v kS (LS' + 1) (t + C.length)
      = lineWeight G C Y v kS (LS' + 1) t := by
    intro t
    have h1 : SegEdge C kS (LS' + 1) (t + C.length) ↔ SegEdge C kS (LS' + 1) t :=
      segEdge_congr (Nat.add_mod_right _ _)
    have h2 : WheelParity.CycEdge G (Y ∪ {v}) C (t + C.length)
        ↔ WheelParity.CycEdge G (Y ∪ {v}) C t := WheelParity.cycEdge_periodic t
    have hb : (SegEdge C kS (LS' + 1) (t + C.length) ∧
          ¬ WheelParity.CycEdge G (Y ∪ {v}) C (t + C.length))
        ↔ (SegEdge C kS (LS' + 1) t ∧ ¬ WheelParity.CycEdge G (Y ∪ {v}) C t) :=
      and_congr h1 (not_congr h2)
    simp only [lineWeight]
    by_cases h : SegEdge C kS (LS' + 1) t ∧ ¬ WheelParity.CycEdge G (Y ∪ {v}) C t
    · rw [if_pos (hb.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hb.mp hc)), if_neg h]
  -- summing the weight over one full period recovers the count over `S`
  have hwin : ∑ t ∈ Finset.Ico ia (ia + C.length), lineWeight G C Y v kS (LS' + 1) t
      = ∑ s ∈ Finset.range LS',
        (if ¬ WheelParity.CycEdge G (Y ∪ {v}) C (kS + s) then 1 else 0) := by
    rw [Finset.sum_Ico_eq_sum_range, show ia + C.length - ia = C.length from by omega,
      periodic_window_sum hper ia kS]
    have hsub : Finset.range LS' ⊆ Finset.range C.length := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))
    have hzero : ∀ x ∈ Finset.range C.length, x ∉ Finset.range LS' →
        lineWeight G C Y v kS (LS' + 1) (kS + x) = 0 := by
      intro x hx hxn
      rw [Finset.mem_range] at hx
      rw [Finset.mem_range] at hxn
      push Not at hxn
      simp only [lineWeight]
      refine if_neg ?_
      rintro ⟨⟨s, hs, hseq⟩, -⟩
      have hcancel : s % C.length = x % C.length := Nat.ModEq.add_left_cancel' kS hseq
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcancel
      omega
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl ?_
    intro s hs
    rw [Finset.mem_range] at hs
    have hse : SegEdge C kS (LS' + 1) (kS + s) := ⟨s, by omega, rfl⟩
    simp only [lineWeight]
    by_cases h : WheelParity.CycEdge G (Y ∪ {v}) C (kS + s)
    · rw [if_neg (fun hc => hc.2 h), if_neg (not_not_intro h)]
    · rw [if_pos ⟨hse, h⟩, if_pos h]
  -- Engine 2: some line carries an odd weight
  have hodd : ¬ Even (∑ t ∈ Finset.Ico ia (ia + C.length),
      lineWeight G C Y v kS (LS' + 1) t) := by rw [hwin]; exact hnonW
  obtain ⟨c, M, hle, hM1, hMB, hNc, hNcM, hint, hoddline⟩ :=
    exists_line_odd (Nbr G C v) (lineWeight G C Y v kS (LS' + 1)) ia (ia + C.length) hia
      ((nbr_periodic ia).mpr hia) (by omega) (exists_next_nbr hn hia) hodd
  -- edges of `S` have both ends `Y`-complete
  have hsegY : ∀ m, SegEdge C kS (LS' + 1) m →
      SegmentBasics.CycVert G Y C m ∧ SegmentBasics.CycVert G Y C (m + 1) := by
    rintro m ⟨s, hs, hm⟩
    refine ⟨(SegmentBasics.cycVert_congr hm).mp (hallS s (by omega)), ?_⟩
    refine (SegmentBasics.cycVert_congr (SegmentBasics.add_mod_congr hm 1)).mp ?_
    rw [show kS + s + 1 = kS + (s + 1) from by omega]
    exact hallS (s + 1) (by omega)
  -- a line of length 1 would carry a `Y ∪ {v}`-complete edge of `S`, which the weight forbids
  have hM2 : 2 ≤ M := by
    by_contra hcon
    have hM : M = 1 := by omega
    subst hM
    have hIco : Finset.Ico c (c + 1) = {c} := by ext x; simp
    rw [hIco, Finset.sum_singleton] at hoddline
    have hcase : SegEdge C kS (LS' + 1) c ∧ ¬ WheelParity.CycEdge G (Y ∪ {v}) C c := by
      by_contra hcw
      simp only [lineWeight, if_neg hcw] at hoddline
      exact hoddline ⟨0, rfl⟩
    obtain ⟨hse, hnce⟩ := hcase
    obtain ⟨hy0, hy1⟩ := hsegY c hse
    exact hnce ((YEdgeConfiguration.cycEdge_iff hC).mpr
      ⟨(cycVert_union_iff c).mpr ⟨hy0, hNc⟩,
        (cycVert_union_iff (c + 1)).mpr ⟨hy1, hNcM⟩⟩)
  -- inside a line of length ≥ 2 no edge is `Y ∪ {v}`-complete, so the weight counts edges of `S`
  have hsumeq : ∑ t ∈ Finset.Ico c (c + M), lineWeight G C Y v kS (LS' + 1) t
      = ∑ t ∈ Finset.Ico c (c + M), segEdgeInd C kS (LS' + 1) t := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hnoW : ¬ WheelParity.CycEdge G (Y ∪ {v}) C t := by
      intro hce
      obtain ⟨h1, h2⟩ := (YEdgeConfiguration.cycEdge_iff hC).mp hce
      have hb1 : Nbr G C v t := ((cycVert_union_iff t).mp h1).2
      have hb2 : Nbr G C v (t + 1) := ((cycVert_union_iff (t + 1)).mp h2).2
      obtain ⟨t', rfl⟩ : ∃ t', t = c + t' := ⟨t - c, by omega⟩
      have ht'0 : t' = 0 := by
        by_contra hcon
        exact hint t' (by omega) (by omega) hb1
      subst ht'0
      exact hint 1 (by omega) (by omega) (by simpa using hb2)
    simp only [lineWeight, segEdgeInd]
    by_cases h : SegEdge C kS (LS' + 1) t
    · rw [if_pos ⟨h, hnoW⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.1), if_neg h]
  exact ⟨c, M, hM2, line_length_lt hn hNc hint hia hib hres, hNc, hNcM, hint,
    by rw [← hsumeq]; exact hoddline⟩

end Rim

/-! ### The main statement -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y : Set V}
  {v a b : V}

/-- PAPER (16.3, claim (1), printed p. 101), the second half:

> *"Define a "line" to be a maximal subpath of `C` with no internal vertex adjacent to `v` …
> this contradicts the optimality of `(C,Y)`.  This proves (1)."*

The hypothesis `hnoseg` is the conclusion of Case A
(`OddWheelNoOddExtSegment.no_odd_ext_segment`), and `hmin` is the second half of the
*"optimality"* of `(C,Y)` fixed at the start of the proof of 16.3. -/
theorem no_bad_vertex_of_no_odd_ext_segment
    (hBerge : Berge G) (hG : InF6 G) (hw : IsWheel G C Y) (hodd : IsOddWheel G C Y)
    (hmin : ∀ C', IsOddWheel G C' Y →
      OptimalWheelChoice.yEdgeCount G Y C ≤ OptimalWheelChoice.yEdgeCount G Y C')
    (hvC : v ∉ C) (hvY : v ∉ Y) (hvnY : ¬ VertexComplete G v Y)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hnadj : ¬ G.Adj a b)
    (hab : OppositeWheelParity G C Y a b)
    (hnoseg : ¬ ∃ S, IsSegment G C (Y ∪ {v}) S ∧ Odd (pathLength S)) : False := by
  classical
  have hhole : IsHoleList G C := hw.1.1
  have hlen6 : 6 ≤ holeLength C := hw.1.2
  have hYne : Y.Nonempty := hw.2.1.1
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  have hCY : ∀ u ∈ C, u ∉ Y := hw.2.1.2.2
  have hn6 : 6 ≤ C.length := hlen6
  have hn : 0 < C.length := by omega
  have hnd : C.Nodup := hhole.2.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  have hCeven : Even C.length := hBerge.1 C hhole
  -- the positions of `a` and `b`
  have haC : a ∈ C := hab.2.1
  have hbC : b ∈ C := hab.2.2.1
  have hne_ab : a ≠ b := hab.1
  obtain ⟨ia, hia_lt, hia_eq⟩ := List.getElem_of_mem haC
  obtain ⟨ib, hib_lt, hib_eq⟩ := List.getElem_of_mem hbC
  have hia_mod : ia % C.length = ia := Nat.mod_eq_of_lt hia_lt
  have hib_mod : ib % C.length = ib := Nat.mod_eq_of_lt hib_lt
  have hiab : ia ≠ ib := by
    intro hcon
    exact hne_ab (by rw [← hia_eq, ← hib_eq]; exact (List.Nodup.getElem_inj_iff hnd).mpr hcon)
  have hres : ia % C.length ≠ ib % C.length := by rw [hia_mod, hib_mod]; exact hiab
  have hNia : Nbr G C v ia := by
    have hxe : (C[ia % C.length]'(Nat.mod_lt _ hn)) = (C[ia]'hia_lt) :=
      (List.Nodup.getElem_inj_iff hnd).mpr hia_mod
    rw [nbr_getElem_iff hn, hxe, hia_eq]
    exact hva.symm
  have hNib : Nbr G C v ib := by
    have hxe : (C[ib % C.length]'(Nat.mod_lt _ hn)) = (C[ib]'hib_lt) :=
      (List.Nodup.getElem_inj_iff hnd).mpr hib_mod
    rw [nbr_getElem_iff hn, hxe, hib_eq]
    exact hvb.symm
  -- the odd `Y`-segment `S`, as a run of cyclic positions
  obtain ⟨S, hS, hSodd⟩ := hodd.2
  have hSpath : IsPathList G S := hS.1.1
  have hSlen1 : 1 ≤ S.length := PathBasics.path_length_pos hSpath
  have hSeven : Even S.length := (SegmentBasics.odd_pathLength_iff_even_length hSlen1).mp hSodd
  have hSle : S.length + 1 ≤ C.length := by
    obtain ⟨k, hk⟩ := hS.1.2.1
    rcases hk with h | h
    · exact SegmentBasics.length_le_of_path_prefix hhole hSpath h
    · have := SegmentBasics.length_le_of_path_prefix hhole
        (PathBasics.isPathList_reverse hSpath) h
      simpa using this
  have hSle2 : S.length + 2 ≤ C.length := by
    obtain ⟨r, hr⟩ := hSeven
    obtain ⟨r', hr'⟩ := hCeven
    omega
  obtain ⟨kS, -, hallS, hnextS, hprevS, hmemS⟩ := SegmentBasics.isSegment_run hhole hS hSle2
  -- the line `L`
  obtain ⟨c, M, hM2, hMlt, hNc, hNcM, hint, hoddSE⟩ :=
    exists_odd_line hhole hNia hNib hres hnoseg hSlen1 hSle hSeven hallS hnextS hprevS
  -- `%`-free reading of the two ends of the line
  have hrlt : c % C.length < C.length := Nat.mod_lt _ hn
  have hcM : (c + M) % C.length
      = if c % C.length + M < C.length then c % C.length + M
        else c % C.length + M - C.length := by
    rw [← Nat.mod_add_mod]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have hEq : c % C.length + M = (c % C.length + M - C.length) + C.length := by omega
      conv_lhs => rw [hEq]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- a line cannot have length `C.length - 1`, else `a` and `b` would be adjacent
  have hMn : M + 2 ≤ C.length := by
    rcases Nat.lt_or_ge M (C.length - 1) with h | h
    · omega
    exfalso
    have hMeq : M = C.length - 1 := by omega
    obtain ⟨t₁, ht₁, hc₁, he₁⟩ := nbr_offset_of_line hn hint hNia
    obtain ⟨t₂, ht₂, hc₂, he₂⟩ := nbr_offset_of_line hn hint hNib
    have ht₁' : t₁ = 0 ∨ t₁ = C.length - 1 := by rcases hc₁ with h' | h' <;> omega
    have ht₂' : t₂ = 0 ∨ t₂ = C.length - 1 := by rcases hc₂ with h' | h' <;> omega
    have htne : t₁ ≠ t₂ := by
      intro hcon; subst hcon; exact hres (he₁.symm.trans he₂)
    -- one of the two is `c`, the other its cyclic predecessor, so they are adjacent
    have key : ∀ (u₁ u₂ : ℕ) (hu₁ : u₁ < C.length) (hu₂ : u₂ < C.length),
        (c + 0) % C.length = u₁ % C.length →
        (c + (C.length - 1)) % C.length = u₂ % C.length →
        G.Adj (C[u₂]'hu₂) (C[u₁]'hu₁) := by
      intro u₁ u₂ hu₁ hu₂ e₁ e₂
      refine (HoleBasics.hole_adj_iff hhole hu₂ hu₁).mpr (Or.inl ?_)
      have hstep : (u₂ + 1) % C.length = u₁ % C.length := by
        rw [← Nat.mod_add_mod u₂ C.length 1, ← e₂, Nat.mod_add_mod,
          show c + (C.length - 1) + 1 = c + C.length from by omega, Nat.add_mod_right]
        simpa using e₁
      rw [Nat.mod_eq_of_lt hu₁] at hstep
      exact hstep.symm
    rcases ht₁' with rfl | rfl
    · rcases ht₂' with rfl | rfl
      · exact htne rfl
      · have hkey := key ia ib hia_lt hib_lt he₁ he₂
        rw [hia_eq, hib_eq] at hkey
        exact hnadj hkey.symm
    · rcases ht₂' with rfl | rfl
      · have hkey := key ib ia hib_lt hia_lt he₂ he₁
        rw [hia_eq, hib_eq] at hkey
        exact hnadj hkey
      · exact htne rfl
  -- the arc `L` of the rim carrying the line
  have hMle : M + 1 + 1 ≤ C.length := by omega
  have hLpath : IsPathList G ((C.rotate c).take (M + 1)) :=
    WheelParity.isPathList_rotate_take hhole (by omega) hMle
  have hLlen : ((C.rotate c).take (M + 1)).length = M + 1 := by
    simp only [List.length_take, List.length_rotate]; omega
  have hLget : ∀ (j : ℕ) (hjl : j < ((C.rotate c).take (M + 1)).length),
      ((C.rotate c).take (M + 1))[j]'hjl = (C[(c + j) % C.length]'(Nat.mod_lt _ hn)) :=
    fun j hjl => SegmentBasics.arc_getElem hn hjl
  have hLmem : ∀ x : V, x ∈ (C.rotate c).take (M + 1) ↔ SegmentBasics.OnArc C c (M + 1) x :=
    fun x => SegmentBasics.mem_arc_iff hn (by omega)
  have hLfrom : IsPathFrom G ((C.rotate c).take (M + 1))
      (C[c % C.length]'(Nat.mod_lt _ hn)) (C[(c + M) % C.length]'(Nat.mod_lt _ hn)) :=
    WheelParity.arc_isPathFrom hhole (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (by omega) hMle rfl
      (by rw [show c + (M + 1) - 1 = c + M from by omega])
  set pp : V := (C[c % C.length]'(Nat.mod_lt _ hn)) with hppdef
  set qq : V := (C[(c + M) % C.length]'(Nat.mod_lt _ hn)) with hqqdef
  set L : List V := (C.rotate c).take (M + 1) with hLdef
  -- vertices of `L` lie on `C`
  have hLsubC : ∀ x ∈ L, x ∈ C := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := (hLmem x).mp hx
    exact SegmentBasics.mem_of_pos hn hxt
  -- only the two ends of `L` are adjacent to `v`
  have hLadjv : ∀ x ∈ L, (G.Adj x v ↔ (x = qq ∨ x = pp)) := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := (hLmem x).mp hx
    have hxeq : (C[(c + t) % C.length]'(Nat.mod_lt _ hn)) = x := by
      rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hxt
      exact Option.some_injective _ hxt
    constructor
    · intro hadjx
      have hNbt : Nbr G C v (c + t) :=
        (nbr_getElem_iff hn (c + t)).mpr (by rw [hxeq]; exact hadjx)
      have ht0 : t = 0 ∨ t = M := by
        by_contra hcon
        push Not at hcon
        exact hint t (by omega) (by omega) hNbt
      rcases ht0 with rfl | rfl
      · exact Or.inr hxeq.symm
      · exact Or.inl hxeq.symm
    · rintro (rfl | rfl)
      · exact (nbr_getElem_iff hn (c + M)).mp hNcM
      · exact (nbr_getElem_iff hn c).mp hNc
  -- the hole `H = v-p-L-q-v`
  have hvL : v ∉ L := fun hmem => hvC (hLsubC v hmem)
  have hHhole : IsHoleList G (L ++ [v]) := by
    refine PathGlue.glue_hole hLfrom ⟨PathBasics.isPathList_singleton G v, rfl, rfl⟩
      (fun x hx hmem => hvL (by rwa [List.mem_singleton.mp hmem] at hx)) ?_
      (by simp only [hLlen, List.length_singleton]; omega)
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    rw [hLadjv x hx]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨h, rfl⟩
      · exact Or.inr ⟨h, rfl⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
  have hHlen : (L ++ [v]).length = M + 2 := by simp [hLlen]
  -- the dictionary between positions of `H` and positions of `C`
  have hHcyc : ∀ j, j ≤ M →
      (SegmentBasics.CycVert G Y (L ++ [v]) j ↔ SegmentBasics.CycVert G Y C (c + j)) := by
    intro j hj
    have hjlt' : j < L.length := by rw [hLlen]; omega
    have hjlt : j < (L ++ [v]).length := by rw [hHlen]; omega
    have h1 : j % (L ++ [v]).length = j := by rw [hHlen]; exact Nat.mod_eq_of_lt (by omega)
    have h2 : (L ++ [v])[j % (L ++ [v]).length]? = C[(c + j) % C.length]? := by
      rw [h1, List.getElem?_eq_getElem hjlt, List.getElem?_eq_getElem (Nat.mod_lt _ hn)]
      congr 1
      rw [List.getElem_append_left hjlt']
      exact hLget j hjlt'
    simp only [SegmentBasics.CycVert, h2]
  have hHcycv : ¬ SegmentBasics.CycVert G Y (L ++ [v]) (M + 1) := by
    rintro ⟨u, hu, hcu⟩
    have h1 : (M + 1) % (L ++ [v]).length = M + 1 := by
      rw [hHlen]; exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hu
    have hjlt : M + 1 < (L ++ [v]).length := by rw [hHlen]; omega
    have hge : L.length ≤ M + 1 := by rw [hLlen]
    have h2 : (L ++ [v])[M + 1]'hjlt = v := by
      rw [List.getElem_append_right hge]
      simp [hLlen]
    rw [List.getElem?_eq_getElem hjlt, h2] at hu
    exact hvnY (by rw [Option.some_injective _ hu]; exact hcu)
  -- the two ends of the line are distinct and nonadjacent
  have hppqq : pp ≠ qq :=
    HoleBasics.hole_ne_of_ne_index hhole (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
      (by rw [hcM]; split_ifs <;> omega)
  have hLlen3 : 3 ≤ L.length := by rw [hLlen]; omega
  have hL0 : L[0]'(by omega) = pp := PathBasics.getElem_zero_of_head? hLfrom.2.1 (by omega)
  have hLlast : L[L.length - 1]'(by omega) = qq :=
    PathBasics.getElem_last_of_getLast? hLfrom.2.2 (by omega)
  have hpqnadj : ¬ G.Adj pp qq := by
    have hnn := PathBasics.path_ends_not_adj hLpath hLlen3
    rw [hL0, hLlast] at hnn
    exact hnn
  have hvpp : G.Adj v pp := ((nbr_getElem_iff hn c).mp hNc).symm
  have hvqq : G.Adj v qq := ((nbr_getElem_iff hn (c + M)).mp hNcM).symm
  have hppC : pp ∈ C := List.getElem_mem _
  have hqqC : qq ∈ C := List.getElem_mem _
  have hLpre : L <+: C.rotate c := by rw [hLdef]; exact List.take_prefix _ _
  -- **By 16.1**, `p` and `q` have the same wheel-parity
  have hsame : SameWheelParity G C Y pp qq := by
    by_contra hcon
    have h161 := (_root_.Workspace.Statements.S16.SPGT.thm_16_1 G hG C Y hw v hvC hvY hvnY
      pp qq hvpp hvqq ⟨hppqq, hppC, hqqC, hcon⟩).1
    obtain ⟨x, hxL, y, hyL, hExy⟩ := h161 L hLpath ⟨c, Or.inl hLpre⟩ (Or.inl hLfrom)
    have hxv : G.Adj x v := (vertexComplete_union.mp hExy.2.1).2
    have hyv : G.Adj y v := (vertexComplete_union.mp hExy.2.2).2
    have hx' := (hLadjv x hxL).mp hxv
    have hy' := (hLadjv y hyL).mp hyv
    have hxyne : x ≠ y := hExy.1.ne
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact hxyne rfl
    · exact hpqnadj hExy.1.symm
    · exact hpqnadj hExy.1
    · exact hxyne rfl
  -- so an even number of edges of the line are `Y`-complete
  have hpar1 : WheelParity.cycCount G Y C c % 2 = WheelParity.cycCount G Y C (c + M) % 2 := by
    have h1 := WheelParity.cycCount_mod_two heven c
    have h2 := WheelParity.cycCount_mod_two heven (c + M)
    have h3 := (WheelParity.sameWheelParity_iff hhole heven (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
      (by rw [hcM]; split_ifs <;> omega)).mp hsame
    omega
  have hIco : ∑ t ∈ Finset.Ico c (c + M), (if WheelParity.CycEdge G Y C t then 1 else 0)
      = ∑ t ∈ Finset.range M, (if WheelParity.CycEdge G Y C (c + t) then 1 else 0) := by
    rw [Finset.sum_Ico_eq_sum_range, show c + M - c = M from by omega]
  have hYeven : Even (∑ t ∈ Finset.Ico c (c + M),
      (if WheelParity.CycEdge G Y C t then 1 else 0)) := by
    rw [hIco, Nat.even_iff]
    have hadd := WheelParity.cycCount_add (G := G) (Y := Y) (C := C) c M
    omega
  -- an edge of `S` inside the line
  obtain ⟨t₀, ht₀a, ht₀b, ht₀SE⟩ : ∃ t, c ≤ t ∧ t < c + M ∧ SegEdge C kS S.length t := by
    by_contra hcon
    push Not at hcon
    refine hoddSE ?_
    have hz : ∀ t ∈ Finset.Ico c (c + M), segEdgeInd C kS S.length t = 0 := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      simp only [segEdgeInd]
      exact if_neg (hcon t ht.1 ht.2)
    rw [Finset.sum_congr rfl hz]
    simp
  -- a `Y`-complete edge of the line that is not an edge of `S`
  obtain ⟨t₁, ht₁a, ht₁b, ht₁Y, ht₁nS⟩ :
      ∃ t, c ≤ t ∧ t < c + M ∧ WheelParity.CycEdge G Y C t ∧ ¬ SegEdge C kS S.length t := by
    by_contra hcon
    push Not at hcon
    refine hoddSE ?_
    have hz : ∀ t ∈ Finset.Ico c (c + M), segEdgeInd C kS S.length t
        = (if WheelParity.CycEdge G Y C t then 1 else 0) := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      simp only [segEdgeInd]
      by_cases hse : SegEdge C kS S.length t
      · have hce : WheelParity.CycEdge G Y C t :=
          (YEdgeConfiguration.cycEdge_iff hhole).mpr
            (((segEdge_iff_inSeg hn hSle).mp hse).imp (cycVert_of_inSeg hallS)
              (cycVert_of_inSeg hallS))
        rw [if_pos hse, if_pos hce]
      · have hce : ¬ WheelParity.CycEdge G Y C t := fun hcc => hse (hcon t ht.1 ht.2 hcc)
        rw [if_neg hse, if_neg hce]
    rw [Finset.sum_congr rfl hz]
    exact hYeven
  -- the two edges are disjoint
  have ht₀InS : InSeg C kS S.length t₀ ∧ InSeg C kS S.length (t₀ + 1) :=
    (segEdge_iff_inSeg hn hSle).mp ht₀SE
  have ht₁nInS : ¬ InSeg C kS S.length t₁ := by
    intro hin
    have h2 : SegmentBasics.CycVert G Y C (t₁ + 1) :=
      ((YEdgeConfiguration.cycEdge_iff hhole).mp ht₁Y).2
    by_cases hin2 : InSeg C kS S.length (t₁ + 1)
    · exact ht₁nS ((segEdge_iff_inSeg hn hSle).mpr ⟨hin, hin2⟩)
    · exact not_cycVert_of_inSeg_right hnextS hin hin2 h2
  have ht₁nInS' : ¬ InSeg C kS S.length (t₁ + 1) := by
    intro hin2
    have h1 : SegmentBasics.CycVert G Y C t₁ :=
      ((YEdgeConfiguration.cycEdge_iff hhole).mp ht₁Y).1
    exact not_cycVert_of_inSeg_left hn hprevS hin2 ht₁nInS h1
  have hne₁ : t₀ % C.length ≠ t₁ % C.length := fun he =>
    ht₁nInS ((inSeg_congr he).mp ht₀InS.1)
  have hne₂ : t₀ % C.length ≠ (t₁ + 1) % C.length := fun he =>
    ht₁nInS' ((inSeg_congr he).mp ht₀InS.1)
  have hne₃ : (t₀ + 1) % C.length ≠ t₁ % C.length := fun he =>
    ht₁nInS ((inSeg_congr he).mp ht₀InS.2)
  have hne₄ : (t₀ + 1) % C.length ≠ (t₁ + 1) % C.length := fun he =>
    ht₁nInS' ((inSeg_congr he).mp ht₀InS.2)
  have hmemH : ∀ t : ℕ, c ≤ t → t ≤ c + M →
      (C[t % C.length]'(Nat.mod_lt _ hn)) ∈ L ++ [v] := by
    intro t h1 h2
    refine List.mem_append_left _ ((hLmem _).mpr ⟨t - c, by omega, ?_⟩)
    rw [show c + (t - c) = t from by omega]
    exact List.getElem?_eq_getElem (Nat.mod_lt _ hn)
  have hE₀ : EdgeComplete G Y (C[t₀ % C.length]'(Nat.mod_lt _ hn))
      (C[(t₀ + 1) % C.length]'(Nat.mod_lt _ hn)) :=
    edgeComplete_of_cycEdge hn ((YEdgeConfiguration.cycEdge_iff hhole).mpr
      (ht₀InS.imp (cycVert_of_inSeg hallS) (cycVert_of_inSeg hallS)))
  have hE₁ : EdgeComplete G Y (C[t₁ % C.length]'(Nat.mod_lt _ hn))
      (C[(t₁ + 1) % C.length]'(Nat.mod_lt _ hn)) := edgeComplete_of_cycEdge hn ht₁Y
  -- `H` has length ≥ 6
  have ht₀t₁ : t₀ ≠ t₁ := fun he => hne₁ (by rw [he])
  have ht₀t₁' : t₀ ≠ t₁ + 1 := fun he => hne₂ (by rw [he])
  have ht₁t₀' : t₁ ≠ t₀ + 1 := fun he => hne₃ (by rw [he])
  have hHevenLen : Even ((L ++ [v]).length) := hBerge.1 _ hHhole
  have hM4 : 4 ≤ M := by
    rw [hHlen] at hHevenLen
    obtain ⟨r, hr⟩ := hHevenLen
    omega
  have hHY : ∀ u ∈ L ++ [v], u ∉ Y := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact hCY u (hLsubC u h)
    · rw [List.mem_singleton.mp h]; exact hvY
  have hHwheel : IsWheel G (L ++ [v]) Y :=
    ⟨⟨hHhole, by show 6 ≤ (L ++ [v]).length; rw [hHlen]; omega⟩,
      ⟨hYne, hYanti, hHY⟩,
      C[t₀ % C.length]'(Nat.mod_lt _ hn), C[(t₀ + 1) % C.length]'(Nat.mod_lt _ hn),
      C[t₁ % C.length]'(Nat.mod_lt _ hn), C[(t₁ + 1) % C.length]'(Nat.mod_lt _ hn),
      hmemH t₀ ht₀a (by omega), hmemH (t₀ + 1) (by omega) (by omega),
      hmemH t₁ ht₁a (by omega), hmemH (t₁ + 1) (by omega) (by omega),
      hE₀, hE₁,
      HoleBasics.hole_ne_of_ne_index hhole _ _ hne₁,
      HoleBasics.hole_ne_of_ne_index hhole _ _ hne₂,
      HoleBasics.hole_ne_of_ne_index hhole _ _ hne₃,
      HoleBasics.hole_ne_of_ne_index hhole _ _ hne₄⟩
  -- **`(H, Y)` is an odd wheel**: an odd number of edges of `S` lie on `L`, and those edges
  -- form one or two `Y`-segments of `H`, one of which is odd
  have hMod : ∀ i : ℕ, i < M + 2 → (M + 2 + i) % (M + 2) = i := by
    intro i hi
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hi]
  have hModM1 : (M + 1) % (M + 2) = M + 1 := Nat.mod_eq_of_lt (by omega)
  have hu2 : (2 * M + 3) % (M + 2) = M + 1 := by
    rw [show 2 * M + 3 = (M + 2) + (M + 1) from by omega, Nat.add_mod_left, hModM1]
  have hsumH : ∑ jj ∈ Finset.Ico (M + 1) (M + 1 + (M + 2)),
        pairInd (OnSegH C kS S.length c M) jj
      = ∑ t ∈ Finset.Ico c (c + M), segEdgeInd C kS S.length t := by
    rw [Finset.sum_Ico_eq_sum_range, show M + 1 + (M + 2) - (M + 1) = M + 2 from by omega,
      Finset.sum_range_succ' (fun i => pairInd (OnSegH C kS S.length c M) (M + 1 + i)) (M + 1),
      Finset.sum_range_succ
        (fun i => pairInd (OnSegH C kS S.length c M) (M + 1 + (i + 1))) M]
    have e0 : pairInd (OnSegH C kS S.length c M) (M + 1 + 0) = 0 := by
      refine pairInd_eq_zero_left ?_
      rintro ⟨hne, -⟩
      exact hne hModM1
    have e2 : pairInd (OnSegH C kS S.length c M) (M + 1 + (M + 1)) = 0 := by
      refine pairInd_eq_zero_right ?_
      rintro ⟨hne, -⟩
      exact hne (by rw [show M + 1 + (M + 1) + 1 = 2 * M + 3 from by omega]; exact hu2)
    have e1 : ∀ i ∈ Finset.range M,
        pairInd (OnSegH C kS S.length c M) (M + 1 + (i + 1))
          = segEdgeInd C kS S.length (c + i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hA : (M + 1 + (i + 1)) % (M + 2) = i := by
        rw [show M + 1 + (i + 1) = M + 2 + i from by omega]
        exact hMod i (by omega)
      have hB : (M + 1 + (i + 1) + 1) % (M + 2) = i + 1 := by
        rw [show M + 1 + (i + 1) + 1 = M + 2 + (i + 1) from by omega]
        exact hMod (i + 1) (by omega)
      have hP : OnSegH C kS S.length c M (M + 1 + (i + 1))
          ↔ InSeg C kS S.length (c + i) := by
        simp only [OnSegH, hA]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      have hQ : OnSegH C kS S.length c M (M + 1 + (i + 1) + 1)
          ↔ InSeg C kS S.length (c + i + 1) := by
        simp only [OnSegH, hB, show c + (i + 1) = c + i + 1 from by omega]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      simp only [pairInd, segEdgeInd]
      by_cases hse : SegEdge C kS S.length (c + i)
      · have hin := (segEdge_iff_inSeg hn hSle).mp hse
        rw [if_pos ⟨hP.mpr hin.1, hQ.mpr hin.2⟩, if_pos hse]
      · have hnot : ¬ (OnSegH C kS S.length c M (M + 1 + (i + 1)) ∧
            OnSegH C kS S.length c M (M + 1 + (i + 1) + 1)) := by
          rintro ⟨h1, h2⟩
          exact hse ((segEdge_iff_inSeg hn hSle).mpr ⟨hP.mp h1, hQ.mp h2⟩)
        rw [if_neg hnot, if_neg hse]
    rw [Finset.sum_congr rfl e1, e0, e2, Finset.sum_Ico_eq_sum_range,
      show c + M - c = M from by omega]
    simp
  obtain ⟨kH, MH, hkHa, hMH1, hkHb, hHrun, hHnext, hHprev, hMHeven⟩ :=
    exists_even_run (OnSegH C kS S.length c M) (M + 1) (M + 1 + (M + 2)) (by omega)
      (by rintro ⟨hne, -⟩; exact hne hModM1)
      (by rintro ⟨hne, -⟩
          exact hne (by rw [show M + 1 + (M + 2) = 2 * M + 3 from by omega]; exact hu2))
      (by rw [hsumH]; exact hoddSE)
  obtain ⟨j, rfl⟩ : ∃ j, kH = M + 2 + j := ⟨kH - (M + 2), by omega⟩
  have hjMH : j + MH ≤ M + 1 := by omega
  have hmodj : ∀ i, i ≤ M + 1 → (M + 2 + i) % (M + 2) = i := fun i hi => hMod i (by omega)
  have hHrun' : ∀ t, t < MH → InSeg C kS S.length (c + j + t) := by
    intro t ht
    obtain ⟨-, hin⟩ := hHrun t ht
    have he : (M + 2 + j + t) % (M + 2) = j + t := by
      rw [show M + 2 + j + t = M + 2 + (j + t) from by omega]
      exact hmodj (j + t) (by omega)
    rw [he] at hin
    rw [show c + j + t = c + (j + t) from by omega]
    exact hin
  have hallH : ∀ t, t < MH → SegmentBasics.CycVert G Y (L ++ [v]) (j + t) := by
    intro t ht
    refine (hHcyc (j + t) (by omega)).mpr ?_
    rw [show c + (j + t) = c + j + t from by omega]
    exact cycVert_of_inSeg hallS (hHrun' t ht)
  have hnextH : ¬ SegmentBasics.CycVert G Y (L ++ [v]) (j + MH) := by
    rcases Nat.eq_or_lt_of_le hjMH with heq | hlt
    · rw [heq]; exact hHcycv
    · have he : (M + 2 + j + MH) % (M + 2) = j + MH := by
        rw [show M + 2 + j + MH = M + 2 + (j + MH) from by omega]
        exact hmodj (j + MH) (by omega)
      have hnot : ¬ InSeg C kS S.length (c + (j + MH)) := by
        intro hin
        refine hHnext ⟨?_, ?_⟩
        · rw [he]; omega
        · rw [he]; exact hin
      have hprevIn : InSeg C kS S.length (c + j + (MH - 1)) := hHrun' (MH - 1) (by omega)
      have hstep : c + j + (MH - 1) + 1 = c + (j + MH) := by omega
      intro hcv
      exact not_cycVert_of_inSeg_right hnextS hprevIn (by rw [hstep]; exact hnot)
        (by rw [hstep]; exact (hHcyc (j + MH) (by omega)).mp hcv)
  have hprevH : ¬ SegmentBasics.CycVert G Y (L ++ [v]) (j + ((L ++ [v]).length - 1)) := by
    rw [hHlen]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using hHcycv
    · have hmodp : (j + (M + 2 - 1)) % (M + 2) = j - 1 := by
        rw [show j + (M + 2 - 1) = M + 2 + (j - 1) from by omega]
        exact hmodj (j - 1) (by omega)
      have hcong : SegmentBasics.CycVert G Y (L ++ [v]) (j + (M + 2 - 1))
          ↔ SegmentBasics.CycVert G Y (L ++ [v]) (j - 1) :=
        SegmentBasics.cycVert_congr (by
          rw [hHlen, hmodp, Nat.mod_eq_of_lt (show j - 1 < M + 2 from by omega)])
      rw [hcong]
      intro hcv
      have hcv' : SegmentBasics.CycVert G Y C (c + (j - 1)) :=
        (hHcyc (j - 1) (by omega)).mp hcv
      have he : (M + 2 + j - 1) % (M + 2) = j - 1 := by
        rw [show M + 2 + j - 1 = M + 2 + (j - 1) from by omega]
        exact hmodj (j - 1) (by omega)
      have hnot : ¬ InSeg C kS S.length (c + (j - 1)) := by
        intro hin
        refine hHprev ⟨?_, ?_⟩
        · rw [he]; omega
        · rw [he]; exact hin
      have hinj : InSeg C kS S.length (c + j) := by
        have h0 := hHrun' 0 (by omega)
        rw [Nat.add_zero] at h0
        exact h0
      exact not_cycVert_of_inSeg_left hn hprevS
        (by rw [show c + (j - 1) + 1 = c + j from by omega]; exact hinj) hnot hcv'
  have hsegH : IsSegment G (L ++ [v]) Y (((L ++ [v]).rotate j).take MH) :=
    SegmentBasics.isSegment_of_run hHhole hMH1 (by rw [hHlen]; omega) hallH hnextH hprevH
  have hsegHlen : (((L ++ [v]).rotate j).take MH).length = MH := by
    simp only [List.length_take, List.length_rotate, hHlen]
    omega
  have hHodd : IsOddWheel G (L ++ [v]) Y := by
    refine ⟨hHwheel, _, hsegH, ?_⟩
    rw [SegmentBasics.odd_pathLength_iff_even_length (by rw [hsegHlen]; omega), hsegHlen]
    exact hMHeven
  -- **By 16.1** again: there is a `Y ∪ {v}`-complete edge of `C`, and it does not lie on `L`
  have hdd : (ib + C.length - ia) % C.length
      = if ia ≤ ib then ib - ia else ib + C.length - ia := by
    split_ifs with h
    · rw [show ib + C.length - ia = (ib - ia) + C.length from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have hdd0 : (ib + C.length - ia) % C.length ≠ 0 := by
    rw [hdd]; split_ifs <;> omega
  have hddn : (ib + C.length - ia) % C.length ≠ C.length - 1 := by
    intro hcon
    rw [hdd] at hcon
    refine hnadj ?_
    rw [← hia_eq, ← hib_eq]
    refine (HoleBasics.hole_adj_iff hhole hia_lt hib_lt).mpr (Or.inr ?_)
    split_ifs at hcon with h
    · rw [show ia = 0 from by omega, show ib = C.length - 1 from by omega,
        show C.length - 1 + 1 = C.length from by omega, Nat.mod_self]
    · rw [show ia = ib + 1 from by omega, Nat.mod_eq_of_lt (by omega)]
  have hddlt : (ib + C.length - ia) % C.length < C.length := Nat.mod_lt _ hn
  have hkq : (ia + ((ib + C.length - ia) % C.length + 1) - 1) % C.length = ib := by
    rw [show ia + ((ib + C.length - ia) % C.length + 1) - 1
      = ia + (ib + C.length - ia) % C.length from by omega, Nat.add_mod_mod,
      show ia + (ib + C.length - ia) = ib + C.length from by omega, Nat.add_mod_right, hib_mod]
  have hPfrom : IsPathFrom G ((C.rotate ia).take ((ib + C.length - ia) % C.length + 1)) a b := by
    have hh := WheelParity.arc_isPathFrom hhole hia_lt hib_lt (by omega) (by omega) hia_mod hkq
    rw [hia_eq, hib_eq] at hh
    exact hh
  obtain ⟨x, hxP, y, hyP, hExy⟩ :=
    (_root_.Workspace.Statements.S16.SPGT.thm_16_1 G hG C Y hw v hvC hvY hvnY a b hva hvb hab).1
      ((C.rotate ia).take ((ib + C.length - ia) % C.length + 1)) hPfrom.1
      ⟨ia, Or.inl (List.take_prefix _ _)⟩ (Or.inl hPfrom)
  have hPsubC : ∀ z ∈ (C.rotate ia).take ((ib + C.length - ia) % C.length + 1), z ∈ C := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := (SegmentBasics.mem_arc_iff hn (by omega)).mp hz
    exact SegmentBasics.mem_of_pos hn hzt
  have hxC : x ∈ C := hPsubC x hxP
  have hyC : y ∈ C := hPsubC y hyP
  have hExyY : EdgeComplete G Y x y :=
    ⟨hExy.1, (vertexComplete_union.mp hExy.2.1).1, (vertexComplete_union.mp hExy.2.2).1⟩
  have hsubset :
      {e : Sym2 V | ∃ u ∈ L ++ [v], ∃ w ∈ L ++ [v], e = s(u, w) ∧ EdgeComplete G Y u w}
        ⊆ {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C, e = s(u, w) ∧ EdgeComplete G Y u w} := by
    rintro e ⟨u, hu, w, hw, rfl, hE⟩
    have huL : u ∈ L := by
      rcases List.mem_append.mp hu with h | h
      · exact h
      · exfalso
        rw [List.mem_singleton.mp h] at hE
        exact hvnY hE.2.1
    have hwL : w ∈ L := by
      rcases List.mem_append.mp hw with h | h
      · exact h
      · exfalso
        rw [List.mem_singleton.mp h] at hE
        exact hvnY hE.2.2
    exact ⟨u, hLsubC u huL, w, hLsubC w hwL, rfl, hE⟩
  have hnotmem : s(x, y) ∉
      {e : Sym2 V | ∃ u ∈ L ++ [v], ∃ w ∈ L ++ [v], e = s(u, w) ∧ EdgeComplete G Y u w} := by
    rintro ⟨u, hu, w, hw, heq, hE⟩
    have hxyH : x ∈ L ++ [v] ∧ y ∈ L ++ [v] := by
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [h1]; exact hu, by rw [h2]; exact hw⟩
      · exact ⟨by rw [h1]; exact hw, by rw [h2]; exact hu⟩
    have hxv : G.Adj x v := (vertexComplete_union.mp hExy.2.1).2
    have hyv : G.Adj y v := (vertexComplete_union.mp hExy.2.2).2
    have hxL : x ∈ L := by
      rcases List.mem_append.mp hxyH.1 with h | h
      · exact h
      · exfalso; rw [List.mem_singleton.mp h] at hxv; exact G.irrefl hxv
    have hyL : y ∈ L := by
      rcases List.mem_append.mp hxyH.2 with h | h
      · exact h
      · exfalso; rw [List.mem_singleton.mp h] at hyv; exact G.irrefl hyv
    have hx' := (hLadjv x hxL).mp hxv
    have hy' := (hLadjv y hyL).mp hyv
    have hxyne : x ≠ y := hExy.1.ne
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact hxyne rfl
    · exact hpqnadj hExy.1.symm
    · exact hpqnadj hExy.1
    · exact hxyne rfl
  have hmemC : s(x, y) ∈ {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C, e = s(u, w) ∧ EdgeComplete G Y u w} :=
    ⟨x, hxC, y, hyC, rfl, hExyY⟩
  have hstrict : OptimalWheelChoice.yEdgeCount G Y (L ++ [v])
      < OptimalWheelChoice.yEdgeCount G Y C := by
    rw [OptimalWheelChoice.yEdgeCount_def, OptimalWheelChoice.yEdgeCount_def]
    exact Set.ncard_lt_ncard ⟨hsubset, fun hsup => hnotmem (hsup hmemC)⟩ (Set.toFinite _)
  exact absurd (hmin (L ++ [v]) hHodd) (by omega)

end Main

end Workspace.ProofLemmas.OddWheelLines
