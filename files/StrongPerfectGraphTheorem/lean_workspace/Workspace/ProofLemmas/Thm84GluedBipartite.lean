import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems

/-!
# The glued subdivision is bipartite

Proof of `glued_isBipartite`.  The argument follows the paper: a cycle of `Hs` traverses whole
tracks, hence projects to a cycle of `J`, whose track lengths sum to an even number by the
cycle-parity equation `hcycle`; so `Hs` has no odd cycle and is `2`-colourable.

Formally we run the same argument in the equivalent "potential" form, which is what makes it
constructive:

* Section `WalkTools` shows that the weighted length `walkSum L` of any **closed walk** of `J`
  is even, where `L u v = trackLength (T u v)`.  A closed walk with distinct interior vertices
  *is* a cycle of `J` in the list encoding `hcycle` uses (`cycle_case`), and a closed walk with
  a repeated vertex splits off a strictly shorter nontrivial closed sub-walk
  (`split_of_not_nodup`); strong induction on the length finishes.
* `exists_potential` turns that into a parity potential `f : U → ZMod 2` with
  `f v = f u + L u v` for every edge `uv` of `J` (integrate `L` along a walk from a chosen
  representative of the connected component; well defined precisely because closed walks are
  even).
* `gcol` then colours a vertex of `Hs` lying at position `i` of the track `T u v` by
  `f u + i`; the track disjointness axioms make this well defined, and consecutive positions
  get different colours, which is exactly a proper `2`-colouring of `Hs`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84GluedBipartite

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

section WalkTools

variable {U : Type*} {J : SimpleGraph U}

/-- The `L`-weighted length of a walk of `J`. -/
def walkSum (L : U → U → ℕ) {a b : U} (w : J.Walk a b) : ℕ :=
  (w.darts.map (fun d => L d.toProd.1 d.toProd.2)).sum

theorem walkSum_nil (L : U → U → ℕ) (a : U) :
    walkSum L (SimpleGraph.Walk.nil : J.Walk a a) = 0 := by
  simp [walkSum]

theorem walkSum_cons (L : U → U → ℕ) {a b c : U} (h : J.Adj a b) (p : J.Walk b c) :
    walkSum L (SimpleGraph.Walk.cons h p) = L a b + walkSum L p := by
  simp [walkSum, SimpleGraph.Walk.darts_cons]

theorem walkSum_append (L : U → U → ℕ) {a b c : U} (p : J.Walk a b) (q : J.Walk b c) :
    walkSum L (p.append q) = walkSum L p + walkSum L q := by
  simp [walkSum, SimpleGraph.Walk.darts_append]

theorem walkSum_of_length_zero (L : U → U → ℕ) {a b : U} (p : J.Walk a b) (h : p.length = 0) :
    walkSum L p = 0 := by
  have hd : p.darts = [] := by
    have := SimpleGraph.Walk.length_darts p
    rw [h] at this
    exact List.eq_nil_of_length_eq_zero this
  simp [walkSum, hd]

theorem exists_cons_of_pos_length {b a : U} (p : J.Walk b a) (h : 1 ≤ p.length) :
    ∃ (c : U) (h2 : J.Adj b c) (q : J.Walk c a), p = SimpleGraph.Walk.cons h2 q := by
  cases p with
  | nil => simp at h
  | @cons _ c _ h2 q => exact ⟨c, h2, q, rfl⟩

theorem walkSum_of_length_one (L : U → U → ℕ) {a b : U} (p : J.Walk a b) (h : p.length = 1) :
    walkSum L p = L a b := by
  obtain ⟨c, h2, q, rfl⟩ := exists_cons_of_pos_length p (by omega)
  have hq : q.length = 0 := by simpa using h
  have hcb : c = b := SimpleGraph.Walk.eq_of_length_eq_zero hq
  subst hcb
  rw [walkSum_cons, walkSum_of_length_zero L q hq]
  omega

theorem walkSum_reverse (L : U → U → ℕ) (hsym : ∀ u v : U, J.Adj u v → L u v = L v u)
    {a b : U} (p : J.Walk a b) : walkSum L p.reverse = walkSum L p := by
  unfold walkSum
  rw [SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro d _
  have hd := hsym d.toProd.1 d.toProd.2 d.adj
  simp only [Function.comp_apply]
  simpa using hd.symm

theorem walkSum_copy (L : U → U → ℕ) {a b a' b' : U} (p : J.Walk a b) (ha : a = a')
    (hb : b = b') : walkSum L (p.copy ha hb) = walkSum L p := by
  subst ha; subst hb; rfl

/-- A closed walk whose vertices — apart from the repeated basepoint — are pairwise distinct is
literally a cycle of `J` in the list encoding used by the cycle-parity equation. -/
theorem cycle_case (L : U → U → ℕ)
    (hcyc : ∀ c : List U, 3 ≤ c.length → c.Nodup →
      (∀ pr ∈ c.zip (c.rotate 1), J.Adj pr.1 pr.2) →
      Even (((c.zip (c.rotate 1)).map (fun pr => L pr.1 pr.2)).sum))
    {a : U} (w : J.Walk a a) (hlen : 3 ≤ w.length) (hnd : w.support.tail.Nodup) :
    Even (walkSum L w) := by
  have hsplit : w.support.dropLast ++ [a] = w.support := by
    have h := List.dropLast_append_getLast (SimpleGraph.Walk.support_ne_nil w)
    rwa [SimpleGraph.Walk.getLast_support] at h
  have hclen : w.support.dropLast.length = w.length := by
    rw [List.length_dropLast, SimpleGraph.Walk.length_support]
    omega
  obtain ⟨x, t, hct⟩ : ∃ x t, w.support.dropLast = x :: t := by
    rcases hcc : w.support.dropLast with _ | ⟨x, t⟩
    · rw [hcc] at hclen; simp at hclen; omega
    · exact ⟨x, t, rfl⟩
  have h1 : x :: (t ++ [a]) = a :: w.support.tail := by
    rw [← SimpleGraph.Walk.support_eq_cons w, ← hsplit, hct]
    rfl
  rw [List.cons.injEq] at h1
  obtain ⟨hxa, hta⟩ := h1
  have hrot : (w.support.dropLast).rotate 1 = w.support.tail := by
    rw [hct, List.rotate_cons_succ, List.rotate_zero, hxa, hta]
  have hzip : (w.support.dropLast).zip ((w.support.dropLast).rotate 1)
      = w.darts.map (fun d => d.toProd) := by
    rw [hrot, ← SimpleGraph.Walk.map_fst_darts, ← SimpleGraph.Walk.map_snd_darts, List.zip_map']
  have hnodup : (w.support.dropLast).Nodup := by
    have hp := List.rotate_perm (w.support.dropLast) 1
    refine (List.Perm.nodup_iff hp).mp ?_
    rw [hrot]; exact hnd
  have hsum : walkSum L w
      = (((w.support.dropLast).zip ((w.support.dropLast).rotate 1)).map
          (fun pr => L pr.1 pr.2)).sum := by
    rw [hzip, List.map_map]
    rfl
  rw [hsum]
  refine hcyc _ (by omega) hnodup ?_
  intro pr hpr
  rw [hzip] at hpr
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hpr
  exact d.adj

/-- A walk with a repeated vertex splits off a nontrivial closed sub-walk. -/
theorem split_of_not_nodup [DecidableEq U] (L : U → U → ℕ) {b a : U} (p : J.Walk b a)
    (hnd : ¬ p.support.Nodup) :
    ∃ (x : U) (p' : J.Walk b a) (C : J.Walk x x),
      p'.length + C.length = p.length ∧ 1 ≤ C.length ∧
      walkSum L p' + walkSum L C = walkSum L p := by
  rw [List.nodup_iff_count_le_one] at hnd
  push_neg at hnd
  obtain ⟨x, hx2⟩ := hnd
  have hxmem : x ∈ p.support := List.count_pos_iff.mp (by omega)
  obtain ⟨p1, p2, hspec, hcount1⟩ :
      ∃ (p1 : J.Walk b x) (p2 : J.Walk x a), p1.append p2 = p ∧
        List.count x p1.support = 1 :=
    ⟨p.takeUntil x hxmem, p.dropUntil x hxmem, SimpleGraph.Walk.take_spec p hxmem,
      SimpleGraph.Walk.count_support_takeUntil_eq_one p hxmem⟩
  have hcnt : List.count x p.support = 1 + List.count x p2.support.tail := by
    rw [← hspec, SimpleGraph.Walk.support_append, List.count_append, hcount1]
  have hx3 : x ∈ p2.support.tail := List.count_pos_iff.mp (by omega)
  have hp2len : 1 ≤ p2.length := by
    have h2 : p2.support.length = p2.length + 1 := SimpleGraph.Walk.length_support p2
    have h4 : 0 < p2.support.tail.length := by
      cases hh : p2.support.tail with
      | nil => rw [hh] at hx3; simp at hx3
      | cons _ _ => simp
    have h3 : p2.support.tail.length = p2.support.length - 1 := by simp
    omega
  obtain ⟨c, h2, q, hq⟩ := exists_cons_of_pos_length p2 hp2len
  have hxq : x ∈ q.support := by
    rw [hq] at hx3; simpa using hx3
  obtain ⟨r1, r2, hrspec⟩ :
      ∃ (r1 : J.Walk c x) (r2 : J.Walk x a), r1.append r2 = q :=
    ⟨q.takeUntil x hxq, q.dropUntil x hxq, SimpleGraph.Walk.take_spec q hxq⟩
  have hlp : p1.length + p2.length = p.length := by
    rw [← hspec, SimpleGraph.Walk.length_append]
  have hlq : r1.length + r2.length = q.length := by
    rw [← hrspec, SimpleGraph.Walk.length_append]
  have hlp2 : p2.length = q.length + 1 := by
    rw [hq, SimpleGraph.Walk.length_cons]
  have hsp : walkSum L p1 + walkSum L p2 = walkSum L p := by
    rw [← hspec, walkSum_append]
  have hsq : walkSum L r1 + walkSum L r2 = walkSum L q := by
    rw [← hrspec, walkSum_append]
  have hsp2 : walkSum L p2 = L x c + walkSum L q := by
    rw [hq, walkSum_cons]
  refine ⟨x, p1.append r2, SimpleGraph.Walk.cons h2 r1, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]; omega
  · rw [SimpleGraph.Walk.length_cons]; omega
  · rw [walkSum_append, walkSum_cons]; omega

/-- **Every closed walk of `J` has even weighted length**, given that every cycle does. -/
theorem closed_even [DecidableEq U] (L : U → U → ℕ)
    (hsym : ∀ u v : U, J.Adj u v → L u v = L v u)
    (hcyc : ∀ c : List U, 3 ≤ c.length → c.Nodup →
      (∀ pr ∈ c.zip (c.rotate 1), J.Adj pr.1 pr.2) →
      Even (((c.zip (c.rotate 1)).map (fun pr => L pr.1 pr.2)).sum)) :
    ∀ (n : ℕ) (a : U) (w : J.Walk a a), w.length ≤ n → Even (walkSum L w) := by
  intro n
  induction n with
  | zero =>
    intro a w hw
    rw [walkSum_of_length_zero L w (by omega)]
    exact ⟨0, rfl⟩
  | succ n ih =>
    intro a w hw
    by_cases hle : w.length ≤ n
    · exact ih a w hle
    push_neg at hle
    have hwn : w.length = n + 1 := by omega
    cases w with
    | nil => rw [walkSum_nil]; exact ⟨0, rfl⟩
    | @cons _ b _ h p =>
      have hplen : p.length = n := by simpa using hwn
      by_cases hnd : p.support.Nodup
      · rcases Nat.lt_or_ge p.length 2 with hs | hs
        · rcases Nat.lt_or_ge p.length 1 with hs0 | hs1
          · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero (p := p) (by omega)) h.ne'
          · have hp1 : p.length = 1 := by omega
            rw [walkSum_cons, walkSum_of_length_one L p hp1, hsym a b h]
            exact ⟨L b a, rfl⟩
        · refine cycle_case L hcyc _ ?_ ?_
          · rw [SimpleGraph.Walk.length_cons]; omega
          · simpa using hnd
      · obtain ⟨x, p', C, hlen', hClen, hsum'⟩ := split_of_not_nodup L p hnd
        have e1 : Even (walkSum L (SimpleGraph.Walk.cons h p')) := by
          refine ih a _ ?_
          rw [SimpleGraph.Walk.length_cons]
          omega
        have e2 : Even (walkSum L C) := by
          refine ih x C ?_
          omega
        rw [walkSum_cons] at e1
        rw [walkSum_cons, ← hsum',
          show L a b + (walkSum L p' + walkSum L C)
            = (L a b + walkSum L p') + walkSum L C from by ring]
        exact e1.add e2

/-- **A parity potential.**  If every cycle of `J` has even `L`-weight then there is
`f : U → ZMod 2` with `f v = f u + L u v` across every edge. -/
theorem exists_potential [DecidableEq U] (L : U → U → ℕ)
    (hsym : ∀ u v : U, J.Adj u v → L u v = L v u)
    (hcyc : ∀ c : List U, 3 ≤ c.length → c.Nodup →
      (∀ pr ∈ c.zip (c.rotate 1), J.Adj pr.1 pr.2) →
      Even (((c.zip (c.rotate 1)).map (fun pr => L pr.1 pr.2)).sum)) :
    ∃ f : U → ZMod 2, ∀ u v : U, J.Adj u v → f v = f u + ((L u v : ℕ) : ZMod 2) := by
  classical
  have hclosed : ∀ (a : U) (w : J.Walk a a), Even (walkSum L w) :=
    fun a w => closed_even L hsym hcyc w.length a w le_rfl
  have key : ∀ (u v : U), J.Adj u v → ∀ (z : U) (wu : J.Walk z u) (wv : J.Walk z v),
      ((walkSum L wv : ℕ) : ZMod 2)
        = ((walkSum L wu : ℕ) : ZMod 2) + ((L u v : ℕ) : ZMod 2) := by
    intro u v h z wu wv
    have hW := hclosed z (wu.append (SimpleGraph.Walk.cons h wv.reverse))
    rw [walkSum_append, walkSum_cons, walkSum_reverse L hsym] at hW
    have h0 : ((walkSum L wu + (L u v + walkSum L wv) : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff_even).mpr hW
    push_cast at h0
    have h2 : ∀ x y z : ZMod 2, x + (y + z) = 0 → z = x + y := by decide
    exact h2 _ _ _ h0
  have hreach : ∀ u : U, J.Reachable ((J.connectedComponentMk u).out) u := by
    intro u
    exact SimpleGraph.ConnectedComponent.eq.mp (Quot.out_eq (J.connectedComponentMk u))
  refine ⟨fun u => ((walkSum L (hreach u).some : ℕ) : ZMod 2), ?_⟩
  intro u v h
  have hr' : (J.connectedComponentMk u).out = (J.connectedComponentMk v).out :=
    congrArg _ (SimpleGraph.ConnectedComponent.sound h.reachable)
  have hh := key u v h ((J.connectedComponentMk u).out) ((hreach u).some)
      (((hreach v).some).copy hr'.symm rfl)
  rw [walkSum_copy] at hh
  exact hh

theorem sum_map_add_one {α : Type*} (l : List α) (g : α → ℕ) :
    (l.map (fun x => g x + 1)).sum = (l.map g).sum + l.length := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

end WalkTools

section Colour

variable {U Wt : Type*}

/-- An entry of a list at a position which is neither the first nor the last is an interior
vertex of the corresponding track. -/
theorem mem_trackInterior_getElem' (q : List Wt) (k : ℕ) (hk : k + 2 < q.length) :
    q[k + 1]'(by omega) ∈ trackInterior q := by
  have hlen : k < q.tail.dropLast.length := by
    simp only [List.length_dropLast, List.length_tail]
    omega
  have hmem := List.getElem_mem hlen
  simp only [List.getElem_dropLast, List.getElem_tail] at hmem
  exact hmem

theorem getElem_congr_index (q : List Wt) (m m' : ℕ) (hm : m < q.length) (hm' : m' < q.length)
    (h : m = m') : q[m]'hm = q[m']'hm' := by
  subst h; rfl

open scoped Classical in
/-- The colouring of the subdivided graph: a vertex sitting at position `i` of the track
`T u v` gets the colour `f u + i`. -/
noncomputable def gcol (J : SimpleGraph U) (T : U → U → List Wt) (f : U → ZMod 2)
    (w : Wt) : ZMod 2 :=
  if h : ∃ p : U × U, J.Adj p.1 p.2 ∧ ∃ i : ℕ, (T p.1 p.2)[i]? = some w then
    f h.choose.1 + ((h.choose_spec.2.choose : ℕ) : ZMod 2)
  else 0

theorem gcol_spec (J : SimpleGraph U) (T : U → U → List Wt) (f : U → ZMod 2)
    (w : Wt) (a b : U) (hab : J.Adj a b) (j : ℕ) (hj : (T a b)[j]? = some w)
    (huniq : ∀ (a' b' : U), J.Adj a' b' → ∀ j' : ℕ, (T a' b')[j']? = some w →
      f a' + ((j' : ℕ) : ZMod 2) = f a + ((j : ℕ) : ZMod 2)) :
    gcol J T f w = f a + ((j : ℕ) : ZMod 2) := by
  have hex : ∃ p : U × U, J.Adj p.1 p.2 ∧ ∃ i : ℕ, (T p.1 p.2)[i]? = some w :=
    ⟨(a, b), hab, j, hj⟩
  unfold gcol
  rw [dif_pos hex]
  exact huniq _ _ hex.choose_spec.1 _ hex.choose_spec.2.choose_spec

end Colour

/-- **A subdivision of `J` whose track lengths satisfy the cycle-parity equation is bipartite.**

`Hs` is presented by the eight conjuncts of `Tracks.IsSubdivision J Hs` for an explicit
injection `ι` and track family `T` (this is how `Thm84GluedSubdivision` delivers it), together
with the length dictionary `trackLength (T u v) = pathLength (R u v) + 1` and the cycle-parity
equation `hcycle`.

Only `hTlen` and `hcycle` carry mathematical content beyond the subdivision structure; the
standing hypotheses of §8 (`hG`, `hJ`, `hSN`, `hR`, `hRsymm`) are carried so that this statement
plugs directly into `Thm84EveryChoiceFormsLineGraph`. -/
theorem glued_isBipartite {U : Type*} [Fintype U] {Wt : Type*} [Finite Wt]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (Hs : SimpleGraph Wt) (ι : U → Wt) (T : U → U → List Wt)
    (hιinj : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom Hs (T u v) (ι u) (ι v))
    (hlen1 : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hcover : ∀ w : Wt, (∃ u : U, w = ι u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v))
    (hedges : Hs.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hTlen : ∀ u v : U, J.Adj u v → trackLength (T u v) = pathLength (R u v) + 1)
    (hcycle : ∀ c : List U, 3 ≤ c.length → c.Nodup →
      (∀ p ∈ c.zip (c.rotate 1), J.Adj p.1 p.2) →
      ((c.zip (c.rotate 1)).map (fun p => pathLength (R p.1 p.2))).sum ≡ c.length [MOD 2]) :
    Hs.IsBipartite := by
  classical
  -- basic facts about the tracks
  have hq2 : ∀ x y : U, J.Adj x y → 2 ≤ (T x y).length := by
    intro x y hxy
    have h := hlen1 x y hxy
    unfold trackLength at h
    omega
  have hnodupT : ∀ x y : U, J.Adj x y → (T x y).Nodup := fun x y hxy => (htrack x y hxy).1.2.1
  have hhead : ∀ x y : U, J.Adj x y → (T x y)[0]? = some (ι x) := by
    intro x y hxy
    have h := (htrack x y hxy).2.1
    rwa [List.head?_eq_getElem?] at h
  have hlast : ∀ x y : U, J.Adj x y → (T x y)[(T x y).length - 1]? = some (ι y) := by
    intro x y hxy
    have h := (htrack x y hxy).2.2
    rwa [List.getLast?_eq_getElem?] at h
  -- the weight function and its symmetry
  have hsym : ∀ x y : U, J.Adj x y → trackLength (T x y) = trackLength (T y x) := by
    intro x y hxy
    rw [hrev x y hxy]
    simp [trackLength]
  -- every cycle of `J` has even total track length
  have hcyc : ∀ c : List U, 3 ≤ c.length → c.Nodup →
      (∀ pr ∈ c.zip (c.rotate 1), J.Adj pr.1 pr.2) →
      Even (((c.zip (c.rotate 1)).map (fun pr => trackLength (T pr.1 pr.2))).sum) := by
    intro c h3 hnd hadj
    have h1 := hcycle c h3 hnd hadj
    have hmap : ((c.zip (c.rotate 1)).map (fun pr => trackLength (T pr.1 pr.2)))
        = (c.zip (c.rotate 1)).map (fun pr => pathLength (R pr.1 pr.2) + 1) :=
      List.map_congr_left (fun pr hpr => hTlen pr.1 pr.2 (hadj pr hpr))
    have hlenzip : (c.zip (c.rotate 1)).length = c.length := by
      simp [List.length_zip]
    rw [hmap, sum_map_add_one, hlenzip, Nat.even_iff]
    unfold Nat.ModEq at h1
    omega
  -- the parity potential on `V(J)`
  obtain ⟨f, hf⟩ := exists_potential (J := J) (fun x y => trackLength (T x y)) hsym hcyc
  have hf' : ∀ x y : U, J.Adj x y →
      f y = f x + ((((T x y).length - 1 : ℕ)) : ZMod 2) := hf
  -- the colour of a vertex of `Hs` does not depend on which track we read it off
  have huniq : ∀ (w : Wt) (a b : U), J.Adj a b → ∀ j : ℕ, (T a b)[j]? = some w →
      ∀ (u v : U), J.Adj u v → ∀ i : ℕ, (T u v)[i]? = some w →
      f a + ((j : ℕ) : ZMod 2) = f u + ((i : ℕ) : ZMod 2) := by
    intro w a b hab j hj u v huv i hi
    obtain ⟨hjlt, hjw⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hilt, hiw⟩ := List.getElem?_eq_some_iff.mp hi
    by_cases hsame : s(u, v) = s(a, b)
    · rw [Sym2.eq_iff] at hsame
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2
        have hij : i = j := by
          have := (hnodupT u v huv).getElem_inj_iff (i := i) (hi := hilt) (j := j) (hj := hjlt)
          exact this.mp (by rw [hiw, hjw])
        rw [hij]
      · subst h1; subst h2
        -- `T a b = T v u = (T u v).reverse`
        have hrv : T v u = (T u v).reverse := hrev u v huv
        have hjlt' : j < (T u v).reverse.length := by
          rw [← hrv]; exact hjlt
        have e1 : (T v u)[j]'hjlt = (T u v).reverse[j]'hjlt' :=
          List.getElem_of_eq hrv hjlt
        have hjn : j < (T u v).length := by
          rw [List.length_reverse] at hjlt'; exact hjlt'
        have e2 : (T u v).reverse[j]'hjlt'
            = (T u v)[(T u v).length - 1 - j]'(by omega) := by
          rw [List.getElem_reverse]
        have hidx : i = (T u v).length - 1 - j := by
          have := (hnodupT u v huv).getElem_inj_iff (i := i) (hi := hilt)
            (j := (T u v).length - 1 - j) (hj := by omega)
          refine this.mp ?_
          rw [hiw, ← e2, ← e1, hjw]
        have hfv := hf' u v huv
        have hcast : (((T u v).length - 1 : ℕ) : ZMod 2)
            = (((T u v).length - 1 - j : ℕ) : ZMod 2) + ((j : ℕ) : ZMod 2) := by
          rw [← Nat.cast_add]
          congr 1
          omega
        rw [hidx, hfv, hcast]
        have halg : ∀ x y z : ZMod 2, x + (y + z) + z = x + y := by decide
        exact halg _ _ _
    · -- different edges of `J`: the common vertex is an end of both tracks
      have hwp : w ∈ T a b := by rw [← hjw]; exact List.getElem_mem hjlt
      have hwq : w ∈ T u v := by rw [← hiw]; exact List.getElem_mem hilt
      have hnq : w ∉ trackInterior (T u v) := fun hc =>
        hdisjint u v a b huv hab hsame w hc hwp
      have hnp : w ∉ trackInterior (T a b) := fun hc =>
        hdisjint a b u v hab huv (Ne.symm hsame) w hc hwq
      have hicase : i = 0 ∨ i = (T u v).length - 1 := by
        by_contra hc
        push_neg at hc
        obtain ⟨hc0, hc1⟩ := hc
        apply hnq
        have hmem := mem_trackInterior_getElem' (T u v) (i - 1) (by omega)
        rw [getElem_congr_index (T u v) (i - 1 + 1) i (by omega) hilt (by omega), hiw] at hmem
        exact hmem
      have hjcase : j = 0 ∨ j = (T a b).length - 1 := by
        by_contra hc
        push_neg at hc
        obtain ⟨hc0, hc1⟩ := hc
        apply hnp
        have hmem := mem_trackInterior_getElem' (T a b) (j - 1) (by omega)
        rw [getElem_congr_index (T a b) (j - 1 + 1) j (by omega) hjlt (by omega), hjw] at hmem
        exact hmem
      have hiw' : (T u v)[i]? = some w := hi
      have hjw' : (T a b)[j]? = some w := hj
      have hfuv := hf' u v huv
      have hfab := hf' a b hab
      rcases hicase with hi0 | hi1 <;> rcases hjcase with hj0 | hj1
      · -- `w = ι u = ι a`
        rw [hi0] at hiw'; rw [hj0] at hjw'
        have h1 : some (ι u) = some w := by rw [← hhead u v huv]; exact hiw'
        have h2 : some (ι a) = some w := by rw [← hhead a b hab]; exact hjw'
        have hua : a = u := hιinj (by
          have e : ι a = w := Option.some_injective _ h2
          have e' : ι u = w := Option.some_injective _ h1
          rw [e, e'])
        rw [hi0, hj0, hua]
      · -- `w = ι u = ι b`
        rw [hi0] at hiw'; rw [hj1] at hjw'
        have h1 : some (ι u) = some w := by rw [← hhead u v huv]; exact hiw'
        have h2 : some (ι b) = some w := by rw [← hlast a b hab]; exact hjw'
        have hub : b = u := hιinj (by
          have e : ι b = w := Option.some_injective _ h2
          have e' : ι u = w := Option.some_injective _ h1
          rw [e, e'])
        rw [hi0, hj1, ← hub, hfab]
        simp
      · -- `w = ι v = ι a`
        rw [hi1] at hiw'; rw [hj0] at hjw'
        have h1 : some (ι v) = some w := by rw [← hlast u v huv]; exact hiw'
        have h2 : some (ι a) = some w := by rw [← hhead a b hab]; exact hjw'
        have hva : a = v := hιinj (by
          have e : ι a = w := Option.some_injective _ h2
          have e' : ι v = w := Option.some_injective _ h1
          rw [e, e'])
        rw [hi1, hj0, hva, hfuv]
        simp
      · -- `w = ι v = ι b`
        rw [hi1] at hiw'; rw [hj1] at hjw'
        have h1 : some (ι v) = some w := by rw [← hlast u v huv]; exact hiw'
        have h2 : some (ι b) = some w := by rw [← hlast a b hab]; exact hjw'
        have hvb : b = v := hιinj (by
          have e : ι b = w := Option.some_injective _ h2
          have e' : ι v = w := Option.some_injective _ h1
          rw [e, e'])
        rw [hi1, hj1, ← hfab, ← hfuv, hvb]
  -- the colour of the `m`-th vertex of a track
  have hg : ∀ (u v : U), J.Adj u v → ∀ (m : ℕ) (hm : m < (T u v).length),
      gcol J T f ((T u v)[m]'hm) = f u + ((m : ℕ) : ZMod 2) := by
    intro u v huv m hm
    refine gcol_spec J T f _ u v huv m (by rw [List.getElem?_eq_getElem hm]) ?_
    intro a' b' hab' j' hj'
    exact huniq _ a' b' hab' j' hj' u v huv m (by rw [List.getElem?_eq_getElem hm])
  -- properness
  have hvalid : ∀ x y : Wt, Hs.Adj x y → gcol J T f x ≠ gcol J T f y := by
    intro x y hxy
    have hmem : s(x, y) ∈ Hs.edgeSet := hxy
    rw [hedges] at hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨u, v, huv, hein⟩ := hmem
    obtain ⟨k, hk, hek⟩ := hein
    have halg : ∀ x y : ZMod 2, x + y ≠ x + (y + 1) := by decide
    rcases (Sym2.eq_iff.mp hek) with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy, hg u v huv k (by omega), hg u v huv (k + 1) hk]
      push_cast
      exact halg _ _
    · rw [hx, hy, hg u v huv (k + 1) hk, hg u v huv k (by omega)]
      push_cast
      exact fun hcon => halg _ _ hcon.symm
  -- assemble the two-colouring
  refine ⟨SimpleGraph.Coloring.mk
    (fun w => (if gcol J T f w = 0 then (0 : Fin 2) else 1)) ?_⟩
  intro x y hxy
  have h := hvalid x y hxy
  have hone : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  by_cases hx0 : gcol J T f x = 0
  · have hy0 : gcol J T f y ≠ 0 := by
      intro hy0
      exact h (hx0.trans hy0.symm)
    simp [hx0, hy0]
  · have hy0 : gcol J T f y = 0 := by
      by_contra hy0
      exact h ((hone _ hx0).trans (hone _ hy0).symm)
    simp [hx0, hy0]

end Workspace.ProofLemmas.Thm84GluedBipartite
