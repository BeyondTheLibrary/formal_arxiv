import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleBasics

/-!
# A balanced pair admits no leap for an even hole

If `(V(C), B)` is a balanced pair, no vertex of the hole `C` lies in `B`, and `C` has even
length, then no two vertices `a, b ∈ B` form a leap for `C`.

The argument is the one the paper uses whenever it discards the *leap* alternative of the
Roussel–Rubio lemma 2.1 for a hole:

* a leap for `C` at the edge `uv` is a leap for the path `C \ uv` in `G \ uv`; write
  `p` for that path (a rotation of `c`, running from `v` round to `u`) and `n = |c|`;
* since `a, b ∈ B` and no vertex of `C` is in `B`, neither `a` nor `b` lies on `C`, while
  `u, v` do — so the deleted edge `uv` is never incident with `a` or `b`, and every one of
  the leap's adjacency statements may be read in `G` itself.  For the same reason
  `¬ (G \ uv).Adj a b` upgrades to `¬ G.Adj a b`;
* the *middle* `M` of `p` — `p` with its first and last vertex removed — is a cyclically
  contiguous block of `C` with `n - 2 ≤ n - 1` vertices, hence an induced path of `G`,
  running from `p₂` to `p_{n-1}`;
* the leap says `a` sees exactly `p₁, p₂, pₙ` and `b` sees exactly `p₁, p_{n-1}, pₙ`, so on
  `M` the vertex `a` sees only `p₂` and the vertex `b` only `p_{n-1}`.  Therefore
  `a-M-b` is an induced path of `G` from `a` to `b`, of length `(n - 2) + 1 = n - 1`, with
  interior inside `V(C)`;
* `n` is even, so `n - 1` is odd, and `a, b` are non-adjacent vertices of `B`: that is
  exactly the configuration the first clause of `Balanced G V(C) B` forbids.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.BalancedNoLeap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*}

/-- The hole `q` with its first and its last vertex removed is an induced path of `G`:
it is a cyclically contiguous block of `q` on `|q| - 2 ≤ |q| - 1` vertices. -/
private theorem isPathList_hole_interior {G : SimpleGraph V} {q : List V}
    (hq : IsHoleList G q) :
    IsPathList G ((q.drop 1).take (q.length - 2)) := by
  have hn : 4 ≤ q.length := hq.1
  have hMlen : ((q.drop 1).take (q.length - 2)).length = q.length - 2 := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro hnil
    rw [hnil] at hMlen
    simp only [List.length_nil] at hMlen
    omega
  · exact List.Nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _)) hq.2.1
  · intro s t hs ht
    have hs2 : s < q.length - 2 := by omega
    have ht2 : t < q.length - 2 := by omega
    have es : ((q.drop 1).take (q.length - 2))[s]'hs = q[1 + s]'(by omega) := by
      simp only [List.getElem_take, List.getElem_drop]
    have et : ((q.drop 1).take (q.length - 2))[t]'ht = q[1 + t]'(by omega) := by
      simp only [List.getElem_take, List.getElem_drop]
    have hadj := hq.2.2 (1 + s) (1 + t) (by omega) (by omega)
    rw [es, et, hadj]
    have m1 : (1 + s + 1) % q.length = 1 + s + 1 := Nat.mod_eq_of_lt (by omega)
    have m2 : (1 + t + 1) % q.length = 1 + t + 1 := Nat.mod_eq_of_lt (by omega)
    rw [m1, m2]
    omega

/-- The heart of the argument, stated for the *path* `p = C \ uv` directly. -/
private theorem key {G : SimpleGraph V} {p : List V} {B : Set V} {u v a b : V}
    (hp : IsHoleList G p) (heven : Even p.length)
    (hpB : ∀ w ∈ p, w ∉ B)
    (hbal : SPGT.Balanced G {w : V | w ∈ p} B)
    (ha : a ∈ B) (hb : b ∈ B) (hu : u ∈ p) (hv : v ∈ p)
    (hleap : IsLeapForPath (G.deleteEdges {s(u, v)}) p a b) : False := by
  obtain ⟨-, -, hab_ne, hab_nadj', hAd, hBd⟩ := hleap
  have hn : 4 ≤ p.length := hp.1
  -- `a` and `b` are not vertices of the hole.
  have hanot : a ∉ p := fun h => hpB a h ha
  have hbnot : b ∉ p := fun h => hpB b h hb
  -- Step 1.  A vertex off the hole is never an end of the deleted edge, so its adjacencies
  -- to the hole are the same in `G` and in `G \ uv`.
  have htrans : ∀ x ∈ p, ∀ w : V, w ∉ p →
      ((G.deleteEdges {s(u, v)}).Adj w x ↔ G.Adj w x) := by
    intro x hx w hw
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    rcases Sym2.eq_iff.mp hmem with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hw (by rw [h1]; exact hu)
    · exact hw (by rw [h1]; exact hv)
  have hab_nadj : ¬ G.Adj a b := by
    intro h
    refine hab_nadj' ?_
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨h, ?_⟩
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    rcases Sym2.eq_iff.mp hmem with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hanot (by rw [h1]; exact hu)
    · exact hanot (by rw [h1]; exact hv)
  have hAg : ∀ (k : ℕ) (hk : k < p.length),
      (G.Adj a (p[k]'hk) ↔ (k = 0 ∨ k = 1 ∨ k = p.length - 1)) := by
    intro k hk
    rw [← htrans (p[k]'hk) (List.getElem_mem hk) a hanot]
    exact hAd k hk
  have hBg : ∀ (k : ℕ) (hk : k < p.length),
      (G.Adj b (p[k]'hk) ↔ (k = 0 ∨ k = p.length - 2 ∨ k = p.length - 1)) := by
    intro k hk
    rw [← htrans (p[k]'hk) (List.getElem_mem hk) b hbnot]
    exact hBd k hk
  -- Step 2.  The middle `M` of `p`, an induced path of `G` from `p₂` to `p_{n-1}`.
  have hMlen : ((p.drop 1).take (p.length - 2)).length = p.length - 2 := by
    simp only [List.length_take, List.length_drop]
    omega
  have hidx : p.length - 2 - 1 + 1 = p.length - 2 := by omega
  have hMpath : IsPathList G ((p.drop 1).take (p.length - 2)) := isPathList_hole_interior hp
  have hMhead : ((p.drop 1).take (p.length - 2)).head? = some (p[1]'(by omega)) := by
    have h := PathBasics.head?_slice p (i := 1) (j := p.length - 2) (by omega) (by omega)
    rw [hidx] at h
    exact h
  have hMlast : ((p.drop 1).take (p.length - 2)).getLast? =
      some (p[p.length - 2]'(by omega)) := by
    have h := PathBasics.getLast?_slice p (i := 1) (j := p.length - 2) (by omega) (by omega)
    rw [hidx] at h
    exact h
  have hMmem : ∀ x : V, x ∈ (p.drop 1).take (p.length - 2) ↔
      ∃ (k : ℕ) (hk : k < p.length), 1 ≤ k ∧ k ≤ p.length - 2 ∧ p[k]'hk = x := by
    intro x
    have h := PathBasics.mem_slice_iff p (i := 1) (j := p.length - 2) (x := x)
      (by omega) (by omega)
    rw [hidx] at h
    exact h
  have hsubp : ∀ x : V, x ∈ (p.drop 1).take (p.length - 2) → x ∈ p := by
    intro x hx
    obtain ⟨k, hk, -, -, rfl⟩ := (hMmem x).mp hx
    exact List.getElem_mem hk
  have hMpathFrom : IsPathFrom G ((p.drop 1).take (p.length - 2))
      (p[1]'(by omega)) (p[p.length - 2]'(by omega)) := ⟨hMpath, hMhead, hMlast⟩
  -- The two attaching edges, and the two "no other neighbour" clauses.
  have hadja : G.Adj a (p[1]'(by omega)) := (hAg 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hadjb : G.Adj b (p[p.length - 2]'(by omega)) :=
    (hBg (p.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
  have haM : a ∉ (p.drop 1).take (p.length - 2) := fun h => hanot (hsubp a h)
  have hbM : b ∉ (p.drop 1).take (p.length - 2) := fun h => hbnot (hsubp b h)
  have hsother : ∀ x ∈ (p.drop 1).take (p.length - 2), x ≠ (p[1]'(by omega)) →
      ¬ G.Adj a x := by
    intro x hx hxne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hMmem x).mp hx
    have hcases := (hAg k hk).mp hadj
    have hkeq : k = 1 := by omega
    exact hxne (hp.2.1.getElem_inj_iff.mpr hkeq)
  have htother : ∀ x ∈ (p.drop 1).take (p.length - 2),
      x ≠ (p[p.length - 2]'(by omega)) → ¬ G.Adj b x := by
    intro x hx hxne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hMmem x).mp hx
    have hcases := (hBg k hk).mp hadj
    have hkeq : k = p.length - 2 := by omega
    exact hxne (hp.2.1.getElem_inj_iff.mpr hkeq)
  -- Step 3.  `a-M-b` is an odd path between nonadjacent vertices of `B` with interior in `V(C)`.
  have hPth : IsPathFrom G (a :: (((p.drop 1).take (p.length - 2)) ++ [b])) a b :=
    PathAttach.isPathFrom_cons_concat hMpathFrom hadja hadjb hab_nadj hab_ne haM hbM
      hsother htother
  have hPlen : pathLength (a :: (((p.drop 1).take (p.length - 2)) ++ [b])) = p.length - 1 := by
    rw [PathAttach.pathLength_cons_append_singleton, hMlen]
    omega
  have hint : ∀ x ∈ SPGT.interior (a :: (((p.drop 1).take (p.length - 2)) ++ [b])),
      x ∈ {w : V | w ∈ p} := by
    intro x hx
    rw [PathBasics.mem_interior_iff_of_pathFrom hPth] at hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rcases PathAttach.mem_cons_append_singleton.mp hx1 with h | h | h
    · exact absurd h hx2
    · exact hsubp x h
    · exact absurd h hx3
  have hodd : Odd (pathLength (a :: (((p.drop 1).take (p.length - 2)) ++ [b]))) := by
    rw [hPlen, Nat.odd_iff]
    obtain ⟨m, hm⟩ := heven
    omega
  exact hbal.1 a b _ ha hb hab_nadj hPth hint hodd

/-- **A balanced pair admits no leap for an even hole.**

If `(V(C), B)` is balanced, `C` is a hole of even length none of whose vertices lies in `B`,
and `a, b ∈ B`, then `a, b` is not a leap for `C` at any edge `uv` of `C`. -/
theorem not_leap_of_balanced {G : SimpleGraph V}
    {c : List V} (hc : IsHoleList G c) (heven : Even c.length)
    {B : Set V} (hcB : ∀ w ∈ c, w ∉ B)
    (hbal : SPGT.Balanced G {w : V | w ∈ c} B)
    {u v a b : V} (ha : a ∈ B) (hb : b ∈ B)
    (hleap : IsLeapForHole G c u v a b) : False := by
  obtain ⟨-, i, hhead, hlast, hlp⟩ := hleap
  refine key (p := c.rotate i) (u := u) (v := v) (HoleBasics.isHoleList_rotate hc i)
    (by simpa using heven) (fun w hw => hcB w (List.mem_rotate.mp hw)) ?_ ha hb
    (PathBasics.getLast_mem hlast) (PathBasics.head_mem hhead) hlp
  rw [HoleBasics.setOf_mem_rotate]
  exact hbal

end Workspace.ProofLemmas.BalancedNoLeap
