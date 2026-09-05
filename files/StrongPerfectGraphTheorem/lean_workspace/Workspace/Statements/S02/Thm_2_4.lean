/-  Proof attempt 1 for statement 2.4 (`Workspace.Statements.S02.SPGT.thm_2_4`).

    THE PAPER'S PROOF (perfect.pdf printed p. 11, `paper/proofs/2_4.md`), verbatim:

        "Proof.  Let v be linked via paths P1, P2, P3.  For 1 ≤ i ≤ 3, v has a
        neighbour in Pi; let Pi be the path from v to ai with interior in V(Qi).
        At least two of Q1, Q2, Q3 have lengths of the same parity, say Q1, Q2;
        and since G|(V(Q1) ∪ V(Q2)) is not an odd hole, it is a cycle of length 3,
        and the claim follows."

    (The printed sentence transposes the two names: it is `Qᵢ` that is "the path from
    `v` to `aᵢ` with interior in `V(Pᵢ)`".)

    THE PROOF REPRODUCED HERE, step for step.

    * "Let `v` be linked via paths `P₁,P₂,P₃`" — `obtain` the three paths out of
      `VertexCanBeLinkedOntoTriangle`.
    * "`v` has a neighbour in `Pᵢ`; let `Qᵢ` be the path from `v` to `aᵢ` with interior
      in `V(Pᵢ)`" — this is `link_data` below: take the neighbour of `v` on `Pᵢ` that is
      *furthest along* `Pᵢ` towards `aᵢ` (greatest index once `Pᵢ` is oriented to end at
      `aᵢ`), and let `Qᵢ = v :: Rᵢ` where `Rᵢ` is the tail of `Pᵢ` from that neighbour on.
      Maximality is exactly what makes `Qᵢ` induced, i.e. a path in the sense of the
      paper.  Write `ℓᵢ = length(Qᵢ) = |Rᵢ| ≥ 1`.
    * "At least two of `Q₁,Q₂,Q₃` have lengths of the same parity, say `Q₁,Q₂`" — the
      pigeonhole on the three parities (`by_cases` on `ℓ₁ ≡ ℓ₂`, then `ℓ₁ ≡ ℓ₃`, else
      `ℓ₂ ≡ ℓ₃`).  The paper's "say `Q₁,Q₂`" is a symmetry the Lean proof realises by
      running the same argument (`step`) on whichever pair comes up.
    * "`G|(V(Qᵢ) ∪ V(Qⱼ))` … is a cycle" — `V(Qᵢ) ∩ V(Qⱼ) = {v}` (the `Pᵢ` are pairwise
      disjoint and `v ∉ Pᵢ`), and the only edge of `G` between `V(Qᵢ) \ {v} ⊆ V(Pᵢ)` and
      `V(Qⱼ) \ {v} ⊆ V(Pⱼ)` is `aᵢaⱼ`, while `v` has exactly one neighbour on each of
      `Rᵢ, Rⱼ`.  So the concatenation `Qᵢ.reverse ++ Rⱼ`, which runs
      `aᵢ → … → v → … → aⱼ` and closes up along the edge `aⱼaᵢ`, is an *induced* cycle:
      that is `glue_hole` below applied to those two paths.  Its length is
      `ℓᵢ + ℓⱼ + 1`.
    * "is not an odd hole" — `G` is Berge, so a hole (a cycle on ≥ 4 vertices) has even
      length; but `ℓᵢ ≡ ℓⱼ` makes `ℓᵢ + ℓⱼ + 1` odd.  Hence the cycle has fewer than 4
      vertices.
    * "it is a cycle of length 3, and the claim follows" — `ℓᵢ + ℓⱼ + 1 ≤ 3` with
      `ℓᵢ, ℓⱼ ≥ 1` forces `ℓᵢ = ℓⱼ = 1`, i.e. `Qᵢ = [v, aᵢ]` and `Qⱼ = [v, aⱼ]`, i.e.
      `v` is adjacent to `aᵢ` and to `aⱼ` — two of `a₁,a₂,a₃`, as claimed.

    One case the paper leaves implicit is `v ∈ V(Pᵢ)` for some `i` (the definition of
    "can be linked" does not exclude it).  Then the uniqueness clause forces `v = aᵢ`,
    and `v` is adjacent to the other two `a`'s directly; this is handled first.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics

-- The frozen statement's `variable` line carries `[Fintype V] [DecidableEq V]`, which this
-- proof does not use.  The linter's suggested `omit ... in` would change the elaborated
-- signature (and be rejected by `rollback_check`), so the linter is switched off instead.
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

namespace SPGT

/-! ### Encoding infrastructure

None of the four lemmas in this section has a counterpart in the paper; they are
bookkeeping for the list encoding of paths and holes, and belong in
`Workspace/ProofLemmas/` once lifted. -/

section Helpers

variable {V : Type*}

private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- Greatest element of a nonempty set of naturals bounded by `n`. -/
private theorem exists_greatest {Q : ℕ → Prop} : ∀ (n : ℕ), (∃ k, k < n ∧ Q k) →
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

/-- Two vertex-disjoint paths whose only two connecting edges join the last vertex of
the first to the first vertex of the second, and the first vertex of the first to the
last vertex of the second, concatenate to a hole. -/
private theorem glue_hole {G : SimpleGraph V} {P R : List V} {u₀ u₁ w₀ w₁ : V}
    (hP : IsPathFrom G P u₀ u₁) (hR : IsPathFrom G R w₀ w₁)
    (hdisj : ∀ x ∈ P, x ∉ R)
    (hcross : ∀ x ∈ P, ∀ y ∈ R, (G.Adj x y ↔ (x = u₁ ∧ y = w₀) ∨ (x = u₀ ∧ y = w₁)))
    (hlen : 4 ≤ P.length + R.length) :
    IsHoleList G (P ++ R) := by
  obtain ⟨hPl, hPh, hPt⟩ := hP
  obtain ⟨hRl, hRh, hRt⟩ := hR
  have hm : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hPl
  have hn : 0 < R.length := Workspace.ProofLemmas.PathBasics.path_length_pos hRl
  have hP0 : P[0]'hm = u₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hPh hm
  have hPm : P[P.length - 1]'(by omega) = u₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hPt hm
  have hR0 : R[0]'hn = w₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hRh hn
  have hRn : R[R.length - 1]'(by omega) = w₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hRt hn
  have hPnd : P.Nodup := hPl.2.1
  have hRnd : R.Nodup := hRl.2.1
  have cross : ∀ (i j : ℕ) (hiP : i < P.length) (hjP : P.length ≤ j)
      (hi : i < (P ++ R).length) (hj : j < (P ++ R).length),
      (G.Adj ((P ++ R)[i]'hi) ((P ++ R)[j]'hj) ↔
        (j = (i + 1) % (P ++ R).length ∨ i = (j + 1) % (P ++ R).length)) := by
    intro i j hiP hjP hi hj
    have hiL : i < P.length + R.length := by simpa using hi
    have hjL : j < P.length + R.length := by simpa using hj
    have hjR : j - P.length < R.length := by omega
    rw [List.getElem_append_left hiP, List.getElem_append_right hjP,
      hcross (P[i]'hiP) (List.getElem_mem hiP) (R[j - P.length]'hjR) (List.getElem_mem hjR)]
    have e1 : (P[i]'hiP = u₁) ↔ i = P.length - 1 := by
      rw [← hPm]; exact hPnd.getElem_inj_iff
    have e2 : (P[i]'hiP = u₀) ↔ i = 0 := by
      rw [← hP0]; exact hPnd.getElem_inj_iff
    have e3 : (R[j - P.length]'hjR = w₀) ↔ j - P.length = 0 := by
      rw [← hR0]; exact hRnd.getElem_inj_iff
    have e4 : (R[j - P.length]'hjR = w₁) ↔ j - P.length = R.length - 1 := by
      rw [← hRn]; exact hRnd.getElem_inj_iff
    rw [e1, e2, e3, e4]
    simp only [List.length_append]
    rw [succ_mod_eq hiL, succ_mod_eq hjL]
    split_ifs <;> omega
  refine ⟨by simpa using hlen, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hPnd, hRnd, fun a ha b hb => by rintro rfl; exact hdisj a ha hb⟩
  · intro i j hi hj
    have hiL : i < P.length + R.length := by simpa using hi
    have hjL : j < P.length + R.length := by simpa using hj
    rcases lt_or_ge i P.length with hiP | hiP
    · rcases lt_or_ge j P.length with hjP | hjP
      · rw [List.getElem_append_left hiP, List.getElem_append_left hjP,
          Workspace.ProofLemmas.PathBasics.path_adj_iff hPl hiP hjP]
        simp only [List.length_append]
        rw [succ_mod_eq hiL, succ_mod_eq hjL]
        split_ifs <;> omega
      · exact cross i j hiP hjP hi hj
    · rcases lt_or_ge j P.length with hjP | hjP
      · rw [SimpleGraph.adj_comm, cross j i hjP hiP hj hi]
        constructor <;> (intro h; tauto)
      · have hiR : i - P.length < R.length := by omega
        have hjR : j - P.length < R.length := by omega
        rw [List.getElem_append_right hiP, List.getElem_append_right hjP,
          Workspace.ProofLemmas.PathBasics.path_adj_iff hRl hiR hjR]
        simp only [List.length_append]
        rw [succ_mod_eq hiL, succ_mod_eq hjL]
        split_ifs <;> omega

/-- Prefixing a path `r` by a vertex `v` whose only neighbour on `r` is its first
vertex again gives a path. -/
private theorem isPathList_cons {G : SimpleGraph V} {r : List V} {v x : V}
    (hr : IsPathList G r) (hhead : r.head? = some x) (hv : v ∉ r)
    (hadj : ∀ y ∈ r, (G.Adj v y ↔ y = x)) :
    IsPathList G (v :: r) := by
  have hrlen : 0 < r.length := Workspace.ProofLemmas.PathBasics.path_length_pos hr
  have hr0 : r[0]'hrlen = x :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hhead hrlen
  refine ⟨by simp, List.nodup_cons.mpr ⟨hv, hr.2.1⟩, ?_⟩
  intro i j hi hj
  rcases i with _ | s <;> rcases j with _ | t
  · simp
  · have ht : t < r.length := by simpa using hj
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [hadj (r[t]'ht) (List.getElem_mem ht), ← hr0, hr.2.1.getElem_inj_iff]
    omega
  · have hs : s < r.length := by simpa using hi
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [SimpleGraph.adj_comm, hadj (r[s]'hs) (List.getElem_mem hs), ← hr0,
      hr.2.1.getElem_inj_iff]
    omega
  · have hs : s < r.length := by simpa using hi
    have ht : t < r.length := by simpa using hj
    simp only [List.getElem_cons_succ]
    rw [Workspace.ProofLemmas.PathBasics.path_adj_iff hr hs ht]
    omega

/-- The paper's *"`v` has a neighbour in `Pᵢ`; let `Qᵢ` be the path from `v` to `aᵢ`
with interior in `V(Pᵢ)`"*, for a path `p` listed so that it ends at `a`.  `r` is the
tail of `p` beginning at the neighbour of `v` on `p` closest to `a`; `v :: r` is `Q`. -/
private theorem link_core {G : SimpleGraph V} {p : List V} {a v : V}
    (hp : IsPathList G p) (hlast : p.getLast? = some a) (hv : v ∉ p)
    (hex : ∃ x ∈ p, G.Adj v x) :
    ∃ (r : List V) (x : V), IsPathFrom G r x a ∧ IsPathFrom G (v :: r) v a ∧
      1 ≤ r.length ∧ (∀ y ∈ r, y ∈ p) ∧ (∀ y ∈ r, (G.Adj v y ↔ y = x)) := by
  obtain ⟨k, hk, hkadj, hkmax⟩ :
      ∃ k, ∃ hk : k < p.length, G.Adj v (p[k]'hk) ∧
        ∀ m, ∀ hm : m < p.length, G.Adj v (p[m]'hm) → m ≤ k := by
    have hQ : ∃ k, k < p.length ∧ (∃ h : k < p.length, G.Adj v (p[k]'h)) := by
      obtain ⟨x, hxp, hadjx⟩ := hex
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hxp
      exact ⟨j, hj, hj, hadjx⟩
    obtain ⟨k, hk, ⟨hk', hadj⟩, hmax⟩ := exists_greatest p.length hQ
    exact ⟨k, hk, hadj, fun m hm hadjm => hmax m hm ⟨hm, hadjm⟩⟩
  have hdlen : (p.drop k).length = p.length - k := List.length_drop
  have hd1 : 1 ≤ (p.drop k).length := by omega
  have hdpath : IsPathList G (p.drop k) :=
    Workspace.ProofLemmas.PathBasics.isPathList_drop hp hk
  have hdsub : ∀ y ∈ p.drop k, y ∈ p := fun _ hy => List.mem_of_mem_drop hy
  have hdhead : (p.drop k).head? = some (p[k]'hk) := by
    rw [List.head?_drop, List.getElem?_eq_getElem hk]
  have hdlast : (p.drop k).getLast? = some a := by
    rw [List.getLast?_drop, if_neg (by omega)]
    exact hlast
  have hvd : v ∉ p.drop k := fun hc => hv (hdsub v hc)
  have hdnbr : ∀ y ∈ p.drop k, (G.Adj v y ↔ y = p[k]'hk) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hy
    have htp : k + t < p.length := by omega
    have hval : (p.drop k)[t]'ht = p[k + t]'htp := List.getElem_drop
    rw [hval]
    constructor
    · intro hadj
      have hle := hkmax (k + t) htp hadj
      have ht0 : t = 0 := by omega
      subst ht0
      simp
    · intro heq
      have hkt : k + t = k := (hp.2.1.getElem_inj_iff).mp heq
      have ht0 : t = 0 := by omega
      subst ht0
      simpa using hkadj
  refine ⟨p.drop k, p[k]'hk, ⟨hdpath, hdhead, hdlast⟩, ⟨?_, by simp, ?_⟩, hd1, hdsub, hdnbr⟩
  · exact isPathList_cons hdpath hdhead hvd hdnbr
  · rw [List.getLast?_cons_of_ne_nil (by intro hc; rw [hc] at hd1; simp at hd1)]
    exact hdlast

/-- `link_core` with the orientation of `p` left free: `a` is an *end* of `p`. -/
private theorem link_data {G : SimpleGraph V} {p : List V} {a v : V}
    (hp : IsPathList G p) (hend : p.head? = some a ∨ p.getLast? = some a) (hv : v ∉ p)
    (hex : ∃ x ∈ p, G.Adj v x) :
    ∃ (r : List V) (x : V), IsPathFrom G r x a ∧ IsPathFrom G (v :: r) v a ∧
      1 ≤ r.length ∧ (∀ y ∈ r, y ∈ p) ∧ (∀ y ∈ r, (G.Adj v y ↔ y = x)) := by
  rcases hend with h | h
  · have hp' : IsPathList G p.reverse :=
      Workspace.ProofLemmas.PathBasics.isPathList_reverse hp
    have h' : p.reverse.getLast? = some a := by rw [List.getLast?_reverse]; exact h
    have hv' : v ∉ p.reverse := by rwa [List.mem_reverse]
    have hex' : ∃ x ∈ p.reverse, G.Adj v x := by
      obtain ⟨x, hx, hadjx⟩ := hex
      exact ⟨x, List.mem_reverse.mpr hx, hadjx⟩
    obtain ⟨r, x, h1, h2, h3, h4, h5⟩ := link_core hp' h' hv' hex'
    exact ⟨r, x, h1, h2, h3, fun y hy => List.mem_reverse.mp (h4 y hy), h5⟩
  · exact link_core hp h hv hex

end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.4** (printed p. 9)

PAPER: *"Let `G` be Berge, and suppose `v` can be linked onto a triangle
`{a₁,a₂,a₃}`.  Then `v` is adjacent to at least two of `a₁,a₂,a₃`."*

That `{a₁,a₂,a₃}` really is a triangle is not repeated as a hypothesis: it is
forced by `VertexCanBeLinkedOntoTriangle` (the three `aᵢ` lie on pairwise
vertex-disjoint paths and `aᵢaⱼ` is an edge between `V(Pᵢ)` and `V(Pⱼ)`).
"Adjacent to at least two of `a₁,a₂,a₃`" is the disjunction over the three
pairs. -/
theorem thm_2_4 (G : SimpleGraph V) (hG : Berge G) (v a₁ a₂ a₃ : V)
    (hlink : VertexCanBeLinkedOntoTriangle G v a₁ a₂ a₃) :
    (G.Adj v a₁ ∧ G.Adj v a₂) ∨ (G.Adj v a₁ ∧ G.Adj v a₃) ∨ (G.Adj v a₂ ∧ G.Adj v a₃) := by
  -- "Let `v` be linked via paths `P₁, P₂, P₃`."
  obtain ⟨p₁, p₂, p₃, ⟨hp₁, hp₂, hp₃⟩, ⟨hd12, hd13, hd23⟩, ⟨he₁, he₂, he₃⟩,
    ⟨hc12, hc13, hc23⟩, ⟨hn₁, hn₂, hn₃⟩⟩ := hlink
  have hmem : ∀ (p : List V) (a : V), (p.head? = some a ∨ p.getLast? = some a) → a ∈ p := by
    rintro p a (h | h)
    · exact Workspace.ProofLemmas.PathBasics.head_mem h
    · exact Workspace.ProofLemmas.PathBasics.getLast_mem h
  have ha₁ : a₁ ∈ p₁ := hmem p₁ a₁ he₁
  have ha₂ : a₂ ∈ p₂ := hmem p₂ a₂ he₂
  have ha₃ : a₃ ∈ p₃ := hmem p₃ a₃ he₃
  -- Degenerate case, left implicit by the paper: `v` lies on one of the three paths.
  -- The uniqueness clause then forces `v = aᵢ`, and `v` is adjacent to the other two.
  by_cases hv₁ : v ∈ p₁
  · obtain ⟨y, hy, hadjy⟩ := hn₂
    obtain ⟨z, hz, hadjz⟩ := hn₃
    have h1 := (hc12 v hv₁ y hy).mp hadjy
    have h2 := (hc13 v hv₁ z hz).mp hadjz
    exact Or.inr (Or.inr ⟨h1.2 ▸ hadjy, h2.2 ▸ hadjz⟩)
  by_cases hv₂ : v ∈ p₂
  · obtain ⟨y, hy, hadjy⟩ := hn₁
    obtain ⟨z, hz, hadjz⟩ := hn₃
    have h1 := (hc12 y hy v hv₂).mp hadjy.symm
    have h2 := (hc23 v hv₂ z hz).mp hadjz
    exact Or.inr (Or.inl ⟨h1.1 ▸ hadjy, h2.2 ▸ hadjz⟩)
  by_cases hv₃ : v ∈ p₃
  · obtain ⟨y, hy, hadjy⟩ := hn₁
    obtain ⟨z, hz, hadjz⟩ := hn₂
    have h1 := (hc13 y hy v hv₃).mp hadjy.symm
    have h2 := (hc23 z hz v hv₃).mp hadjz.symm
    exact Or.inl ⟨h1.1 ▸ hadjy, h2.1 ▸ hadjz⟩
  -- "For `1 ≤ i ≤ 3`, `v` has a neighbour in `Pᵢ`; let `Qᵢ = v :: Rᵢ` be the path from
  -- `v` to `aᵢ` with interior in `V(Pᵢ)`."
  obtain ⟨r₁, x₁, hr₁, hq₁, hl₁, hs₁, hb₁⟩ := link_data hp₁ he₁ hv₁ hn₁
  obtain ⟨r₂, x₂, hr₂, hq₂, hl₂, hs₂, hb₂⟩ := link_data hp₂ he₂ hv₂ hn₂
  obtain ⟨r₃, x₃, hr₃, hq₃, hl₃, hs₃, hb₃⟩ := link_data hp₃ he₃ hv₃ hn₃
  -- "since `G|(V(Qᵢ) ∪ V(Qⱼ))` is not an odd hole, it is a cycle of length 3, and the
  -- claim follows" — for whichever pair `i, j` of equal parity the pigeonhole supplies.
  have step : ∀ (pi pj ri rj : List V) (ai aj xj : V),
      v ∉ pi → v ∉ pj → ai ∈ pi →
      (∀ z ∈ pi, z ∉ pj) →
      (∀ x ∈ pi, ∀ y ∈ pj, (G.Adj x y ↔ (x = ai ∧ y = aj))) →
      (∀ y ∈ ri, y ∈ pi) → (∀ y ∈ rj, y ∈ pj) →
      IsPathFrom G (v :: ri) v ai → IsPathFrom G rj xj aj →
      1 ≤ ri.length → 1 ≤ rj.length →
      (∀ y ∈ rj, (G.Adj v y ↔ y = xj)) →
      ri.length % 2 = rj.length % 2 →
      G.Adj v ai ∧ G.Adj v aj := by
    intro pi pj ri rj ai aj xj hvi hvj hai hdij hcij hsi hsj hqi hrj h1i h1j hbj hpar
    have hvne : v ≠ ai := by rintro rfl; exact hvi hai
    by_cases hbig : 4 ≤ (v :: ri).reverse.length + rj.length
    · -- the cycle is a hole, and it is odd: contradiction with `G` Berge
      exfalso
      have hhole : IsHoleList G ((v :: ri).reverse ++ rj) := by
        refine glue_hole (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hqi) hrj
          ?_ ?_ hbig
        · intro z hz hz'
          rw [List.mem_reverse] at hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hvj (hsj _ hz')
          · exact hdij _ (hsi _ hz) (hsj _ hz')
        · intro z hz y hy
          rw [List.mem_reverse] at hz
          rcases List.mem_cons.mp hz with rfl | hz
          · rw [hbj y hy]
            constructor
            · intro h; exact Or.inl ⟨rfl, h⟩
            · rintro (⟨-, h⟩ | ⟨h, -⟩)
              · exact h
              · exact absurd h hvne
          · have hzri : z ∈ ri := hz
            have hzne : z ≠ v := by rintro rfl; exact hvi (hsi _ hzri)
            rw [hcij z (hsi _ hzri) y (hsj _ hy)]
            constructor
            · intro h; exact Or.inr h
            · rintro (⟨h, -⟩ | h)
              · exact absurd h hzne
              · exact h
      have hev : Even (((v :: ri).reverse ++ rj).length) := hG.1 _ hhole
      simp only [List.length_append, List.length_reverse, List.length_cons] at hev
      rw [Nat.even_iff] at hev
      omega
    · -- "it is a cycle of length 3": both `Qᵢ` and `Qⱼ` have length 1
      simp only [List.length_reverse, List.length_cons] at hbig
      have hri1 : ri.length = 1 := by omega
      have hrj1 : rj.length = 1 := by omega
      constructor
      · refine Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hqi ?_
        simp [Workspace.ProofLemmas.PathBasics.pathLength_cons, hri1]
      · have haj : aj ∈ rj := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hrj).2
        have hxj : xj = aj := by
          obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hrj1
          rw [hc] at hrj
          have e1 : c = xj := by simpa using hrj.2.1
          have e2 : c = aj := by simpa using hrj.2.2
          exact e1.symm.trans e2
        exact (hbj aj haj).mpr hxj.symm
  -- "At least two of `Q₁, Q₂, Q₃` have lengths of the same parity."
  by_cases h12 : r₁.length % 2 = r₂.length % 2
  · exact Or.inl (step p₁ p₂ r₁ r₂ a₁ a₂ x₂ hv₁ hv₂ ha₁ hd12 hc12 hs₁ hs₂ hq₁ hr₂
      hl₁ hl₂ hb₂ h12)
  by_cases h13 : r₁.length % 2 = r₃.length % 2
  · exact Or.inr (Or.inl (step p₁ p₃ r₁ r₃ a₁ a₃ x₃ hv₁ hv₃ ha₁ hd13 hc13 hs₁ hs₃ hq₁ hr₃
      hl₁ hl₃ hb₃ h13))
  · have h23 : r₂.length % 2 = r₃.length % 2 := by omega
    exact Or.inr (Or.inr (step p₂ p₃ r₂ r₃ a₂ a₃ x₃ hv₂ hv₃ ha₂ hd23 hc23 hs₂ hs₃ hq₂ hr₃
      hl₂ hl₃ hb₃ h23))


end SPGT

end Workspace.Statements.S02
