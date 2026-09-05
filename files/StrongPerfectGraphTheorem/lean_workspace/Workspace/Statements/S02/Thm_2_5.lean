/-  Proof attempt for statement 2.5 of Chudnovsky–Robertson–Seymour–Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 10).

    PRINTED PROOF (verbatim, `paper/proofs/2_5.md`):

      "By 2.2, v has a neighbour in P*, and we may assume that p_{n-1} is not its only such
       neighbour, so v has a neighbour in {p₂,…,p_{n-2}}.  If P has length ≤ 3 then the
       result follows, so we may assume its length is at least 5.  By 2.1, there is a leap
       a, b for P in X; so there is a path a-p₂-⋯-p_{n-1}-b.  Now {p₁, p₂, a} is a triangle,
       and v can be linked onto it via the three paths b-p₁, P \ {p₁, p_{n-1}, p_n}, a; and
       so v has two neighbours in the triangle, by 2.4, and the claim follows."

    MAP ONTO THE LEAN PROOF, step for step.

    * "By 2.2, v has a neighbour in P*"        — `thm_2_2 … v hv`.
    * "we may assume that p_{n-1} is not its only such neighbour" — the `by_cases hset` on the
      conclusion's second disjunct; if the neighbour set is not `{p_{n-1}}` then, since 2.2
      makes it nonempty, some neighbour `w ∈ P*` differs from `p_{n-1}`.  Indexing `P*` gives
      `w = p[k]` with `1 ≤ k ≤ n-3`, i.e. `w ∈ {p₂,…,p_{n-2}}`.
    * "If P has length ≤ 3 then the result follows" — length 1 is impossible (`P*` would be
      empty) and for length 3 the range `1 ≤ k ≤ n-3 = 1` forces `w = p₂`, the first disjunct.
    * "By 2.1, there is a leap a, b for P in X"  — `thm_2_1`; its first outcome is `hnoedge`,
      its third is excluded by length `≥ 5`.
    * "Now {p₁, p₂, a} is a triangle, and v can be linked onto it via the three paths
      b-p₁, P \ {p₁, p_{n-1}, p_n}, a"  — `P₁ = [b, p₁]`, `P₂ = p₂-⋯-p_{n-2}` (the slice of
      `p` on indices `1 … n-3`), `P₃ = [a]`.  The leap's two adjacency equivalences supply
      every clause of `VertexLinkedOntoTriangle`; `v` has a neighbour on each path because
      `a, b ∈ X` and `v` is `X`-complete, and because of `w` above.
    * "so v has two neighbours in the triangle, by 2.4, and the claim follows" — `thm_2_4`
      returns two of `p₁, p₂, a`, and in each of the three cases one of them is `p₁` or `p₂`.

    The statement carries `hX : AnticonnectedSet G X`, added during formalization because both
    2.2 and 2.1 — which this printed proof cites — require it (see `FIXES.md` §F4).  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_4

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.5** (printed p. 10)

PAPER: *"Let `G` be Berge, let `X ⊆ V(G)`, and let `P` be a path in `G \ X` of odd
length, with vertices be `p₁`-`⋯`-`pₙ`, such that `p₁,pₙ` are `X`-complete, and no
edge of `P` is `X`-complete.  Let `v ∈ V(G)` be `X`-complete.  Then either `v` is
adjacent to one of `p₁,p₂`, or the only neighbour of `v` in `P*` is `pₙ₋₁`."*

("with vertices be `p₁`-`⋯`-`pₙ`" is a grammatical slip present in both the
published and the arXiv text; the intended reading, "with vertices
`p₁`-`⋯`-`pₙ` in order", is what is transcribed.)

**The printed statement omits a hypothesis its own proof requires: that `X` is
anticonnected.**  As printed, 2.5 assumes only `X ⊆ V(G)`; but its proof opens
*"By 2.2, `v` has a neighbour in `P*`"* and continues *"By 2.1, there is a leap
`a, b` for `P` in `X`"*, and **both 2.2 and 2.1 assume `X` anticonnected**.  The
omission makes the statement not merely unprovable but **false**, so it is
repaired here by adding `hX : AnticonnectedSet G X` — the hypothesis the paper's
own argument uses — and nothing else.

Counterexample to the statement without `hX` (verified by exhaustive enumeration
of all holes of `G` and of `Gᶜ`, `scripts/check_2_5_counterexample.py`).  On
`V = {x₁,x₂,p₁,p₂,p₃,p₄,v}` with edges
`x₁x₂, x₁p₁, x₁p₂, x₁p₄, x₁v, x₂p₁, x₂p₃, x₂p₄, x₂v, p₁p₂, p₂p₃, p₃p₄`:
`G` is Berge (its only holes are the three `4`-holes `{x₁,x₂,p₃,p₂}`,
`{x₁,p₂,p₃,p₄}`, `{x₂,p₁,p₂,p₃}`, and `Gᶜ` has no hole at all).  With
`X = {x₁,x₂}` and `p = [p₁,p₂,p₃,p₄]` every hypothesis of the unrepaired
statement holds — `p` is an induced path of odd length `3` avoiding `X`, its ends
`p₁,p₄` are `X`-complete, `p₂` and `p₃` are not (each misses one of `x₂,x₁`), so
no edge of `p` is `X`-complete, and `v` is `X`-complete — yet `v` is adjacent to
none of `p₁,…,p₄`, so both disjuncts of the conclusion fail.  There `X` is *not*
anticonnected: `x₁x₂ ∈ E(G)`, so `Gᶜ|X` is two isolated vertices.  Full write-up:
`FIXES.md` §F4, `AMBIGUITIES.md` §A24.

`p₁` and `p₂` are the first two vertices of the list (so `p` has the shape
`p₁ :: p₂ :: rest`), `pₙ` is its last vertex and `pₙ₋₁` its last but one
(`p.dropLast.getLast?`).  "The only neighbour of `v` in `P*` is `pₙ₋₁`" is read as
the set equality: the neighbours of `v` in `P*` are exactly `{pₙ₋₁}`. -/
theorem thm_2_5 (G : SimpleGraph V) (hG : Berge G) (X : Set V)
    (hX : AnticonnectedSet G X)
    (p : List V) (p₁ p₂ pn1 pn : V) (rest : List V)
    (hp : IsPathList G p) (hpdef : p = p₁ :: p₂ :: rest)
    (hpn1 : p.dropLast.getLast? = some pn1) (hpnlast : p.getLast? = some pn)
    (hpX : ∀ w ∈ p, w ∉ X) (hodd : Odd (pathLength p))
    (hcp₁ : VertexComplete G p₁ X) (hcpn : VertexComplete G pn X)
    (hnoedge : ¬ ∃ u ∈ p, ∃ v ∈ p, EdgeComplete G X u v)
    (v : V) (hv : VertexComplete G v X) :
    (G.Adj v p₁ ∨ G.Adj v p₂) ∨
    {w : V | w ∈ SPGT.interior p ∧ G.Adj v w} = {pn1} := by
  -- ### Basic decoding of the statement's naming of the vertices of `P`
  have hlen2 : 2 ≤ p.length := by rw [hpdef]; simp
  have hhead : p.head? = some p₁ := by rw [hpdef]; rfl
  have hPF : IsPathFrom G p p₁ pn := ⟨hp, hhead, hpnlast⟩
  have hnd : p.Nodup := hp.2.1
  have hp0 : (p[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
  have hp1 : (p[1]'(by omega)) = p₂ := by simp [hpdef]
  have hplast : (p[p.length - 1]'(by omega)) = pn :=
    PathBasics.getElem_last_of_getLast? hpnlast (by omega)
  have hdl : p.dropLast.length = p.length - 1 := by simp
  have hpn1' : (p[p.length - 2]'(by omega)) = pn1 := by
    have hlt : p.length - 2 < p.dropLast.length := by omega
    have h := hpn1
    rw [List.getLast?_eq_getElem?, show p.dropLast.length - 1 = p.length - 2 from by omega,
      List.getElem?_eq_getElem hlt] at h
    exact (List.getElem_dropLast hlt).symm.trans (Option.some_injective _ h)
  have hp₁mem : p₁ ∈ p := by rw [hpdef]; simp
  have hp₂mem : p₂ ∈ p := by rw [hpdef]; simp
  -- ### "we may assume that `p_{n-1}` is not its only such neighbour"
  by_cases hset : {w : V | w ∈ SPGT.interior p ∧ G.Adj v w} = {pn1}
  · exact Or.inr hset
  refine Or.inl ?_
  -- "By 2.2, `v` has a neighbour in `P*`"
  obtain ⟨w0, hw0i, hw0adj⟩ :=
    thm_2_2 G hG X hX p p₁ pn hPF hpX hodd hcp₁ hcpn hnoedge v hv
  have hex : ∃ w ∈ SPGT.interior p, G.Adj v w ∧ w ≠ pn1 := by
    by_contra hcon
    push Not at hcon
    refine absurd ?_ hset
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · have he : w0 = pn1 := hcon w0 hw0i hw0adj
      exact ⟨he ▸ hw0i, he ▸ hw0adj⟩
    · rintro x ⟨hx1, hx2⟩
      exact hcon x hx1 hx2
  obtain ⟨w, hwi, hwadj, hwne⟩ := hex
  obtain ⟨k, hk, hk1, hk2, hpk⟩ := PathBasics.exists_getElem_of_mem_interior hp hwi
  -- `w ≠ p_{n-1}` turns the index bound `k ≤ n-2` into `k ≤ n-3`
  have hkne : k ≠ p.length - 2 := by
    intro hkeq
    refine hwne ?_
    rw [← hpk, ← hpn1']
    exact hnd.getElem_inj_iff.mpr hkeq
  have hoddm : pathLength p % 2 = 1 := Nat.odd_iff.mp hodd
  have hlenp : pathLength p = p.length - 1 := PathBasics.pathLength_eq p
  -- ### "If `P` has length ≤ 3 then the result follows"
  rcases (show pathLength p = 3 ∨ 5 ≤ pathLength p by omega) with hcase3 | hcase5
  · -- `n = 4`, so `1 ≤ k ≤ n-3 = 1`, i.e. `w = p₂`
    have hk1' : k = 1 := by omega
    refine Or.inr ?_
    have hpw : p₂ = w := by
      rw [← hp1, ← hpk]
      exact hnd.getElem_inj_iff.mpr (by omega)
    exact hpw ▸ hwadj
  -- ### "By 2.1, there is a leap a, b for P in X"
  have hn6 : 6 ≤ p.length := by omega
  rcases thm_2_1 G hG X hX p p₁ pn hPF hpX hodd hcp₁ hcpn with
    hc1 | ⟨-, a, haX, b, hbX, hleap⟩ | ⟨hc3, -⟩
  · exact absurd hc1 hnoedge
  · obtain ⟨-, -, hab, hnab, hadja, hadjb⟩ := hleap
    have hanp : a ∉ p := fun h => hpX a h haX
    have hbnp : b ∉ p := fun h => hpX b h hbX
    have hap₁ : G.Adj a p₁ := by rw [← hp0]; exact (hadja 0 (by omega)).mpr (Or.inl rfl)
    have hap₂ : G.Adj a p₂ := by
      rw [← hp1]; exact (hadja 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    have hbp₁ : G.Adj b p₁ := by rw [← hp0]; exact (hadjb 0 (by omega)).mpr (Or.inl rfl)
    have hbp₁ne : b ≠ p₁ := fun h => hbnp (h ▸ hp₁mem)
    have hap₁ne : a ≠ p₁ := fun h => hanp (h ▸ hp₁mem)
    have hap₂ne : a ≠ p₂ := fun h => hanp (h ▸ hp₂mem)
    -- `P₂ = P \ {p₁, p_{n-1}, p_n}`, the slice of `p` on indices `1 … n-3`
    obtain ⟨P₂, hP₂list, hP₂head, hP₂mem⟩ :
        ∃ Q : List V, IsPathList G Q ∧ Q.head? = some (p[1]'(by omega)) ∧
          (∀ x, x ∈ Q ↔ ∃ (m : ℕ) (hm : m < p.length),
            1 ≤ m ∧ m ≤ p.length - 3 ∧ (p[m]'hm) = x) :=
      ⟨(p.drop 1).take (p.length - 3 - 1 + 1),
        PathBasics.isPathList_slice hp (by omega) (by omega),
        PathBasics.head?_slice p (by omega) (by omega),
        fun x => PathBasics.mem_slice_iff p (by omega) (by omega)⟩
    have hP₂sub : ∀ x ∈ P₂, x ∈ p := by
      intro x hx
      obtain ⟨m, hm, -, -, hmx⟩ := (hP₂mem x).mp hx
      exact hmx ▸ List.getElem_mem hm
    -- "v can be linked onto {p₁, p₂, a} via b-p₁, P \ {p₁, p_{n-1}, p_n}, a"
    have hlink : VertexCanBeLinkedOntoTriangle G v p₁ p₂ a := by
      refine ⟨[b, p₁], P₂, [a], ⟨PathBasics.isPathList_pair hbp₁, hP₂list,
        PathBasics.isPathList_singleton G a⟩, ⟨?_, ?_, ?_⟩,
        ⟨Or.inr (by simp), Or.inl (by rw [hP₂head, hp1]), Or.inl (by simp)⟩,
        ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      -- the three paths are pairwise vertex-disjoint
      · intro x hx hxP2
        obtain ⟨m, hm, hm1, hm2, hmx⟩ := (hP₂mem x).mp hxP2
        rcases List.mem_cons.mp hx with hxb | hx'
        · exact hbnp (hxb ▸ (hmx ▸ List.getElem_mem hm))
        · have hxp1 : x = p₁ := by simpa using hx'
          have hzero : (p[m]'hm) = (p[0]'(show 0 < p.length by omega)) := by
            rw [hmx, hxp1]; exact hp0.symm
          have := hnd.getElem_inj_iff.mp hzero
          omega
      · intro x hx hxa
        have hxa' : x = a := by simpa using hxa
        rcases List.mem_cons.mp hx with hxb | hx'
        · exact hab (hxa' ▸ hxb ▸ rfl : a = b)
        · have hxp1 : x = p₁ := by simpa using hx'
          exact hap₁ne (hxa' ▸ hxp1)
      · intro x hx hxa
        have hxa' : x = a := by simpa using hxa
        exact hanp (hxa' ▸ hP₂sub x hx)
      -- `p₁p₂` is the unique edge between `V(P₁)` and `V(P₂)`
      · intro x hx y hy
        obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hP₂mem y).mp hy
        rcases List.mem_cons.mp hx with hxb | hx'
        · refine iff_of_false ?_ ?_
          · intro hadjxy
            have := (hadjb m hm).mp (hxb ▸ hadjxy)
            omega
          · rintro ⟨hc, -⟩
            exact hbp₁ne (hxb ▸ hc : b = p₁)
        · have hxp1 : x = p₁ := by simpa using hx'
          have hEq : ((p[m]'hm) = p₂) ↔ m = 1 := by
            rw [← hp1]; exact hnd.getElem_inj_iff
          have hAdj : G.Adj p₁ (p[m]'hm) ↔ m = 1 := by
            rw [← hp0, PathBasics.path_adj_iff hp (show 0 < p.length by omega) hm]
            omega
          rw [hxp1, hAdj, hEq]
          simp
      -- `p₁a` is the unique edge between `V(P₁)` and `V(P₃)`
      · intro x hx y hy
        have hya : y = a := by simpa using hy
        rcases List.mem_cons.mp hx with hxb | hx'
        · rw [hxb, hya]
          refine iff_of_false (fun h => hnab h.symm) ?_
          rintro ⟨hc, -⟩
          exact hbp₁ne hc
        · have hxp1 : x = p₁ := by simpa using hx'
          rw [hxp1, hya]
          exact iff_of_true hap₁.symm ⟨rfl, rfl⟩
      -- `p₂a` is the unique edge between `V(P₂)` and `V(P₃)`
      · intro x hx y hy
        have hya : y = a := by simpa using hy
        obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hP₂mem x).mp hx
        have hEq : ((p[m]'hm) = p₂) ↔ m = 1 := by
          rw [← hp1]; exact hnd.getElem_inj_iff
        have hAdj : G.Adj (p[m]'hm) a ↔ m = 1 := by
          constructor
          · intro h
            have := (hadja m hm).mp h.symm
            omega
          · intro h
            exact ((hadja m hm).mpr (by omega)).symm
        rw [hya, hAdj, hEq]
        simp
      -- `v` has a neighbour on each of the three paths
      · exact ⟨b, by simp, hv b hbX⟩
      · exact ⟨w, (hP₂mem w).mpr ⟨k, hk, hk1, by omega, hpk⟩, hwadj⟩
      · exact ⟨a, by simp, hv a haX⟩
    -- "so v has two neighbours in the triangle, by 2.4, and the claim follows"
    rcases thm_2_4 G hG v p₁ p₂ a hlink with ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₂, -⟩
    · exact Or.inl h₁
    · exact Or.inl h₁
    · exact Or.inr h₂
  · omega


end SPGT

end Workspace.Statements.S02
