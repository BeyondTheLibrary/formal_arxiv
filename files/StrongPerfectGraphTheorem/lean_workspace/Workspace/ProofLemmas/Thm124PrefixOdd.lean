import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm121C3PathCons
import Workspace.Statements.S02.Thm_2_2

/-!
# 12.4(1), the parity computation

PAPER (printed p. 74, claim (1) of the proof of 12.4):

*"(1) `S`, `T` both have odd length, and therefore `s`, `t` are different.*

*For choose `a ∈ A` and `b ∈ B`, both `Q`-complete; then `a`-`a₀`-`S`-`s` has length `> 1`, and
its ends are `Q`-complete and its internal vertices are not, and `b` is also `Q`-complete and
has no neighbours in the interior of `a`-`a₀`-`S`-`s`.  By 2.2, this path is even, and so `S` is
odd, and similarly `T` is odd."*

The two halves of the argument (for `S` and for `T`) are the same computation read from the two
ends of `R₀`, so it is isolated here as one lemma about an abstract path `R`:

* `R` is a path avoiding `Q`, and `i` is the **first** index at which `R` carries a
  `Q`-complete vertex, with `0 < i`;
* `a` is a vertex outside `R`, `Q`-complete, adjacent to `R₀` alone among `V(R)` (in the
  application, `a ∈ A` and `R` starts at the left-star `a₀`);
* `b` is `Q`-complete with no neighbour among `R₀, …, R_{i-1}` (in the application, `b ∈ B`,
  which is anticomplete to the left-star `a₀` and to the interior of the banister).

Then `i`, which is the length of the initial stretch `a₀`-`S`-`s`, is odd.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm124PrefixOdd

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The printed computation *"`a`-`a₀`-`S`-`s` … By 2.2, this path is even, and so `S` is
odd"*. -/
theorem prefix_odd (G : SimpleGraph V) (hG : Berge G) (Q : Set V)
    (hQ : AnticonnectedSet G Q)
    (R : List V) (hR : IsPathList G R)
    (i : ℕ) (hi : i < R.length) (hi0 : 0 < i)
    (hcomp : VertexComplete G (R[i]'hi) Q)
    (hmin : ∀ (k : ℕ) (hk : k < R.length), k < i → ¬ VertexComplete G (R[k]'hk) Q)
    (hRQ : ∀ w ∈ R, w ∉ Q)
    (a : V) (haR : a ∉ R) (haQ : VertexComplete G a Q)
    (hadj : ∀ (k : ℕ) (hk : k < R.length), (G.Adj a (R[k]'hk) ↔ k = 0))
    (b : V) (hbQ : VertexComplete G b Q)
    (hbanti : ∀ (k : ℕ) (hk : k < R.length), k < i → ¬ G.Adj b (R[k]'hk)) :
    Odd i := by
  classical
  have h0len : 0 < R.length := by omega
  -- the initial stretch `a₀`-`S`-`s` of `R`
  set S : List V := (R.drop 0).take (i - 0 + 1) with hSdef
  have hSlen : S.length = i - 0 + 1 := PathBasics.length_slice R (by omega) hi
  have hSmem : ∀ x ∈ S, ∃ (k : ℕ) (hk : k < R.length), k ≤ i ∧ (R[k]'hk) = x := by
    intro x hx
    obtain ⟨k, hk, -, hki, hkx⟩ := (PathBasics.mem_slice_iff R (by omega) hi).mp hx
    exact ⟨k, hk, hki, hkx⟩
  have hSsub : ∀ x ∈ S, x ∈ R := by
    intro x hx
    obtain ⟨k, hk, -, rfl⟩ := hSmem x hx
    exact List.getElem_mem hk
  have hSfrom : IsPathFrom G S (R[0]'h0len) (R[i]'hi) :=
    PathBasics.isPathFrom_slice hR hi0 hi
  -- the path `a`-`a₀`-`S`-`s`
  have haS : a ∉ S := fun h => haR (hSsub a h)
  have hadjS : ∀ y ∈ S, (G.Adj a y ↔ y = (R[0]'h0len)) := by
    intro y hy
    obtain ⟨k, hk, -, rfl⟩ := hSmem y hy
    rw [hadj k hk]
    constructor
    · rintro rfl; rfl
    · intro h
      by_contra hk0
      exact PathBasics.path_ne_of_ne_index hR hk h0len hk0 h
  set P : List V := a :: S with hPdef
  have hPfrom : IsPathFrom G P a (R[i]'hi) :=
    Thm121C3PathCons.isPathFrom_cons hSfrom haS hadjS
  have hPlen : pathLength P = i + 1 := by
    rw [hPdef, PathBasics.pathLength_cons, hSlen]
    omega
  -- every vertex of `P` lies outside `Q`
  have hanQ : a ∉ Q := fun h => G.irrefl (haQ a h)
  have hPQ : ∀ w ∈ P, w ∉ Q := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hanQ
    · exact hRQ w (hSsub w hw)
  -- the `Q`-complete vertices of `P` are exactly its two ends
  have hPcomplete : ∀ w ∈ P, VertexComplete G w Q → w = a ∨ w = (R[i]'hi) := by
    intro w hw hwQ
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl rfl
    · obtain ⟨k, hk, hki, rfl⟩ := hSmem w hw
      refine Or.inr ?_
      rcases lt_or_eq_of_le hki with hlt | rfl
      · exact absurd hwQ (hmin k hk hlt)
      · rfl
  have hnoedge : ¬ ∃ u ∈ P, ∃ v ∈ P, EdgeComplete G Q u v := by
    rintro ⟨u, hu, v, hv, hadjuv, huQ, hvQ⟩
    have hai : ¬ G.Adj a (R[i]'hi) := by
      rw [hadj i hi]
      omega
    rcases hPcomplete u hu huQ with rfl | rfl <;> rcases hPcomplete v hv hvQ with rfl | rfl
    · exact G.irrefl hadjuv
    · exact hai hadjuv
    · exact hai hadjuv.symm
    · exact G.irrefl hadjuv
  -- PAPER: *"By 2.2, this path is even"*
  by_contra hodd
  have hoddP : Odd (pathLength P) := by
    rw [hPlen]
    rcases Nat.even_or_odd i with he | ho
    · exact Even.add_one he
    · exact absurd ho hodd
  obtain ⟨w, hwint, hbw⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hG Q hQ P a (R[i]'hi) hPfrom hPQ hoddP haQ hcomp
      hnoedge b hbQ
  rw [PathBasics.mem_interior_iff_of_pathFrom hPfrom] at hwint
  obtain ⟨hwP, hwa, hws⟩ := hwint
  rcases List.mem_cons.mp hwP with rfl | hwS
  · exact hwa rfl
  · obtain ⟨k, hk, hki, rfl⟩ := hSmem w hwS
    have hklt : k < i := by
      rcases lt_or_eq_of_le hki with h | rfl
      · exact h
      · exact absurd rfl hws
    exact hbanti k hk hklt hbw

/-- The mirror image of `prefix_odd`, read from the far end of `R` — the printed
*"and similarly `T` is odd"*.  Here `i` is the **last** index at which `R` carries a
`Q`-complete vertex, `a` is attached to the last vertex of `R` alone, and `b` has no
neighbour among `R_{i+1}, …`; the conclusion is that the terminal stretch, of length
`R.length - 1 - i`, is odd. -/
theorem suffix_odd (G : SimpleGraph V) (hG : Berge G) (Q : Set V)
    (hQ : AnticonnectedSet G Q)
    (R : List V) (hR : IsPathList G R)
    (i : ℕ) (hi : i < R.length) (hilast : i < R.length - 1)
    (hcomp : VertexComplete G (R[i]'hi) Q)
    (hmax : ∀ (k : ℕ) (hk : k < R.length), i < k → ¬ VertexComplete G (R[k]'hk) Q)
    (hRQ : ∀ w ∈ R, w ∉ Q)
    (a : V) (haR : a ∉ R) (haQ : VertexComplete G a Q)
    (hadj : ∀ (k : ℕ) (hk : k < R.length), (G.Adj a (R[k]'hk) ↔ k = R.length - 1))
    (b : V) (hbQ : VertexComplete G b Q)
    (hbanti : ∀ (k : ℕ) (hk : k < R.length), i < k → ¬ G.Adj b (R[k]'hk)) :
    Odd (R.length - 1 - i) := by
  classical
  have hrevlen : R.reverse.length = R.length := List.length_reverse
  have hrev : ∀ (k : ℕ) (hk : k < R.reverse.length),
      (R.reverse[k]'hk) = R[R.length - 1 - k]'(by rw [hrevlen] at hk; omega) :=
    fun k hk => List.getElem_reverse hk
  have hi' : R.length - 1 - i < R.reverse.length := by rw [hrevlen]; omega
  refine Workspace.ProofLemmas.Thm124PrefixOdd.prefix_odd G hG Q hQ R.reverse
    (PathBasics.isPathList_reverse hR) (R.length - 1 - i) hi' (by omega) ?_ ?_ ?_ a ?_ haQ ?_
    b hbQ ?_
  · rw [hrev _ hi']
    have : R.length - 1 - (R.length - 1 - i) = i := by omega
    simpa [this] using hcomp
  · intro k hk hklt
    rw [hrev k hk]
    exact hmax _ _ (by rw [hrevlen] at hk; omega)
  · intro w hw
    exact hRQ w (List.mem_reverse.mp hw)
  · exact fun h => haR (List.mem_reverse.mp h)
  · intro k hk
    rw [hrev k hk, hadj _ (by rw [hrevlen] at hk; omega)]
    rw [hrevlen] at hk
    omega
  · intro k hk hklt
    rw [hrev k hk]
    exact hbanti _ _ (by rw [hrevlen] at hk; omega)

end Workspace.ProofLemmas.Thm124PrefixOdd
