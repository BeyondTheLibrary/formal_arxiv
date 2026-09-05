import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm81Cycle
import Workspace.ProofLemmas.Thm81CycleEven

set_option autoImplicit false

namespace Workspace.Statements.S08

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **8.1** (printed p. 40)

PAPER: *"Let `(S,N)` be a `J`-strip system in a Berge graph `G`, where `J` is 3-connected.
Then for every `uv ∈ E(J)`, all `uv`-rungs have lengths of the same parity."*

Notes on the transcription.

* A `uv`-rung is `StripSystems.IsUVRung G J S N u v R`, a path of `G` given by the list `R`
  of its vertices in order, and its length is `Core.pathLength R`.
* *"All `uv`-rungs have lengths of the same parity"* is: any two `uv`-rungs have lengths of
  the same parity.  (The `IsUVRung` predicate already carries `J.Adj u v`, so the hypothesis
  `huv` merely records the paper's `uv ∈ E(J)`.) -/
theorem thm_8_1 {U : Type*} [Fintype U] (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (u v : U) (huv : J.Adj u v) (R R' : List V)
    (hR : IsUVRung G J S N u v R) (hR' : IsUVRung G J S N u v R') :
    (Even (pathLength R) ↔ Even (pathLength R')) := by
  classical
  -- "Since `J` is 3-connected, there is a cycle `C` of `J` with `|V(C)| ≥ 4` and `uv ∈ E(C)`."
  obtain ⟨w, hw2, hnd, hadj⟩ :=
    Workspace.ProofLemmas.Thm81Cycle.exists_cycle_through_edge J hJ huv
  -- "For each `xy ∈ E(C)` different from `uv`, choose an `xy`-rung `R_xy`."
  obtain ⟨Rs, hRs, -⟩ := Workspace.ProofLemmas.StripSystemBasics.exists_special_rungs hSN
  have hlen : 4 ≤ (u :: v :: w).length := by
    simp only [List.length_cons]
    omega
  have hrot : (u :: v :: w).rotate 1 = v :: (w ++ [u]) := by
    simp [List.rotate_cons_succ]
  have hzip : (u :: v :: w).zip ((u :: v :: w).rotate 1)
      = (u, v) :: ((v :: w).zip (w ++ [u])) := by
    rw [hrot]
    rfl
  have hune : u ∉ (v :: w) := (List.nodup_cons.mp hnd).1
  have hfst : ∀ p ∈ (v :: w).zip (w ++ [u]), p.1 ≠ u := by
    rintro ⟨a, b⟩ hp
    have := (List.of_mem_zip hp).1
    intro hau
    exact hune (hau ▸ this)
  -- The key computation: for any `uv`-rung `Q`, the hole through `Q` and the `R_xy` is even.
  have key : ∀ Q : List V, IsUVRung G J S N u v Q →
      Even (pathLength Q +
        ((((v :: w).zip (w ++ [u])).map (fun p => pathLength (Rs p.1 p.2))).sum
          + (u :: v :: w).length)) := by
    intro Q hQ
    set F : U → U → List V := fun x y => if x = u ∧ y = v then Q else Rs x y with hF
    have hFuv : F u v = Q := by simp [hF]
    have hFother : ∀ p ∈ (v :: w).zip (w ++ [u]), F p.1 p.2 = Rs p.1 p.2 := by
      intro p hp
      have := hfst p hp
      simp [hF, this]
    have hFother' : ∀ p ∈ (v :: w).zip (w ++ [u]),
        pathLength (F p.1 p.2) = pathLength (Rs p.1 p.2) := by
      intro p hp
      rw [hFother p hp]
    have hmain := Workspace.ProofLemmas.Thm81CycleEven.even_cycle_sum G hG J S N hSN
      (u :: v :: w) hlen hnd hadj F ?_
    · rw [hzip] at hmain
      simp only [List.map_cons, List.sum_cons] at hmain
      rw [hFuv] at hmain
      rw [List.map_congr_left hFother'] at hmain
      · rw [← add_assoc]
        exact hmain
    · intro p hp
      rw [hzip] at hp
      rcases List.mem_cons.mp hp with h | h
      · subst h
        simpa [hFuv] using hQ
      · rw [hFother p h]
        exact hRs p.1 p.2 (hadj p (by rw [hzip]; exact List.mem_cons_of_mem _ h))
  have h1 := key R hR
  have h2 := key R' hR'
  rw [Nat.even_add] at h1 h2
  exact h1.trans h2.symm


end SPGT

end Workspace.Statements.S08
