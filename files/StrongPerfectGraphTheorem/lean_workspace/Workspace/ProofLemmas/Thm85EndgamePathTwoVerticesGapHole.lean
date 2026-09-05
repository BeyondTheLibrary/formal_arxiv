import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.StripSystemBasics

/-!
# 8.5, the closing paragraph for `n = 1`: the printed odd hole

PAPER (printed p. 45, the last sentence of the proof of 8.5):

*"But then the path `f₁-r_hj-R_hj-r_jh-r_ji-f₁` is an odd hole, a contradiction."*

The cycle is: the vertex `f₁` outside the strip system, the `hj`-rung `R_hj` traversed from its
end `r_hj ∈ N_h` to its end `r_jh ∈ N_j`, then a vertex `r_ji ∈ N_j ∩ S_ij`, and back to `f₁`.
It is induced because

* `r_hj` is the only vertex of the rung adjacent to `f₁` (that is claim (4)),
* the only edges between `S_hj` and `S_ij` join `N_j ∩ S_hj` to `N_j ∩ S_ij`, and the rung meets
  `N_j` only in `r_jh`,
* `f₁` lies outside `V(S,N)`, and the strips `S_hj` and `S_ij` are disjoint.

Its length is `pathLength R_hj + 3`, so `G` being Berge forces `pathLength R_hj` to be odd as
soon as it is nonzero.  That is the form in which the sentence is used: combined with the
parity of the four rungs round a cycle of `J` it pins `pathLength R_hj = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapHole

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*}

/-- **"But then the path `f₁-r_hj-R_hj-r_jh-r_ji-f₁` is an odd hole, a contradiction"**
(printed p. 45).

`L` is the `hj`-rung `R_hj`; `r` is its end `r_hj` in `N_h`, the unique vertex of `L` adjacent
to `f₁`; and `b` is `r_ji`, a vertex of `N_j ∩ S_ij` adjacent to `f₁`.  If `L` has nonzero
length the cycle has length `pathLength L + 3 ≥ 4`, so it is a hole, and `G` being Berge makes
`pathLength L` odd. -/
theorem odd_of_pos {G : SimpleGraph V} (hG : Berge G) {J : SimpleGraph U}
    {S : U → U → Set V} {N : U → Set V} (hSN : IsJStripSystem G J S N)
    {h i j : U} (hij : J.Adj i j) (hhi : h ≠ i)
    {L : List V} (hL : IsUVRung G J S N h j L)
    {f₁ r b : V} (hf₁ : f₁ ∉ stripSystemVertices J S)
    (hrL : r ∈ L) (hrN : r ∈ N h) (hrf : G.Adj r f₁)
    (hruniq : ∀ x ∈ L, G.Adj x f₁ → x = r)
    (hbN : b ∈ N j) (hbS : b ∈ S i j) (hbf : G.Adj b f₁)
    (hpos : 0 < pathLength L) :
    Odd (pathLength L) := by
  classical
  have hhj : J.Adj h j := hL.1
  obtain ⟨-, s, t, hpath, hsub, hsN, htN⟩ := hL
  have hsL : s ∈ L := List.mem_of_mem_head? hpath.2.1
  have htL : t ∈ L := List.mem_of_getLast? hpath.2.2
  have hrs : r = s := (hsN r hrL).mp hrN
  subst hrs
  -- the two strips at `j`
  have hSjh : S j h = S h j := (StripSystemBasics.strip_symm hSN hhj).symm
  have hSji : S j i = S i j := (StripSystemBasics.strip_symm hSN hij).symm
  have hjh : J.Adj j h := hhj.symm
  have hji : J.Adj j i := hij.symm
  have hhine : h ≠ i := hhi
  -- `b` is not on the rung, and `f₁` is not either
  have hLsub : ∀ x ∈ L, x ∈ S h j := hsub
  have hbnotL : b ∉ L := by
    intro hbL
    have h1 : b ∈ S h j := hLsub b hbL
    have h2 : s(h, j) = s(i, j) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hhj hij h1 hbS
    rcases Sym2.eq_iff.mp h2 with ⟨e1, -⟩ | ⟨e1, e2⟩
    · exact hhi e1
    · exact hij.ne' e2
  have hfnotL : f₁ ∉ L := fun hx =>
    hf₁ (StripSystemBasics.strip_subset_vertices hhj (hLsub f₁ hx))
  have hbf₁ne : b ≠ f₁ := by
    intro hc
    exact hf₁ (hc ▸ StripSystemBasics.strip_subset_vertices hij hbS)
  -- the edge `r_jh r_ji`
  have htb : G.Adj t b :=
    StripSystemBasics.Nuv_complete hSN hjh hji hhi t
      ⟨(htN t htL).mpr rfl, by rw [hSjh]; exact hLsub t htL⟩ b ⟨hbN, by rw [hSji]; exact hbS⟩
  -- the second path of the cycle
  have hR : IsPathFrom G [b, f₁] b f₁ := by
    refine ⟨⟨by simp, by simp [hbf₁ne], ?_⟩, rfl, rfl⟩
    intro p q hp hq
    have hp' : p < 2 := by simpa using hp
    have hq' : q < 2 := by simpa using hq
    interval_cases p <;> interval_cases q <;> simp [hbf, hbf.symm, hbf₁ne, hbf₁ne.symm]
  -- the cycle is a hole
  have hhole : IsHoleList G (L ++ [b, f₁]) := by
    refine PathGlue.glue_hole hpath hR ?_ ?_ ?_
    · intro x hx hxR
      have hx2 : x = b ∨ x = f₁ := by simpa using hxR
      rcases hx2 with hc | hc
      · exact hbnotL (hc ▸ hx)
      · exact hfnotL (hc ▸ hx)
    · intro x hx y hy
      have hy2 : y = b ∨ y = f₁ := by simpa using hy
      rcases hy2 with hyb | hyf
      · rw [hyb]
        constructor
        · intro hadj
          have hxNj := (StripSystemBasics.mem_N_of_adj hSN hjh hji hhi
            (by rw [hSjh]; exact hLsub x hx) (by rw [hSji]; exact hbS) hadj).1
          exact Or.inl ⟨(htN x hx).mp hxNj, rfl⟩
        · rintro (⟨hxt, -⟩ | ⟨-, hc⟩)
          · rw [hxt]; exact htb
          · exact absurd hc hbf₁ne
      · rw [hyf]
        constructor
        · intro hadj
          exact Or.inr ⟨hruniq x hx hadj, rfl⟩
        · rintro (⟨-, hc⟩ | ⟨hxs, -⟩)
          · exact absurd hc.symm hbf₁ne
          · rw [hxs]; exact hrf
    · have := PathBasics.path_length_pos hpath.1
      simp only [pathLength] at hpos
      simp only [List.length_cons, List.length_nil]
      omega
  have heven := hG.1 _ hhole
  simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at heven
  simp only [pathLength] at hpos ⊢
  have hlen : 0 < L.length := PathBasics.path_length_pos hpath.1
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff]
  omega

end Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapHole
