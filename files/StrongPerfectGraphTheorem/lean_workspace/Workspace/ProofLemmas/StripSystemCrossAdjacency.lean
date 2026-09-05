import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics

/-!
# Edges of `G` between two different strips

PAPER (printed p. 39, the fifth and sixth axioms of a `J`-strip system):

* *"If `uv, wx ∈ E(J)` with `u,v,w,x` all distinct, then there are no edges between `S_{uv}` and
  `S_{wx}`"*;
* *"If `uv, uw ∈ E(J)` with `v ≠ w`, then `N_u ∩ S_{uv}` is complete to `N_u ∩ S_{uw}`, and there
  are no other edges between `S_{uv}` and `S_{uw}`."*

Together these two axioms say exactly one thing, which the paper then uses without further
comment (it is what makes the union of a choice of rungs a *line graph*, the remark following the
proof of 8.1 on printed p. 40): **two vertices lying in different strips are adjacent in `G` if
and only if the two edges of `J` share an end `w` and both vertices lie in `N_w`.**  That is
`adj_iff_of_ne_edges` below; `adj_iff_of_shared` is the special case where the shared end is
given, i.e. axiom 6 with its two halves packaged as one `Iff`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.StripSystemCrossAdjacency

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}
  {S : U → U → Set V} {N : U → Set V}

/-- **Axiom 6, both halves at once.**  For two edges `wb`, `wd` of `J` sharing the end `w`, a
vertex of `S_{wb}` and a vertex of `S_{wd}` are adjacent in `G` exactly when both lie in
`N_w`. -/
theorem adj_iff_of_shared (h : IsJStripSystem G J S N) {w b d : U} {x y : V}
    (hwb : J.Adj w b) (hwd : J.Adj w d) (hbd : b ≠ d)
    (hx : x ∈ S w b) (hy : y ∈ S w d) :
    G.Adj x y ↔ (x ∈ N w ∧ y ∈ N w) := by
  constructor
  · intro hadj
    exact StripSystemBasics.mem_N_of_adj h hwb hwd hbd hx hy hadj
  · rintro ⟨hxn, hyn⟩
    exact StripSystemBasics.Nuv_complete h hwb hwd hbd x ⟨hxn, hx⟩ y ⟨hyn, hy⟩

/-- **Adjacency between two different strips.**  If `ab` and `cd` are distinct edges of `J`,
`x ∈ S_{ab}` and `y ∈ S_{cd}`, then `x` and `y` are adjacent in `G` if and only if the two edges
have a common end `w` with `x, y ∈ N_w`.

(*Only if* is axiom 5 — all four ends distinct forbids any edge — followed by axiom 6's second
half; *if* is axiom 6's first half.) -/
theorem adj_iff_of_ne_edges (h : IsJStripSystem G J S N) {a b c d : U} {x y : V}
    (hab : J.Adj a b) (hcd : J.Adj c d) (hne : s(a, b) ≠ s(c, d))
    (hx : x ∈ S a b) (hy : y ∈ S c d) :
    G.Adj x y ↔ ∃ w : U, (w = a ∨ w = b) ∧ (w = c ∨ w = d) ∧ x ∈ N w ∧ y ∈ N w := by
  constructor
  · intro hadj
    by_cases hac : a = c
    · have hbd : b ≠ d := by
        intro hh
        apply hne
        rw [hac, hh]
      have hy' : y ∈ S a d := by rw [hac]; exact hy
      have had : J.Adj a d := by rw [hac]; exact hcd
      obtain ⟨h1, h2⟩ := StripSystemBasics.mem_N_of_adj h hab had hbd hx hy' hadj
      exact ⟨a, Or.inl rfl, Or.inl hac, h1, h2⟩
    · by_cases had : a = d
      · have hca : J.Adj a c := by rw [had]; exact hcd.symm
        have hy' : y ∈ S a c := by
          rw [StripSystemBasics.strip_symm h hca, had]
          exact hy
        have hbc : b ≠ c := by
          intro hh
          apply hne
          rw [hh, had]
          exact Sym2.eq_swap
        obtain ⟨h1, h2⟩ := StripSystemBasics.mem_N_of_adj h hab hca hbc hx hy' hadj
        exact ⟨a, Or.inl rfl, Or.inr had, h1, h2⟩
      · by_cases hbc : b = c
        · have hbd : J.Adj b d := by rw [hbc]; exact hcd
          have hx' : x ∈ S b a := by
            rw [← StripSystemBasics.strip_symm h hab]; exact hx
          have hy' : y ∈ S b d := by rw [hbc]; exact hy
          have had' : a ≠ d := by
            intro hh
            apply hne
            rw [hbc, hh]
            exact Sym2.eq_swap
          obtain ⟨h1, h2⟩ :=
            StripSystemBasics.mem_N_of_adj h hab.symm hbd had' hx' hy' hadj
          exact ⟨b, Or.inr rfl, Or.inl hbc, h1, h2⟩
        · by_cases hbd : b = d
          · have hcb : J.Adj c b := by rw [hbd]; exact hcd
            have hx' : x ∈ S b a := by
              rw [← StripSystemBasics.strip_symm h hab]; exact hx
            have hy' : y ∈ S b c := by
              rw [StripSystemBasics.strip_symm h hcb.symm, hbd]
              exact hy
            have hac' : a ≠ c := hac
            obtain ⟨h1, h2⟩ :=
              StripSystemBasics.mem_N_of_adj h hab.symm hcb.symm hac' hx' hy' hadj
            exact ⟨b, Or.inr rfl, Or.inr hbd, h1, h2⟩
          · exfalso
            have h1 : a ≠ b := hab.ne
            have h2 : c ≠ d := hcd.ne
            have hnd : [a, b, c, d].Nodup := by
              simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
                or_false, not_or]
              tauto
            exact StripSystemBasics.not_adj_of_disjoint_edges h hab hcd hnd hx hy hadj
  · rintro ⟨w, hw1, hw2, hxn, hyn⟩
    rcases hw1 with h1 | h1
    · rcases hw2 with h2 | h2
      · have hwb : J.Adj w b := by rw [h1]; exact hab
        have hwd : J.Adj w d := by rw [h2]; exact hcd
        have hxw : x ∈ S w b := by rw [h1]; exact hx
        have hyw : y ∈ S w d := by rw [h2]; exact hy
        have hbd : b ≠ d := by
          intro hh
          apply hne
          rw [← h1, ← h2, hh]
        exact (adj_iff_of_shared h hwb hwd hbd hxw hyw).mpr ⟨hxn, hyn⟩
      · have hwb : J.Adj w b := by rw [h1]; exact hab
        have hwc : J.Adj w c := by rw [h2]; exact hcd.symm
        have hxw : x ∈ S w b := by rw [h1]; exact hx
        have hyw : y ∈ S w c := by
          rw [StripSystemBasics.strip_symm h hwc, h2]; exact hy
        have hbc : b ≠ c := by
          intro hh
          apply hne
          rw [← h1, ← h2, hh]
          exact Sym2.eq_swap
        exact (adj_iff_of_shared h hwb hwc hbc hxw hyw).mpr ⟨hxn, hyn⟩
    · rcases hw2 with h2 | h2
      · have hwa : J.Adj w a := by rw [h1]; exact hab.symm
        have hwd : J.Adj w d := by rw [h2]; exact hcd
        have hxw : x ∈ S w a := by
          rw [StripSystemBasics.strip_symm h hwa, h1]; exact hx
        have hyw : y ∈ S w d := by rw [h2]; exact hy
        have had : a ≠ d := by
          intro hh
          apply hne
          rw [← h1, ← h2, hh]
          exact Sym2.eq_swap
        exact (adj_iff_of_shared h hwa hwd had hxw hyw).mpr ⟨hxn, hyn⟩
      · have hwa : J.Adj w a := by rw [h1]; exact hab.symm
        have hwc : J.Adj w c := by rw [h2]; exact hcd.symm
        have hxw : x ∈ S w a := by
          rw [StripSystemBasics.strip_symm h hwa, h1]; exact hx
        have hyw : y ∈ S w c := by
          rw [StripSystemBasics.strip_symm h hwc, h2]; exact hy
        have hac : a ≠ c := by
          intro hh
          apply hne
          rw [← h1, ← h2, hh]
        exact (adj_iff_of_shared h hwa hwc hac hxw hyw).mpr ⟨hxn, hyn⟩

end Workspace.ProofLemmas.StripSystemCrossAdjacency
