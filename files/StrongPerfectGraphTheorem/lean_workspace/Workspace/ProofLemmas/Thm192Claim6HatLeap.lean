import Workspace.ProofLemmas.Thm192Claim6Basics
import Workspace.Statements.S02.Thm_2_10

/-! The hat-or-leap step in claim (6) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim6HatLeap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem rotate_index_eq {H : List V} (hnd : H.Nodup)
    {i j : ℕ} (hj : j < H.length) {w : V}
    (hhead : (H.rotate i).head? = some w) (hjw : H[j]'hj = w) :
    H.rotate i = H.rotate j := by
  have hpos : 0 < H.length := by omega
  have hmod : i % H.length < H.length := Nat.mod_lt _ hpos
  have hg : (H.rotate i).head? = H[(0 + i) % H.length]? := by
    rw [List.head?_eq_getElem?, List.getElem?_rotate hpos]
  rw [hg, Nat.zero_add, List.getElem?_eq_getElem hmod] at hhead
  have hij : i % H.length = j :=
    hnd.getElem_inj_iff.mp ((Option.some.inj hhead).trans hjw.symm)
  rw [← List.rotate_mod H i, hij]

/-- At the cut edge `zx₀`, one vertex of a leap has no neighbour among `p₁,…,pₙ`.
This reads the six edges in the definition of a leap, as in the first part of (6). -/
theorem leap_misses_interior {G : SimpleGraph V} {P : List V} {z x₀ x₁ a b : V}
    (hP : IsPathFrom G P x₀ x₁) (hlen : 3 ≤ P.length)
    (hb : b ∉ z :: P)
    (hl : IsLeapForHole G (z :: P) z x₀ a b ∨
      IsLeapForHole G (z :: P) x₀ z a b) :
    ∀ w ∈ SPGT.interior P, ¬ G.Adj b w := by
  have hp0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hx₀P := PathBasics.head_mem hP.2.1
  have hbz : b ≠ z := fun h => hb (by simp [h])
  have hbx₀ : b ≠ x₀ := fun h => hb (by simp [h, hx₀P])
  rcases hl with hl | hl
  · obtain ⟨hC, i, hhd, hlast, hpath, hpathlen, hab, hnab, hAa, hBb⟩ := hl
    have hrot : (z :: P).rotate i = P ++ [z] := by
      rw [rotate_index_eq hC.2.1 (j := 1) (by simp; omega) hhd (by simpa using hp0)]
      simpa using (List.rotate_cons_succ z P 0)
    rw [hrot] at hBb
    intro w hw hadj
    obtain ⟨k, hk, hk1, hk2, hkw⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hw
    have hedge : (G.deleteEdges {s(z, x₀)}).Adj b (P[k]'hk) := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨by rwa [hkw], ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨he, _⟩ | ⟨he, _⟩)
      · exact hbz he
      · exact hbx₀ he
    have he := (hBb k (by simp; omega)).mp (by
      rw [List.getElem_append_left hk]
      exact hedge)
    simp only [List.length_append, List.length_cons, List.length_nil] at he
    omega
  · obtain ⟨hC, i, hhd, hlast, _⟩ := hl
    have hrot := rotate_index_eq hC.2.1 (j := 0) (by simp) hhd (by simp)
    rw [hrot, List.rotate_zero] at hlast
    have hn : 0 < (z :: P).length := by simp
    have hlast' := PathBasics.getElem_last_of_getLast? hlast hn
    have hhead' : (z :: P)[1]'(by simp; omega) = x₀ := by simpa using hp0
    have he := hC.2.1.getElem_inj_iff.mp (hlast'.trans hhead'.symm)
    simp only [List.length_cons] at he
    omega

/-- PAPER (claim (6)): "Therefore `z,x₀` are the only `Y ∪ {x₂}`-complete
vertices in `C`, and by 2.10 there is a hat or a leap."
If every member of the hub has an interior neighbour, both outcomes are excluded. -/
theorem hat_leap_absurd {G : SimpleGraph V} (hG : Berge G) {S : Set V}
    (hS : AnticonnectedSet G S) {P : List V} {z x₀ x₁ : V}
    (hP : IsPathFrom G P x₀ x₁) (hC : IsHoleList G (z :: P)) (hlen : 5 ≤ P.length)
    (hdisj : ∀ w ∈ z :: P, w ∉ S) (hzx : G.Adj z x₀)
    (hzS : VertexComplete G z S) (hxS : VertexComplete G x₀ S)
    (honly : ∀ w ∈ z :: P, VertexComplete G w S → w = z ∨ w = x₀)
    (hnb : ∀ s ∈ S, ∃ w ∈ SPGT.interior P, G.Adj s w) : False := by
  have hxP := PathBasics.head_mem hP.2.1
  rcases Workspace.Statements.S02.SPGT.thm_2_10 G hG S hS (z :: P) hC hdisj
      (by simp only [holeLength, List.length_cons]; omega) z x₀ (by simp)
      (by simp [hxP]) hzx hzS hxS honly with ⟨s, hs, hh⟩ | ⟨a, ha, b, hb, hl⟩
  · obtain ⟨w, hw, hsw⟩ := hnb s hs
    have hwP := PathBasics.interior_subset hw
    have hwz : w ≠ z := fun he => (List.nodup_cons.mp hC.2.1).1 (he ▸ hwP)
    have hwx := ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hw).2.1
    exact hh.2.2.2.2.2.2 w (by simp [hwP]) hwz hwx hsw
  · obtain ⟨w, hw, hbw⟩ := hnb b hb
    exact leap_misses_interior hP (by omega) (fun h => hdisj b h hb) hl w hw hbw

end Workspace.ProofLemmas.Thm192Claim6HatLeap
