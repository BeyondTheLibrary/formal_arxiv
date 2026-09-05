import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.SubdivisionDatumRealize
import Workspace.ProofLemmas.DatumDegeneracy
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.CrossTrackNormalize
import Workspace.ProofLemmas.HPrimeDatum
import Workspace.ProofLemmas.CrossTrackEndgame

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.Types.CrossTrackYieldsK33

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*}

private structure Config (H : SimpleGraph W) (P Q R : List W) (i j : ℕ) : Prop where
  hm : 3 ≤ P.length
  hn : 3 ≤ Q.length
  htP : IsTrackList H P
  htQ : IsTrackList H Q
  hiP : i < P.length
  hjQ : j < Q.length
  hPQ : ∀ x ∈ P, x ∉ Q
  hRlen : 2 ≤ R.length
  hRint : ∀ w ∈ trackInterior R, w ∉ P ∧ w ∉ Q
  hR : IsTrackFrom H R (P[i]'hiP) (Q[j]'hjQ)
  e11 : H.Adj (P[0]'(by omega)) (Q[0]'(by omega))
  e1n : H.Adj (P[0]'(by omega)) (Q[Q.length - 1]'(by omega))
  em1 : H.Adj (P[P.length - 1]'(by omega)) (Q[0]'(by omega))
  emn : H.Adj (P[P.length - 1]'(by omega)) (Q[Q.length - 1]'(by omega))
  n11 : s(P[0]'(by omega), Q[0]'(by omega)) ∉ trackEdges R
  n1n : s(P[0]'(by omega), Q[Q.length - 1]'(by omega)) ∉ trackEdges R
  nm1 : s(P[P.length - 1]'(by omega), Q[0]'(by omega)) ∉ trackEdges R
  nmn : s(P[P.length - 1]'(by omega), Q[Q.length - 1]'(by omega)) ∉ trackEdges R

private theorem getElem_rev (l : List W) {k : ℕ} (hk : k < l.length)
    (hk' : l.length - 1 - k < l.reverse.length) :
    l.reverse[l.length - 1 - k]'hk' = l[k]'hk := by
  rw [List.getElem_reverse]
  exact getElem_eq_of_index_eq l (by omega) _ _

private theorem Config.reverseP {H : SimpleGraph W} {P Q R : List W} {i j : ℕ}
    (c : Config H P Q R i j) : Config H P.reverse Q R (P.length - 1 - i) j := by
  have hm := c.hm
  have hn := c.hn
  have hiP := c.hiP
  have hlen : P.reverse.length = P.length := List.length_reverse
  have b1 : (0 : ℕ) < P.reverse.length := by omega
  have b2 : P.length - 1 < P.length := by omega
  have b3 : P.reverse.length - 1 < P.reverse.length := by omega
  have b4 : (0 : ℕ) < P.length := by omega
  have h0 : P.reverse[0]'b1 = P[P.length - 1]'b2 := by
    rw [List.getElem_reverse]
    exact getElem_eq_of_index_eq P (by omega) _ _
  have h1 : P.reverse[P.reverse.length - 1]'b3 = P[0]'b4 := by
    rw [List.getElem_reverse]
    exact getElem_eq_of_index_eq P (by omega) _ _
  refine ⟨by omega, c.hn, isTrackList_reverse c.htP, c.htQ, by omega, c.hjQ, ?_,
    c.hRlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact c.hPQ x (List.mem_reverse.mp hx)
  · intro w hw
    exact ⟨fun hc => (c.hRint w hw).1 (List.mem_reverse.mp hc), (c.hRint w hw).2⟩
  · rw [getElem_rev P hiP]
    exact c.hR
  · rw [h0]; exact c.em1
  · rw [h0]; exact c.emn
  · rw [h1]; exact c.e11
  · rw [h1]; exact c.e1n
  · rw [h0]; exact c.nm1
  · rw [h0]; exact c.nmn
  · rw [h1]; exact c.n11
  · rw [h1]; exact c.n1n

private theorem Config.reverseQ {H : SimpleGraph W} {P Q R : List W} {i j : ℕ}
    (c : Config H P Q R i j) : Config H P Q.reverse R i (Q.length - 1 - j) := by
  have hm := c.hm
  have hn := c.hn
  have hjQ := c.hjQ
  have hlen : Q.reverse.length = Q.length := List.length_reverse
  have b1 : (0 : ℕ) < Q.reverse.length := by omega
  have b2 : Q.length - 1 < Q.length := by omega
  have b3 : Q.reverse.length - 1 < Q.reverse.length := by omega
  have b4 : (0 : ℕ) < Q.length := by omega
  have h0 : Q.reverse[0]'b1 = Q[Q.length - 1]'b2 := by
    rw [List.getElem_reverse]
    exact getElem_eq_of_index_eq Q (by omega) _ _
  have h1 : Q.reverse[Q.reverse.length - 1]'b3 = Q[0]'b4 := by
    rw [List.getElem_reverse]
    exact getElem_eq_of_index_eq Q (by omega) _ _
  refine ⟨c.hm, by omega, c.htP, isTrackList_reverse c.htQ, c.hiP, by omega, ?_,
    c.hRlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hc
    exact c.hPQ x hx (List.mem_reverse.mp hc)
  · intro w hw
    exact ⟨(c.hRint w hw).1, fun hc => (c.hRint w hw).2 (List.mem_reverse.mp hc)⟩
  · rw [getElem_rev Q hjQ]
    exact c.hR
  · rw [h0]; exact c.e1n
  · rw [h1]; exact c.e11
  · rw [h0]; exact c.emn
  · rw [h1]; exact c.em1
  · rw [h0]; exact c.n1n
  · rw [h1]; exact c.n11
  · rw [h0]; exact c.nmn
  · rw [h1]; exact c.nm1

private theorem four_cycle_cases {p : Fin 4 → Fin 4 → Prop} (α β γ δ : Fin 4)
    (d1 : α ≠ β) (d2 : α ≠ γ) (d3 : α ≠ δ) (d4 : β ≠ γ) (d5 : β ≠ δ) (d6 : γ ≠ δ)
    (s1 : p α β) (s2 : p β γ) (s3 : p γ δ) (s4 : p δ α)
    (t1 : p β α) (t2 : p γ β) (t3 : p δ γ) (t4 : p α δ) :
    (p 0 1 ∧ p 1 2 ∧ p 2 3 ∧ p 0 3) ∨
    (p 0 1 ∧ p 1 3 ∧ p 2 3 ∧ p 0 2) ∨
    (p 0 2 ∧ p 1 2 ∧ p 1 3 ∧ p 0 3) := by
  have hf : ∀ x : Fin 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hf α with rfl | rfl | rfl | rfl <;> rcases hf β with rfl | rfl | rfl | rfl <;>
    rcases hf γ with rfl | rfl | rfl | rfl <;> rcases hf δ with rfl | rfl | rfl | rfl <;>
    simp_all

private theorem core [Finite W] {H : SimpleGraph W} (hbip : H.IsBipartite)
    (hdegall : ∀ S : H.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe →
      DegenerateK4Appearance S.coe)
    {P Q R : List W} {i j : ℕ} (c : Config H P Q R i j)
    (hi : i ≤ P.length - 2) (hj : j ≤ Q.length - 2) :
    R.length = 2 ∧ i = P.length - 2 ∧ j = Q.length - 2 := by
  classical
  have hm := c.hm
  have hn := c.hn
  have hRlen := c.hRlen
  obtain ⟨ι, T, hd, hι0, hι1, hι2, hι3, L01, L02, L03, L12, L13, L23⟩ :=
    Workspace.ProofLemmas.HPrimeDatum.exists_hprime_datum c.htP c.htQ c.hm c.hn hi hj c.hPQ
      c.hR c.hRlen c.hRint c.e1n c.em1 c.emn
  have hS := Workspace.ProofLemmas.SubdivisionDatumRealize.isSubdivision_dsubgraph hd
  obtain ⟨α, β, γ, δ, d1, d2, d3, d4, d5, d6, s1, s2, s3, s4⟩ :=
    Workspace.ProofLemmas.DatumDegeneracy.exists_degenerate_cycle_of_datum hd (hdegall _ hS)
  have hsym : ∀ u v : Fin 4, (T u v).length = 2 → (T v u).length = 2 := by
    intro u v h
    by_cases huv : u = v
    · subst huv; exact h
    · rw [hd.2.2.2.1 u v huv, List.length_reverse]; exact h
  have htri := four_cycle_cases (p := fun u v => (T u v).length = 2) α β γ δ d1 d2 d3 d4 d5 d6
    s1 s2 s3 s4 (hsym _ _ s1) (hsym _ _ s2) (hsym _ _ s3) (hsym _ _ s4)
  simp only at htri
  have hnot : ¬ (R.length = 2 ∧ i = 0 ∧ j = 0) := by
    rintro ⟨ht2, hi0, hj0⟩
    apply c.n11
    have hR0 : R[0]'(by omega) = P[i]'c.hiP := track_head c.hR (by omega)
    have hR1 : R[1]'(by omega) = Q[j]'c.hjQ := track_last c.hR ht2
    have hPi : P[i]'c.hiP = P[0]'(by omega) := getElem_eq_of_index_eq P hi0 _ _
    have hQj : Q[j]'c.hjQ = Q[0]'(by omega) := getElem_eq_of_index_eq Q hj0 _ _
    exact ⟨0, by omega, by rw [hR0, hR1, hPi, hQj]⟩
  rcases htri with ⟨c01, c12, -, c03⟩ | ⟨c01, c13, -, c02⟩ | ⟨c02, c12, c13, c03⟩
  · exact Workspace.ProofLemmas.CrossTrackEndgame.cross_track_indices hm hn hi hj hRlen hnot
      (Or.inl (by omega))
  · exact Workspace.ProofLemmas.CrossTrackEndgame.cross_track_indices hm hn hi hj hRlen hnot
      (Or.inr (by omega))
  · exfalso
    have htr12 : IsTrackFrom H (T 1 2) (ι 1) (ι 2) := hd.2.1 1 2 (by decide)
    have htr13 : IsTrackFrom H (T 1 3) (ι 1) (ι 3) := hd.2.1 1 3 (by decide)
    have a12 : H.Adj (ι 1) (ι 2) := by
      have h := htr12.1.2.2 0 (by omega)
      rw [getElem_eq_of_index_eq (T 1 2) (show (0 : ℕ) + 1 = 1 from rfl) (by omega) (by omega),
        track_head htr12 (by omega), track_last htr12 c12] at h
      exact h
    have a13 : H.Adj (ι 1) (ι 3) := by
      have h := htr13.1.2.2 0 (by omega)
      rw [getElem_eq_of_index_eq (T 1 3) (show (0 : ℕ) + 1 = 1 from rfl) (by omega) (by omega),
        track_head htr13 (by omega), track_last htr13 c13] at h
      exact h
    have a23 : H.Adj (ι 2) (ι 3) := by rw [hι2, hι3]; exact c.emn
    exact Workspace.ProofLemmas.CrossTrackEndgame.bipartite_no_triangle hbip a23 a12.symm a13.symm

private theorem k33_of_config [Finite W] {H : SimpleGraph W} (hbip : H.IsBipartite)
    (hdegall : ∀ S : H.Subgraph, IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe →
      DegenerateK4Appearance S.coe)
    {P Q R : List W} {i j : ℕ} (c : Config H P Q R i j)
    (hi : i ≤ P.length - 2) (hj : j ≤ Q.length - 2) :
    ∃ J : H.Subgraph, Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  have hm := c.hm
  have hn := c.hn
  have hlenP : P.reverse.length = P.length := List.length_reverse
  have hlenQ : Q.reverse.length = Q.length := List.length_reverse
  obtain ⟨ht, hieq, hjeq⟩ := core hbip hdegall c hi hj
  obtain ⟨-, hieq2, -⟩ := core hbip hdegall c.reverseP (by omega) hj
  have hm3 : P.length = 3 := by omega
  obtain ⟨-, -, hjeq2⟩ := core hbip hdegall c.reverseQ hi (by omega)
  have hn3 : Q.length = 3 := by omega
  have hi1 : i = 1 := by omega
  have hj1 : j = 1 := by omega
  have hadj : H.Adj (P[1]'(by omega)) (Q[1]'(by omega)) := by
    have h := c.hR.1.2.2 0 (show 0 + 1 < R.length by omega)
    rw [getElem_eq_of_index_eq R (show (0 : ℕ) + 1 = 1 from rfl) (by omega) (by omega),
      track_head c.hR (by omega), track_last c.hR ht,
      getElem_eq_of_index_eq P hi1 c.hiP (show 1 < P.length by omega),
      getElem_eq_of_index_eq Q hj1 c.hjQ (show 1 < Q.length by omega)] at h
    exact h
  have hp2 : P[P.length - 1]'(by omega) = P[2]'(by omega) :=
    getElem_eq_of_index_eq P (by omega) _ _
  have hq2 : Q[Q.length - 1]'(by omega) = Q[2]'(by omega) :=
    getElem_eq_of_index_eq Q (by omega) _ _
  have E11 := c.e11
  have E1n := c.e1n
  have Em1 := c.em1
  have Emn := c.emn
  rw [hq2] at E1n
  rw [hp2] at Em1
  rw [hp2, hq2] at Emn
  exact Workspace.ProofLemmas.CrossTrackEndgame.exists_k33_of_len3 c.htP c.htQ hm3 hn3 c.hPQ
    E11 E1n Em1 Emn hadj

theorem crossTrackYieldsK33
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hbip : H.IsBipartite)
    (P Q : List W) (hPlen : 3 ≤ P.length) (hQlen : 3 ≤ Q.length)
    (hP : IsTrackList H P) (hQ : IsTrackList H Q)
    (hdisj : ∀ x ∈ P, x ∉ Q)
    (hPodd : Odd P.length) (hQodd : Odd Q.length)
    (e11 : H.Adj P[0] Q[0])
    (e1n : H.Adj P[0] Q[Q.length - 1])
    (em1 : H.Adj P[P.length - 1] Q[0])
    (emn : H.Adj P[P.length - 1] Q[Q.length - 1])
    (hdeg : ∀ D : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) D.coe → DegenerateK4Appearance D.coe)
    (hcross : ∃ (a b : W) (R : List W),
      a ∈ P ∧ b ∈ Q ∧ IsTrackFrom H R a b ∧
      s(P[0], Q[0]) ∉ trackEdges R ∧
      s(P[0], Q[Q.length - 1]) ∉ trackEdges R ∧
      s(P[P.length - 1], Q[0]) ∉ trackEdges R ∧
      s(P[P.length - 1], Q[Q.length - 1]) ∉ trackEdges R) :
    ∃ J : H.Subgraph,
      Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  obtain ⟨a, b, R₀, haP, hbQ, hR₀, hnn1, hnn2, hnn3, hnn4⟩ := hcross
  obtain ⟨R, i, j, hiP, hjQ, hR, hRlen, hRint, hsub⟩ :=
    Workspace.ProofLemmas.CrossTrackNormalize.exists_normalized_cross_track hR₀ haP hbQ hdisj
  have c : Config H P Q R i j :=
    { hm := hPlen, hn := hQlen, htP := hP, htQ := hQ, hiP := hiP, hjQ := hjQ, hPQ := hdisj,
      hRlen := hRlen, hRint := hRint, hR := hR,
      e11 := e11, e1n := e1n, em1 := em1, emn := emn,
      n11 := fun h => hnn1 (hsub h), n1n := fun h => hnn2 (hsub h),
      nm1 := fun h => hnn3 (hsub h), nmn := fun h => hnn4 (hsub h) }
  have hlenP : P.reverse.length = P.length := List.length_reverse
  have hlenQ : Q.reverse.length = Q.length := List.length_reverse
  by_cases hi : i ≤ P.length - 2
  · by_cases hj : j ≤ Q.length - 2
    · exact k33_of_config hbip hdeg c hi hj
    · exact k33_of_config hbip hdeg c.reverseQ hi (by omega)
  · by_cases hj : j ≤ Q.length - 2
    · exact k33_of_config hbip hdeg c.reverseP (by omega) hj
    · exact k33_of_config hbip hdeg c.reverseP.reverseQ (by omega) (by omega)

end Workspace.Types.CrossTrackYieldsK33
