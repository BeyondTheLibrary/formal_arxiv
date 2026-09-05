import Workspace.Types.Core
import Workspace.Types.Tracks

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT

private def endpointCleanSlice {V : Type*} (P : List V) (i j : ℕ) : List V :=
  (P.drop i).take (j - i + 1)

private theorem endpointCleanSlice_length {V : Type*} (P : List V) {i j : ℕ}
    (hj : j < P.length) (hij : i ≤ j) :
    (endpointCleanSlice P i j).length = j - i + 1 := by
  simp only [endpointCleanSlice, List.length_take, List.length_drop]
  omega

private theorem endpointCleanSlice_getElem {V : Type*} (P : List V) {i j k : ℕ}
    (hk : k < (endpointCleanSlice P i j).length) (hik : i + k < P.length) :
    (endpointCleanSlice P i j)[k]'hk = P[i + k]'hik := by
  simp only [endpointCleanSlice, List.getElem_take, List.getElem_drop]

private theorem endpointCleanSlice_sublist {V : Type*} (P : List V) (i j : ℕ) :
    List.Sublist (endpointCleanSlice P i j) P :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)

private theorem endpointCleanSlice_track {V : Type*} {H : SimpleGraph V} {P : List V}
    (hP : IsTrackList H P) {i j : ℕ} (hj : j < P.length) (hij : i ≤ j) :
    IsTrackFrom H (endpointCleanSlice P i j) (P[i]'(by omega)) (P[j]'hj) := by
  have hlen := endpointCleanSlice_length P hj hij
  have htrack : IsTrackList H (endpointCleanSlice P i j) := by
    refine ⟨?_, List.Nodup.sublist (endpointCleanSlice_sublist P i j) hP.2.1, ?_⟩
    · intro hc
      rw [hc] at hlen
      simp at hlen
    · intro k hk
      have hkb : k + 1 < j - i + 1 := by rw [hlen] at hk; exact hk
      have h1 : i + k < P.length := by omega
      have h2 : i + (k + 1) < P.length := by omega
      rw [endpointCleanSlice_getElem P (by omega) h1,
        endpointCleanSlice_getElem P hk h2]
      exact hP.2.2 (i + k) (by omega)
  refine ⟨htrack, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    exact congrArg some (endpointCleanSlice_getElem P (by omega) (by omega))
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    refine congrArg some ?_
    rw [endpointCleanSlice_getElem P (by omega)
      (show i + ((endpointCleanSlice P i j).length - 1) < P.length by omega)]
    congr 1
    omega

private theorem endpointCleanSlice_mem_iff {V : Type*} {P : List V} {i j : ℕ}
    (hj : j < P.length) (hij : i ≤ j) {x : V} :
    x ∈ endpointCleanSlice P i j ↔
      ∃ (k : ℕ) (hk : k < P.length), i ≤ k ∧ k ≤ j ∧ P[k]'hk = x := by
  have hlen := endpointCleanSlice_length P hj hij
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨i + k, by omega, by omega, by omega,
      (endpointCleanSlice_getElem P hk (by omega)).symm⟩
  · rintro ⟨k, hk, hik, hkj, rfl⟩
    refine List.mem_iff_getElem.mpr ⟨k - i, by omega, ?_⟩
    rw [endpointCleanSlice_getElem P (by omega)
      (show i + (k - i) < P.length by omega)]
    congr 1
    omega

private theorem endpointClean_indices {V : Type*} {P : List V} {A B : Set V} :
    ∀ (d i₀ j₀ : ℕ) (_hd : j₀ - i₀ ≤ d) (hj₀ : j₀ < P.length) (hlt : i₀ < j₀)
      (_hA : P[i₀]'(by omega) ∈ A) (_hB : P[j₀]'hj₀ ∈ B),
      ∃ i j, i₀ ≤ i ∧ i < j ∧ j ≤ j₀ ∧ ∃ (hi : i < P.length) (hj : j < P.length),
        P[i]'hi ∈ A ∧ P[j]'hj ∈ B ∧
        ∀ (k : ℕ) (hk : k < P.length), i < k → k < j →
          P[k]'hk ∉ A ∧ P[k]'hk ∉ B := by
  classical
  intro d
  induction d with
  | zero =>
      intro i₀ j₀ hd hj₀ hlt _ _
      exact absurd hlt (by omega)
  | succ n ih =>
      intro i₀ j₀ hd hj₀ hlt hA hB
      by_cases hbad : ∃ (k : ℕ) (hk : k < P.length),
          i₀ < k ∧ k < j₀ ∧ (P[k]'hk ∈ A ∨ P[k]'hk ∈ B)
      · obtain ⟨k, hk, hik, hkj, hor⟩ := hbad
        rcases hor with hkA | hkB
        · obtain ⟨i, j, h1, h2, h3, hi, hj, h4, h5, h6⟩ :=
            ih k j₀ (by omega) hj₀ (by omega) hkA hB
          exact ⟨i, j, by omega, h2, h3, hi, hj, h4, h5, h6⟩
        · obtain ⟨i, j, h1, h2, h3, hi, hj, h4, h5, h6⟩ :=
            ih i₀ k (by omega) hk hik hA hkB
          exact ⟨i, j, h1, h2, by omega, hi, hj, h4, h5, h6⟩
      · refine ⟨i₀, j₀, le_rfl, hlt, le_rfl, by omega, hj₀, hA, hB, ?_⟩
        intro k hk hik hkj
        exact ⟨fun hc => hbad ⟨k, hk, hik, hkj, Or.inl hc⟩,
          fun hc => hbad ⟨k, hk, hik, hkj, Or.inr hc⟩⟩

theorem ConnectedSetHasEndpointCleanTrack
    {V : Type*} (H : SimpleGraph V) (S A B : Set V)
    (hS : ConnectedSet H S)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAS : A ⊆ S) (hBS : B ⊆ S) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ P : List V,
      IsTrackFrom H P a b ∧
      (∀ v ∈ P, v ∈ S) ∧
      (∀ v ∈ P, v ∈ A → v = a) ∧
      (∀ v ∈ P, v ∈ B → v = b) := by
  classical
  by_cases hAB : (A ∩ B).Nonempty
  · obtain ⟨x, hxA, hxB⟩ := hAB
    refine ⟨x, hxA, x, hxB, [x], ?_, ?_, ?_, ?_⟩
    · exact ⟨⟨by simp, by simp, by simp⟩, by simp, by simp⟩
    · intro v hv
      have hvx : v = x := by simpa using hv
      simpa [hvx] using hAS hxA
    · intro v hv _
      simpa using hv
    · intro v hv _
      simpa using hv
  · obtain ⟨a₀, ha₀⟩ := hA
    obtain ⟨b₀, hb₀⟩ := hB
    have hab : a₀ ≠ b₀ := by
      intro hab
      apply hAB
      exact ⟨a₀, ha₀, hab ▸ hb₀⟩
    obtain ⟨w, hw⟩ := hS.exists_isPath ⟨a₀, hAS ha₀⟩ ⟨b₀, hBS hb₀⟩
    let f : H.induce S →g H :=
      { toFun := fun z => z.1
        map_rel' := fun h => h }
    let p : H.Walk a₀ b₀ := w.map f
    have hp : p.IsPath := by
      exact (w.map_isPath_iff_of_injective Subtype.val_injective).2 hw
    let P₀ : List V := p.support
    have hP₀ : IsTrackFrom H P₀ a₀ b₀ := by
      refine ⟨⟨p.support_ne_nil, hp.support_nodup, ?_⟩, ?_, ?_⟩
      · exact List.isChain_iff_getElem.mp p.isChain_adj_support
      · rw [List.head?_eq_some_head p.support_ne_nil]
        exact congrArg some p.head_support
      · rw [List.getLast?_eq_some_getLast p.support_ne_nil]
        exact congrArg some p.getLast_support
    have hP₀S : ∀ v ∈ P₀, v ∈ S := by
      intro v hv
      change v ∈ (w.map f).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      exact z.2
    have hlenpos : 0 < P₀.length := List.length_pos_of_ne_nil hP₀.1.1
    have hlen2 : 2 ≤ P₀.length := by
      by_contra h
      have hone : P₀.length = 1 := by omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hone
      have hhead := hP₀.2.1
      have hlast := hP₀.2.2
      rw [hx] at hhead hlast
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
      exact hab (hhead.symm.trans hlast)
    have hfirst : P₀[0]'hlenpos = a₀ := by
      have h := hP₀.2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlenpos] at h
      exact Option.some_inj.mp h
    have hlast : P₀[P₀.length - 1]'(by omega) = b₀ := by
      have h := hP₀.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
      exact Option.some_inj.mp h
    obtain ⟨i, j, -, hij, -, hi, hj, hiA, hjB, hclean⟩ :=
      endpointClean_indices (P := P₀) (A := A) (B := B) (P₀.length - 1)
        0 (P₀.length - 1) le_rfl (by omega) (by omega) (hfirst ▸ ha₀) (hlast ▸ hb₀)
    let a : V := P₀[i]'hi
    let b : V := P₀[j]'hj
    let P : List V := endpointCleanSlice P₀ i j
    have hPtrack : IsTrackFrom H P a b :=
      endpointCleanSlice_track hP₀.1 hj (by omega)
    refine ⟨a, hiA, b, hjB, P, hPtrack, ?_, ?_, ?_⟩
    · intro v hv
      exact hP₀S v ((endpointCleanSlice_sublist P₀ i j).subset hv)
    · intro v hv hvA
      obtain ⟨k, hk, hik, hkj, hkv⟩ :=
        (endpointCleanSlice_mem_iff hj (by omega)).mp hv
      have hki : k = i := by
        by_contra hne
        have hik' : i < k := by omega
        by_cases hkj' : k < j
        · exact (hclean k hk hik' hkj').1 (hkv ▸ hvA)
        · have hkj_eq : k = j := by omega
          apply hAB
          exact ⟨P₀[j]'hj, hkj_eq ▸ hkv ▸ hvA, hjB⟩
      exact hkv.symm.trans (by simp [a, hki])
    · intro v hv hvB
      obtain ⟨k, hk, hik, hkj, hkv⟩ :=
        (endpointCleanSlice_mem_iff hj (by omega)).mp hv
      have hkj_eq : k = j := by
        by_contra hne
        have hkj' : k < j := by omega
        by_cases hik' : i < k
        · exact (hclean k hk hik' hkj').2 (hkv ▸ hvB)
        · have hik_eq : k = i := by omega
          apply hAB
          exact ⟨P₀[i]'hi, hiA, hik_eq ▸ hkv ▸ hvB⟩
      exact hkv.symm.trans (by simp [b, hkj_eq])

end Workspace.ProofLemmas
