import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.K33ComponentConstruction
import Workspace.ProofLemmas.TrackThroughComponent
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.SubdivisionDatumRealize
import Workspace.ProofLemmas.DatumDegeneracy
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.TrackSlice

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace Workspace.Types.K33ComponentYieldsNondegenerate

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.SubdivisionDatumRealize

private theorem twoTrack {W : Type*} {H : SimpleGraph W} {x y : W}
    (hxy : x ≠ y) (hadj : H.Adj x y) : IsTrackFrom H [x, y] x y := by
  refine ⟨⟨by simp, by simp [hxy], ?_⟩, rfl, rfl⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  have : i = 0 := by omega
  subst i
  simpa using hadj

private theorem threeTrack {W : Type*} {H : SimpleGraph W} {x y z : W}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy' : H.Adj x y) (hyz' : H.Adj y z) : IsTrackFrom H [x, y, z] x z := by
  refine ⟨⟨by simp, by simp [hxy, hxz, hyz], ?_⟩, rfl, rfl⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  have hc : i = 0 ∨ i = 1 := by omega
  rcases hc with rfl | rfl
  · simpa using hxy'
  · simpa using hyz'

private theorem sameSide
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (S₀ : Set W) (a b : Fin 3 → W)
    (haS : ∀ i, a i ∈ S₀) (hbS : ∀ i, b i ∈ S₀)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (habne : ∀ i j, a i ≠ b j)
    (hadj : ∀ i j, H.Adj (a i) (b j))
    (P : List W) (hP : IsTrackFrom H P (a 0) (a 1))
    (hPlen : 2 ≤ trackLength P)
    (hPint : ∀ w ∈ trackInterior P, w ∉ S₀) :
    ∃ S : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe := by
  classical
  let ι : Fin 4 → W := ![a 0, a 1, a 2, b 1]
  let T : Fin 4 → Fin 4 → List W :=
    ![![[], P, [a 0, b 2, a 2], [a 0, b 1]],
      ![P.reverse, [], [a 1, b 0, a 2], [a 1, b 1]],
      ![[a 2, b 2, a 0], [a 2, b 0, a 1], [], [a 2, b 1]],
      ![[b 1, a 0], [b 1, a 1], [b 1, a 2], []]]
  have hP0 : 0 < P.length := by
    simp only [trackLength] at hPlen
    omega
  have hPhead : P[0]'hP0 = a 0 :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hP hP0
  have hPlast : P[P.length - 1]'(by omega) = a 1 :=
    Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hP hP0
  have hPnamed : ∀ i, a i ∈ P → i = 0 ∨ i = 1 := by
    intro i hi
    have hnint : a i ∉ trackInterior P := fun h => hPint _ h (haS i)
    rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior hi hnint hP0 with h | h
    · rw [hPhead] at h
      exact Or.inl (ha h)
    · rw [hPlast] at h
      exact Or.inr (ha h)
  have ha2P : a 2 ∉ P := fun h => by
    rcases hPnamed 2 h with h | h <;> omega
  have hbP : ∀ i, b i ∉ P := by
    intro i h
    have hnint : b i ∉ trackInterior P := fun hx => hPint _ hx (hbS i)
    rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior h hnint hP0 with e | e
    · exact habne 0 i (hPhead.symm.trans e.symm)
    · exact habne 1 i (hPlast.symm.trans e.symm)
  have d01 : a 0 ≠ a 1 := fun e => (show (0 : Fin 3) ≠ 1 by decide) (ha e)
  have d02 : a 0 ≠ a 2 := fun e => (show (0 : Fin 3) ≠ 2 by decide) (ha e)
  have d12 : a 1 ≠ a 2 := fun e => (show (1 : Fin 3) ≠ 2 by decide) (ha e)
  have db01 : b 0 ≠ b 1 := fun e => (show (0 : Fin 3) ≠ 1 by decide) (hb e)
  have db02 : b 0 ≠ b 2 := fun e => (show (0 : Fin 3) ≠ 2 by decide) (hb e)
  have db12 : b 1 ≠ b 2 := fun e => (show (1 : Fin 3) ≠ 2 by decide) (hb e)
  have e02 : IsTrackFrom H [a 0, b 2, a 2] (a 0) (a 2) :=
    threeTrack (habne 0 2) d02 (habne 2 2).symm (hadj 0 2) (hadj 2 2).symm
  have e03 : IsTrackFrom H [a 0, b 1] (a 0) (b 1) :=
    twoTrack (habne 0 1) (hadj 0 1)
  have e12 : IsTrackFrom H [a 1, b 0, a 2] (a 1) (a 2) :=
    threeTrack (habne 1 0) d12 (habne 2 0).symm (hadj 1 0) (hadj 2 0).symm
  have e13 : IsTrackFrom H [a 1, b 1] (a 1) (b 1) :=
    twoTrack (habne 1 1) (hadj 1 1)
  have e23 : IsTrackFrom H [a 2, b 1] (a 2) (b 1) :=
    twoTrack (habne 2 1) (hadj 2 1)
  have hιinj : Function.Injective ι := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ι] at hij ⊢
    all_goals first
      | exact (d01 hij).elim | exact (d01 hij.symm).elim
      | exact (d02 hij).elim | exact (d02 hij.symm).elim
      | exact (d12 hij).elim | exact (d12 hij.symm).elim
      | exact (habne 0 1 hij).elim | exact (habne 0 1 hij.symm).elim
      | exact (habne 1 1 hij).elim | exact (habne 1 1 hij.symm).elim
      | exact (habne 2 1 hij).elim | exact (habne 2 1 hij.symm).elim
  have htrack : ∀ u v : Fin 4, u ≠ v → IsTrackFrom H (T u v) (ι u) (ι v) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp [T, ι] at huv ⊢
    all_goals first
      | exact (huv rfl).elim
      | exact hP
      | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hP
      | exact e02 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e02
      | exact e03 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e03
      | exact e12 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e12
      | exact e13 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e13
      | exact e23 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e23
  have hlen : ∀ u v : Fin 4, u ≠ v → 1 ≤ trackLength (T u v) := by
    intro u v huv
    simp only [trackLength] at hPlen
    fin_cases u <;> fin_cases v <;> simp [T, trackLength] at huv ⊢ <;> omega
  have hrev : ∀ u v : Fin 4, u ≠ v → T v u = (T u v).reverse := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at huv ⊢ <;> simp
  have hnamedIntP : ∀ x ∈ S₀, x ∉ trackInterior P := fun x hx h => hPint x h hx
  have ha0I := hnamedIntP (a 0) (haS 0)
  have ha1I := hnamedIntP (a 1) (haS 1)
  have ha2I := hnamedIntP (a 2) (haS 2)
  have hb0I := hnamedIntP (b 0) (hbS 0)
  have hb1I := hnamedIntP (b 1) (hbS 1)
  have hb2I := hnamedIntP (b 2) (hbS 2)
  have hIntNeA : ∀ w ∈ trackInterior P, ∀ i, w ≠ a i := by
    intro w hw i e
    apply hPint w hw
    rw [e]
    exact haS i
  have hIntNeB : ∀ w ∈ trackInterior P, ∀ i, w ≠ b i := by
    intro w hw i e
    apply hPint w hw
    rw [e]
    exact hbS i
  have hswapMem : ∀ u v : Fin 4, u ≠ v → ∀ x, x ∈ T v u ↔ x ∈ T u v := by
    intro u v huv x
    rw [hrev u v huv, List.mem_reverse]
  have hswapInt : ∀ u v : Fin 4, u ≠ v → ∀ x,
      x ∈ trackInterior (T v u) ↔ x ∈ trackInterior (T u v) := by
    intro u v huv x
    rw [hrev u v huv, Workspace.ProofLemmas.TrackSlice.trackInterior_reverse, List.mem_reverse]
  have hdisj0 : ∀ u v u' v' : Fin 4, u < v → u' < v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v' := by
    intro u v u' v' huv huv' hs w hw hmem
    fin_cases u <;> fin_cases v <;>
      simp [T, trackInterior] at huv hw
    all_goals try omega
    all_goals fin_cases u' <;> fin_cases v' <;>
      simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        List.mem_cons, List.mem_singleton] at huv' hmem
    all_goals simp at huv'
    all_goals try omega
    all_goals try exact hs rfl
    all_goals simp_all [trackInterior, d01, d02, d12, db01, db02, db12, habne,
      ha2P, hbP, hIntNeA, hIntNeB, Ne.symm d01, Ne.symm d02, Ne.symm d12,
      Ne.symm db01, Ne.symm db02, Ne.symm db12, fun i j => Ne.symm (habne i j)]
  have hdisj : ∀ u v u' v' : Fin 4, u ≠ v → u' ≠ v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v' := by
    intro u v u' v' huv huv' hs w hw hmem
    rcases lt_or_gt_of_ne huv with h | h <;> rcases lt_or_gt_of_ne huv' with h' | h'
    · exact hdisj0 u v u' v' h h' hs w hw hmem
    · exact hdisj0 u v v' u' h h' (by simpa [Sym2.eq_swap] using hs) w hw
        ((hswapMem v' u' h'.ne w).mp hmem)
    · exact hdisj0 v u u' v' h h' (by simpa [Sym2.eq_swap] using hs) w
        ((hswapInt v u h.ne w).mp hw) hmem
    · exact hdisj0 v u v' u' h h' (by simpa [Sym2.eq_swap] using hs) w
        ((hswapInt v u h.ne w).mp hw) ((hswapMem v' u' h'.ne w).mp hmem)
  have hnew0 : ∀ u v : Fin 4, u < v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι := by
    intro u v huv w hw hr
    obtain ⟨k, rfl⟩ := hr
    fin_cases u <;> fin_cases v <;> simp [T, trackInterior] at huv hw
    all_goals try omega
    all_goals first
      | exact hPint _ hw (by fin_cases k <;> simp [ι, haS, hbS])
      | fin_cases k <;>
          simp_all [ι, d01, d02, d12, db01, db02, db12, habne,
            Ne.symm d01, Ne.symm d02, Ne.symm d12, Ne.symm db01,
            Ne.symm db02, Ne.symm db12, fun i j => Ne.symm (habne i j)]
  have hnew : ∀ u v : Fin 4, u ≠ v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι := by
    intro u v huv w hw hr
    rcases lt_or_gt_of_ne huv with h | h
    · exact hnew0 u v h w hw hr
    · exact hnew0 v u h w ((hswapInt v u h.ne w).mp hw) hr
  have hd : IsK4Datum H ι T := ⟨hιinj, htrack, hlen, hrev, hdisj, hnew⟩
  let S := dsubgraph H ι T hd
  refine ⟨S, isSubdivision_dsubgraph hd, ?_⟩
  rw [Workspace.ProofLemmas.ClassLemmas.nondegenerateAppearance_K4_iff]
  apply Workspace.ProofLemmas.DatumDegeneracy.nondegenerate_of_two_long hd
  · simp only [trackLength] at hPlen
    simpa [T] using (show 3 ≤ P.length by omega)
  · simp [T]

private theorem oppositeSide
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (S₀ : Set W) (a b : Fin 3 → W)
    (haS : ∀ i, a i ∈ S₀) (hbS : ∀ i, b i ∈ S₀)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (habne : ∀ i j, a i ≠ b j)
    (hadj : ∀ i j, H.Adj (a i) (b j))
    (P : List W) (hP : IsTrackFrom H P (a 0) (b 0))
    (hPlen : 2 ≤ trackLength P)
    (hPint : ∀ w ∈ trackInterior P, w ∉ S₀) :
    ∃ S : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe := by
  classical
  let ι : Fin 4 → W := ![a 0, b 0, a 2, b 2]
  let T : Fin 4 → Fin 4 → List W :=
    ![![[], P, [a 0, b 1, a 2], [a 0, b 2]],
      ![P.reverse, [], [b 0, a 2], [b 0, a 1, b 2]],
      ![[a 2, b 1, a 0], [a 2, b 0], [], [a 2, b 2]],
      ![[b 2, a 0], [b 2, a 1, b 0], [b 2, a 2], []]]
  have hP0 : 0 < P.length := by
    simp only [trackLength] at hPlen
    omega
  have hPhead : P[0]'hP0 = a 0 :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hP hP0
  have hPlast : P[P.length - 1]'(by omega) = b 0 :=
    Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hP hP0
  have haP : ∀ i, a i ∈ P → i = 0 := by
    intro i hi
    have hnint : a i ∉ trackInterior P := fun h => hPint _ h (haS i)
    rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior hi hnint hP0 with h | h
    · exact ha (h.trans hPhead)
    · exact absurd (h.trans hPlast) (habne i 0)
  have hbP' : ∀ i, b i ∈ P → i = 0 := by
    intro i hi
    have hnint : b i ∉ trackInterior P := fun h => hPint _ h (hbS i)
    rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior hi hnint hP0 with h | h
    · exact absurd (h.trans hPhead).symm (habne 0 i)
    · exact hb (h.trans hPlast)
  have ha1P : a 1 ∉ P := fun h => by have := haP 1 h; omega
  have ha2P : a 2 ∉ P := fun h => by have := haP 2 h; omega
  have hb1P : b 1 ∉ P := fun h => by have := hbP' 1 h; omega
  have hb2P : b 2 ∉ P := fun h => by have := hbP' 2 h; omega
  have da02 : a 0 ≠ a 2 := fun e => (show (0 : Fin 3) ≠ 2 by decide) (ha e)
  have db02 : b 0 ≠ b 2 := fun e => (show (0 : Fin 3) ≠ 2 by decide) (hb e)
  have da01 : a 0 ≠ a 1 := fun e => (show (0 : Fin 3) ≠ 1 by decide) (ha e)
  have da12 : a 1 ≠ a 2 := fun e => (show (1 : Fin 3) ≠ 2 by decide) (ha e)
  have db01 : b 0 ≠ b 1 := fun e => (show (0 : Fin 3) ≠ 1 by decide) (hb e)
  have db12 : b 1 ≠ b 2 := fun e => (show (1 : Fin 3) ≠ 2 by decide) (hb e)
  have e02 : IsTrackFrom H [a 0, b 1, a 2] (a 0) (a 2) :=
    threeTrack (habne 0 1) da02 (habne 2 1).symm (hadj 0 1) (hadj 2 1).symm
  have e03 : IsTrackFrom H [a 0, b 2] (a 0) (b 2) :=
    twoTrack (habne 0 2) (hadj 0 2)
  have e12 : IsTrackFrom H [b 0, a 2] (b 0) (a 2) :=
    twoTrack (habne 2 0).symm (hadj 2 0).symm
  have e13 : IsTrackFrom H [b 0, a 1, b 2] (b 0) (b 2) :=
    threeTrack (habne 1 0).symm db02 (habne 1 2) (hadj 1 0).symm (hadj 1 2)
  have e23 : IsTrackFrom H [a 2, b 2] (a 2) (b 2) :=
    twoTrack (habne 2 2) (hadj 2 2)
  have hιinj : Function.Injective ι := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ι] at hij ⊢
    all_goals first
      | exact (da02 hij).elim | exact (da02 hij.symm).elim
      | exact (db02 hij).elim | exact (db02 hij.symm).elim
      | exact (habne 0 0 hij).elim | exact (habne 0 0 hij.symm).elim
      | exact (habne 0 2 hij).elim | exact (habne 0 2 hij.symm).elim
      | exact (habne 2 0 hij).elim | exact (habne 2 0 hij.symm).elim
      | exact (habne 2 2 hij).elim | exact (habne 2 2 hij.symm).elim
  have htrack : ∀ u v : Fin 4, u ≠ v → IsTrackFrom H (T u v) (ι u) (ι v) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp [T, ι] at huv ⊢
    all_goals first
      | exact (huv rfl).elim
      | exact hP
      | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hP
      | exact e02 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e02
      | exact e03 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e03
      | exact e12 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e12
      | exact e13 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e13
      | exact e23 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse e23
  have hlen : ∀ u v : Fin 4, u ≠ v → 1 ≤ trackLength (T u v) := by
    intro u v huv
    simp only [trackLength] at hPlen
    fin_cases u <;> fin_cases v <;> simp [T, trackLength] at huv ⊢ <;> omega
  have hrev : ∀ u v : Fin 4, u ≠ v → T v u = (T u v).reverse := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at huv ⊢ <;> simp
  have hnamedIntP : ∀ x ∈ S₀, x ∉ trackInterior P := fun x hx h => hPint x h hx
  have ha0I := hnamedIntP (a 0) (haS 0)
  have ha1I := hnamedIntP (a 1) (haS 1)
  have ha2I := hnamedIntP (a 2) (haS 2)
  have hb0I := hnamedIntP (b 0) (hbS 0)
  have hb1I := hnamedIntP (b 1) (hbS 1)
  have hb2I := hnamedIntP (b 2) (hbS 2)
  have hIntNeA : ∀ w ∈ trackInterior P, ∀ i, w ≠ a i := by
    intro w hw i e
    apply hPint w hw
    rw [e]
    exact haS i
  have hIntNeB : ∀ w ∈ trackInterior P, ∀ i, w ≠ b i := by
    intro w hw i e
    apply hPint w hw
    rw [e]
    exact hbS i
  have hswapMem : ∀ u v : Fin 4, u ≠ v → ∀ x, x ∈ T v u ↔ x ∈ T u v := by
    intro u v huv x
    rw [hrev u v huv, List.mem_reverse]
  have hswapInt : ∀ u v : Fin 4, u ≠ v → ∀ x,
      x ∈ trackInterior (T v u) ↔ x ∈ trackInterior (T u v) := by
    intro u v huv x
    rw [hrev u v huv, Workspace.ProofLemmas.TrackSlice.trackInterior_reverse, List.mem_reverse]
  have hdisj0 : ∀ u v u' v' : Fin 4, u < v → u' < v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v' := by
    intro u v u' v' huv huv' hs w hw hmem
    fin_cases u <;> fin_cases v <;>
      simp [T, trackInterior] at huv hw
    all_goals try omega
    all_goals fin_cases u' <;> fin_cases v' <;>
      simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        List.mem_cons, List.mem_singleton] at huv' hmem
    all_goals simp at huv'
    all_goals try omega
    all_goals try exact hs rfl
    all_goals simp_all [trackInterior, da01, da02, da12, db01, db02, db12, habne,
      ha1P, ha2P, hb1P, hb2P, hIntNeA, hIntNeB, Ne.symm da01, Ne.symm da02,
      Ne.symm da12, Ne.symm db01, Ne.symm db02, Ne.symm db12,
      fun i j => Ne.symm (habne i j)]
  have hdisj : ∀ u v u' v' : Fin 4, u ≠ v → u' ≠ v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v' := by
    intro u v u' v' huv huv' hs w hw hmem
    rcases lt_or_gt_of_ne huv with h | h <;> rcases lt_or_gt_of_ne huv' with h' | h'
    · exact hdisj0 u v u' v' h h' hs w hw hmem
    · exact hdisj0 u v v' u' h h' (by simpa [Sym2.eq_swap] using hs) w hw
        ((hswapMem v' u' h'.ne w).mp hmem)
    · exact hdisj0 v u u' v' h h' (by simpa [Sym2.eq_swap] using hs) w
        ((hswapInt v u h.ne w).mp hw) hmem
    · exact hdisj0 v u v' u' h h' (by simpa [Sym2.eq_swap] using hs) w
        ((hswapInt v u h.ne w).mp hw) ((hswapMem v' u' h'.ne w).mp hmem)
  have hnew0 : ∀ u v : Fin 4, u < v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι := by
    intro u v huv w hw hr
    obtain ⟨k, rfl⟩ := hr
    fin_cases u <;> fin_cases v <;> simp [T, trackInterior] at huv hw
    all_goals try omega
    all_goals first
      | exact hPint _ hw (by fin_cases k <;> simp [ι, haS, hbS])
      | fin_cases k <;>
          simp_all [ι, da01, da02, da12, db01, db02, db12, habne,
            Ne.symm da01, Ne.symm da02, Ne.symm da12, Ne.symm db01,
            Ne.symm db02, Ne.symm db12, fun i j => Ne.symm (habne i j)]
  have hnew : ∀ u v : Fin 4, u ≠ v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι := by
    intro u v huv w hw hr
    rcases lt_or_gt_of_ne huv with h | h
    · exact hnew0 u v h w hw hr
    · exact hnew0 v u h w ((hswapInt v u h.ne w).mp hw) hr
  have hd : IsK4Datum H ι T := ⟨hιinj, htrack, hlen, hrev, hdisj, hnew⟩
  let S := dsubgraph H ι T hd
  refine ⟨S, isSubdivision_dsubgraph hd, ?_⟩
  rw [Workspace.ProofLemmas.ClassLemmas.nondegenerateAppearance_K4_iff]
  apply Workspace.ProofLemmas.DatumDegeneracy.nondegenerate_of_two_long hd
  · simp only [trackLength] at hPlen
    simpa [T] using (show 3 ≤ P.length by omega)
  · simp [T]

private def rot3 (i k : Fin 3) : Fin 3 :=
  ⟨(i.val + k.val) % 3, Nat.mod_lt _ (by decide)⟩

private theorem rot3_zero (i : Fin 3) : rot3 i 0 = i := by
  fin_cases i <;> rfl

private theorem rot3_injective (i : Fin 3) : Function.Injective (rot3 i) := by
  intro x y h
  fin_cases i <;> fin_cases x <;> fin_cases y <;> simp [rot3] at h ⊢

private theorem oppositeSideIndexed
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (S₀ : Set W) (a b : Fin 3 → W)
    (haS : ∀ i, a i ∈ S₀) (hbS : ∀ i, b i ∈ S₀)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (habne : ∀ i j, a i ≠ b j)
    (hadj : ∀ i j, H.Adj (a i) (b j))
    (i j : Fin 3) (P : List W) (hP : IsTrackFrom H P (a i) (b j))
    (hPlen : 2 ≤ trackLength P)
    (hPint : ∀ w ∈ trackInterior P, w ∉ S₀) :
    ∃ S : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe := by
  let aa : Fin 3 → W := fun k => a (rot3 i k)
  let bb : Fin 3 → W := fun k => b (rot3 j k)
  apply oppositeSide H S₀ aa bb
  · intro k
    exact haS (rot3 i k)
  · intro k
    exact hbS (rot3 j k)
  · exact ha.comp (rot3_injective i)
  · exact hb.comp (rot3_injective j)
  · intro x y
    exact habne (rot3 i x) (rot3 j y)
  · intro x y
    exact hadj (rot3 i x) (rot3 j y)
  · simpa [aa, bb, rot3_zero] using hP
  · exact hPlen
  · exact hPint

theorem k33ComponentYieldsNondegenerate
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H)
    (J : H.Subgraph)
    (hJ : Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)))
    (houtside : ∃ v : W, v ∉ J.verts) :
    ∃ S : H.Subgraph,
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) S.coe ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) S.coe := by
  classical
  obtain ⟨a, b, haS, hbS, ha, hb, habne, hadj, hcover⟩ :=
    Workspace.ProofLemmas.K33ComponentConstruction.exists_k33_vertices J hJ
  obtain ⟨v, hv⟩ := houtside
  have hcard : 2 ≤ J.verts.ncard := by
    have hsub : Set.range a ⊆ J.verts := by
      intro x hx
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      exact haS i
    have hc : (Set.range a).ncard = 3 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ ha, Set.ncard_univ]
      simp
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  obtain ⟨u₁, u₂, P, hu₁, hu₂, hne, hP, hPlen, hPint⟩ :=
    Workspace.ProofLemmas.TrackThroughComponent.exists_two_attachments_track
      hc3 J.verts hcard hv
  rcases hcover u₁ hu₁ with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases hcover u₂ hu₂ with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have hij : i ≠ j := fun e => hne (congrArg a e)
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact sameSide H J.verts ![a 0, a 1, a 2] b
          (by intro k; fin_cases k <;> simp [haS]) hbS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;>
              try { have hh := ha e; omega })
          hb (by intro x y; fin_cases x <;> simp [habne])
          (by intro x y; fin_cases x <;> simp [hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![a 1, a 0, a 2] b
          (by intro k; fin_cases k <;> simp [haS]) hbS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;>
              try { have hh := ha e; omega })
          hb (by intro x y; fin_cases x <;> simp [habne])
          (by intro x y; fin_cases x <;> simp [hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![a 0, a 2, a 1] b
          (by intro k; fin_cases k <;> simp [haS]) hbS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;>
              try { have hh := ha e; omega })
          hb (by intro x y; fin_cases x <;> simp [habne])
          (by intro x y; fin_cases x <;> simp [hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![a 2, a 0, a 1] b
          (by intro k; fin_cases k <;> simp [haS]) hbS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;>
              try { have hh := ha e; omega })
          hb (by intro x y; fin_cases x <;> simp [habne])
          (by intro x y; fin_cases x <;> simp [hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![a 1, a 2, a 0] b
          (by intro k; fin_cases k <;> simp [haS]) hbS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;>
              try { have hh := ha e; omega })
          hb (by intro x y; fin_cases x <;> simp [habne])
          (by intro x y; fin_cases x <;> simp [hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![a 2, a 1, a 0] b
          (by intro k; fin_cases k <;> simp [haS]) hbS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;>
              try { have hh := ha e; omega })
          hb (by intro x y; fin_cases x <;> simp [habne])
          (by intro x y; fin_cases x <;> simp [hadj]) P hP hPlen hPint
  · subst hj
    exact oppositeSideIndexed H J.verts a b haS hbS ha hb habne hadj i j P hP hPlen hPint
  · subst hj
    have hPr := Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hP
    have hPintr : ∀ w ∈ trackInterior P.reverse, w ∉ J.verts := by
      intro w hw
      rw [Workspace.ProofLemmas.TrackSlice.trackInterior_reverse, List.mem_reverse] at hw
      exact hPint w hw
    exact oppositeSideIndexed H J.verts a b haS hbS ha hb habne hadj j i P.reverse hPr
      (by simpa [trackLength] using hPlen) hPintr
  · subst hj
    have hij : i ≠ j := fun e => hne (congrArg b e)
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact sameSide H J.verts ![b 0, b 1, b 2] a
          (by intro k; fin_cases k <;> simp [hbS]) haS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;> try { have hh := hb e; omega })
          ha (by intro x y; fin_cases x <;> simp [Ne.symm (habne _ _)])
          (by intro x y; fin_cases x <;> simp [SimpleGraph.adj_comm, hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![b 1, b 0, b 2] a
          (by intro k; fin_cases k <;> simp [hbS]) haS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;> try { have hh := hb e; omega })
          ha (by intro x y; fin_cases x <;> simp [Ne.symm (habne _ _)])
          (by intro x y; fin_cases x <;> simp [SimpleGraph.adj_comm, hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![b 0, b 2, b 1] a
          (by intro k; fin_cases k <;> simp [hbS]) haS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;> try { have hh := hb e; omega })
          ha (by intro x y; fin_cases x <;> simp [Ne.symm (habne _ _)])
          (by intro x y; fin_cases x <;> simp [SimpleGraph.adj_comm, hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![b 2, b 0, b 1] a
          (by intro k; fin_cases k <;> simp [hbS]) haS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;> try { have hh := hb e; omega })
          ha (by intro x y; fin_cases x <;> simp [Ne.symm (habne _ _)])
          (by intro x y; fin_cases x <;> simp [SimpleGraph.adj_comm, hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![b 1, b 2, b 0] a
          (by intro k; fin_cases k <;> simp [hbS]) haS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;> try { have hh := hb e; omega })
          ha (by intro x y; fin_cases x <;> simp [Ne.symm (habne _ _)])
          (by intro x y; fin_cases x <;> simp [SimpleGraph.adj_comm, hadj]) P hP hPlen hPint
      | exact sameSide H J.verts ![b 2, b 1, b 0] a
          (by intro k; fin_cases k <;> simp [hbS]) haS
          (by intro x y e; fin_cases x <;> fin_cases y <;> simp at e ⊢ <;> try { have hh := hb e; omega })
          ha (by intro x y; fin_cases x <;> simp [Ne.symm (habne _ _)])
          (by intro x y; fin_cases x <;> simp [SimpleGraph.adj_comm, hadj]) P hP hPlen hPint

end Workspace.Types.K33ComponentYieldsNondegenerate
