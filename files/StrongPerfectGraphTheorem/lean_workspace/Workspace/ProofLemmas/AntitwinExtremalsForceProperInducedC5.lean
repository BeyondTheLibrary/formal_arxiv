import Workspace.Types.Core
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.HoleSupportCycleIso
import Workspace.ProofLemmas.OddCycleCliqueAndTwoColoringObstruction

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- Nonempty extremal clique and stable antitwin-side sets force a proper
imperfect induced subgraph, internally an induced five-cycle. -/
theorem AntitwinExtremalsForceProperInducedC5
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (u v : W) (huv : u ≠ v)
    (hanti : ∀ z : W, z ≠ u → z ≠ v →
      Xor' (K.Adj z u) (K.Adj z v))
    (D R : Set W)
    (hDsub : D ⊆ {z : W | z ≠ u ∧ z ≠ v ∧ K.Adj z v})
    (hDnonempty : D.Nonempty)
    (hDclique : K.IsClique D)
    (hDmax : ∀ z : W,
      z ∈ (({x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x u} ∪
        {x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x v}) \ D) →
        ∃ d ∈ D, ¬ K.Adj z d)
    (hRsub : R ⊆ {z : W | z ≠ u ∧ z ≠ v ∧ K.Adj z u})
    (hRnonempty : R.Nonempty)
    (hRstable : Set.Pairwise R (fun x y => ¬ K.Adj x y))
    (hRmax : ∀ z : W,
      z ∈ (({x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x u} ∪
        {x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x v}) \ R) →
        ∃ r ∈ R, K.Adj z r) :
    ∃ S : Set W, S ≠ Set.univ ∧ ¬ SPGT.IsPerfect (K.induce S) := by
  classical
  have hDnotu : ∀ ⦃d : W⦄, d ∈ D → ¬ K.Adj d u := by
    intro d hd hdu
    rcases hDsub hd with ⟨hdu', hdv', hdv⟩
    rcases hanti d hdu' hdv' with h | h
    · exact h.2 hdv
    · exact h.2 hdu
  have hDR : ∀ ⦃d r : W⦄, d ∈ D → r ∈ R → d ≠ r := by
    intro d r hd hr hdr
    apply hDnotu hd
    simpa [hdr] using (hRsub hr).2.2
  let N : W → Finset W := fun d =>
    R.toFinset.filter (fun r => K.Adj r d)
  have mem_N {r d : W} : r ∈ N d ↔ r ∈ R ∧ K.Adj r d := by
    simp [N]
  obtain ⟨x, hxD, hxmin⟩ :=
    Set.exists_min_image D (fun d => (N d).card) (Set.toFinite D) hDnonempty
  have hxnotR : x ∉ R := by
    intro hxR
    exact hDnotu hxD (hRsub hxR).2.2
  obtain ⟨z, hzR, hxz0⟩ :=
    hRmax x ⟨Or.inr (hDsub hxD), hxnotR⟩
  have hznotD : z ∉ D := by
    intro hzD
    exact hDnotu hzD (hRsub hzR).2.2
  obtain ⟨y, hyD, hzy⟩ :=
    hDmax z ⟨Or.inl (hRsub hzR), hznotD⟩
  have hxy : x ≠ y := by
    intro hxy
    apply hzy
    rw [← hxy]
    exact hxz0.symm
  have hzNx : z ∈ N x := mem_N.mpr ⟨hzR, hxz0.symm⟩
  have hzNy : z ∉ N y := by
    intro hzNy
    exact hzy (mem_N.mp hzNy).2
  have hwy_exists : ∃ w : W, w ∈ N y ∧ w ∉ N x := by
    by_contra h
    have hsub : N y ⊆ N x := by
      intro a ha
      by_contra ha'
      exact h ⟨a, ha, ha'⟩
    have hstrict : N y ⊂ N x :=
      (Finset.ssubset_iff_of_subset hsub).2 ⟨z, hzNx, hzNy⟩
    exact (Nat.not_lt_of_ge (hxmin y hyD)) (Finset.card_lt_card hstrict)
  obtain ⟨w, hwNy, hwNx⟩ := hwy_exists
  have hwR : w ∈ R := (mem_N.mp hwNy).1
  have hwyadj : K.Adj w y := (mem_N.mp hwNy).2
  have hwxnon : ¬ K.Adj w x := by
    intro hwx
    exact hwNx (mem_N.mpr ⟨hwR, hwx⟩)
  have hzw : z ≠ w := by
    intro hzw
    apply hwNx
    simpa [← hzw] using hzNx
  have hzx_ne : z ≠ x := (hDR hxD hzR).symm
  have hzy_ne : z ≠ y := (hDR hyD hzR).symm
  have hxw_ne : x ≠ w := hDR hxD hwR
  have hyw_ne : y ≠ w := hDR hyD hwR
  have huz_ne : u ≠ z := (hRsub hzR).1.symm
  have hux_ne : u ≠ x := (hDsub hxD).1.symm
  have huy_ne : u ≠ y := (hDsub hyD).1.symm
  have huw_ne : u ≠ w := (hRsub hwR).1.symm
  have hnodup : ([u, z, x, y, w] : List W).Nodup := by
    simp [huz_ne, hux_ne, huy_ne, huw_ne, hzx_ne, hzy_ne, hzw, hxy, hxw_ne, hyw_ne]
  have huz : K.Adj u z := (hRsub hzR).2.2.symm
  have hzu : K.Adj z u := huz.symm
  have hzx : K.Adj z x := hxz0.symm
  have hxz : K.Adj x z := hzx.symm
  have hxyedge : K.Adj x y := hDclique hxD hyD hxy
  have hyx : K.Adj y x := hxyedge.symm
  have hyw : K.Adj y w := hwyadj.symm
  have hwy : K.Adj w y := hyw.symm
  have hwu : K.Adj w u := (hRsub hwR).2.2
  have huw : K.Adj u w := hwu.symm
  have huxnon : ¬ K.Adj u x := fun h => hDnotu hxD h.symm
  have hxunon : ¬ K.Adj x u := hDnotu hxD
  have huynon : ¬ K.Adj u y := fun h => hDnotu hyD h.symm
  have hyunon : ¬ K.Adj y u := hDnotu hyD
  have hyznon : ¬ K.Adj y z := fun h => hzy h.symm
  have hxwnon : ¬ K.Adj x w := fun h => hwxnon h.symm
  have hzwnon : ¬ K.Adj z w := hRstable hzR hwR hzw
  have hwznon : ¬ K.Adj w z := fun h => hzwnon h.symm
  have hhole : SPGT.IsHoleList K [u, z, x, y, w] := by
    refine ⟨by norm_num, hnodup, ?_⟩
    intro i j hi hj
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      simp [huz, hzu, hzx, hxz, hxyedge, hyx, hyw, hwy, hwu, huw,
        huxnon, hxunon, huynon, hyunon, hzy, hyznon, hwxnon, hxwnon,
        hzwnon, hwznon]
  let c : List W := [u, z, x, y, w]
  have hholec : SPGT.IsHoleList K c := by
    simpa [c] using hhole
  refine ⟨(c.toFinset : Set W), ?_, ?_⟩
  · intro hS
    have hvS : v ∈ (c.toFinset : Set W) := by
      rw [hS]
      exact Set.mem_univ v
    have hvC : v ∈ c := by
      simpa using hvS
    have hvnot : v ∉ c := by
      simp [c, huv.symm, (hRsub hzR).2.1.symm, (hDsub hxD).2.1.symm,
        (hDsub hyD).2.1.symm, (hRsub hwR).2.1.symm]
    exact hvnot hvC
  · intro hperfect
    obtain ⟨e, -⟩ := HoleSupportCycleIso K c hholec
    have hperfectcycle : SPGT.IsPerfect (SimpleGraph.cycleGraph 5) := by
      simpa [c] using
        (Workspace.ProofLemmas.IsoTransport.isPerfect_of_iso e.symm hperfect)
    have hobs := OddCycleCliqueAndTwoColoringObstruction 5 (by norm_num) (by norm_num)
    have hcolor :=
      CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect
        (SimpleGraph.cycleGraph 5) hperfectcycle
    rw [hobs.1] at hcolor
    exact hobs.2 hcolor

end Workspace.ProofLemmas

