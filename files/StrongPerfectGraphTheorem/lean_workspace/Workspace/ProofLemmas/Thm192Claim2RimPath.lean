import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.Statements.S02.Thm_2_3

/-!
# The rim path used in 19.2, claim (2)

Once the inductive wheel lies in `{x₀,x₁,z} ∪ A`, delete `z` from its rim.
Its only rim neighbours are `x₀,x₁`, so the remaining path has interior in `A`.
The wheel supplies a complete edge avoiding `z`. By 2.3 the total number of
complete rim edges is even. Deleting the two complete edges at `z` therefore
leaves at least two complete edges.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim2RimPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete `z` from a hole whose only neighbours of `z` are the named ends. -/
theorem delete_vertex {G : SimpleGraph V} {C : List V} {z a b : V}
    (hC : IsHoleList G C) (hlen : 5 ≤ C.length) (hz : z ∈ C)
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b)
    (hza : G.Adj z a) (hzb : G.Adj z b)
    (honly : ∀ v ∈ C, G.Adj z v → v = a ∨ v = b) :
    ∃ P : List V, IsPathFrom G P a b ∧
      ∀ v, v ∈ P ↔ v ∈ C ∧ v ≠ z := by
  obtain ⟨r, hr⟩ := HoleArithmetic.exists_rotate_head hz
  let R := C.rotate r
  have hR : IsHoleList G R := HoleBasics.isHoleList_rotate hC r
  have hRl : 5 ≤ R.length := by simpa [R] using hlen
  have hR0 : R[0]'(by omega) = z := hr _
  have hP := HoleMinusVertexPath.isPathFrom_tail hR hRl
  have hends := HoleMinusVertexPath.ends_ne hR hRl
  have hfirst : R[1]'(by omega) = a ∨ R[1]'(by omega) = b := by
    apply honly _ (List.mem_rotate.mp (List.getElem_mem (l := R) (by omega)))
    rw [← hR0]
    exact (HoleMinusVertexPath.adj_head_iff hR hRl (by omega)).mpr (Or.inl rfl)
  have hlast : R[R.length - 1]'(by omega) = a ∨ R[R.length - 1]'(by omega) = b := by
    apply honly _ (List.mem_rotate.mp (List.getElem_mem (l := R) (by omega)))
    rw [← hR0]
    exact (HoleMinusVertexPath.adj_head_iff hR hRl (by omega)).mpr (Or.inr rfl)
  have hmem : ∀ v, v ∈ R.tail ↔ v ∈ C ∧ v ≠ z := by
    intro v
    rw [HoleMinusVertexPath.mem_tail_iff hR hRl, hR0]
    exact and_congr_left (fun _ => List.mem_rotate)
  rcases hfirst with hfirst | hfirst <;> rcases hlast with hlast | hlast
  · exact (hends (hfirst.trans hlast.symm)).elim
  · exact ⟨R.tail, by simpa only [hfirst, hlast] using hP, hmem⟩
  · refine ⟨R.tail.reverse, ?_, ?_⟩
    · simpa only [hfirst, hlast] using PathBasics.isPathFrom_reverse hP
    · intro v
      rw [List.mem_reverse, hmem]
  · exact (hends (hfirst.trans hlast.symm)).elim

/-- PAPER (19.2 (2)): *"there is a path ... containing at least two
`Y₀`-complete edges."* This is the path and parity step after locating the wheel. -/
theorem path_of_local_wheel {G : SimpleGraph V} (hG : Berge G)
    {C : List V} {W A : Set V} {z a b : V}
    (hW : IsWheel G C W) (hz : z ∈ C) (ha : a ∈ C) (hb : b ∈ C)
    (hab : a ≠ b) (hza : G.Adj z a) (hzb : G.Adj z b)
    (hzW : VertexComplete G z W) (haW : VertexComplete G a W)
    (hbW : VertexComplete G b W)
    (hsub : {v | v ∈ C} ⊆ ({a,b,z} : Set V) ∪ A)
    (hAz : ∀ v ∈ A, ¬ G.Adj z v) :
    ∃ P : List V, IsPathFrom G P a b ∧
      (∀ v ∈ SPGT.interior P, v ∈ A) ∧
      2 ≤ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u,v) ∧ EdgeComplete G W u v}.ncard := by
  classical
  have honly : ∀ v ∈ C, G.Adj z v → v = a ∨ v = b := by
    intro v hv hadj
    rcases hsub hv with hv | hv
    · rcases hv with hv | hv | hv
      · exact Or.inl hv
      · exact Or.inr hv
      · exact (G.irrefl (hv ▸ hadj)).elim
    · exact (hAz v hv hadj).elim
  have hlen : 5 ≤ C.length := le_trans (by omega) hW.1.2
  obtain ⟨P, hP, hmem⟩ := delete_vertex hW.1.1 hlen hz ha hb hab hza hzb honly
  have hzP : z ∉ P := fun h => (hmem z).mp h |>.2 rfl
  refine ⟨P, hP, ?_, ?_⟩
  · intro v hv
    have hv' := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hv
    rcases hsub ((hmem v).mp hv'.1).1 with hs | hs
    · rcases hs with hs | hs | hs
      · exact (hv'.2.1 hs).elim
      · exact (hv'.2.2 hs).elim
      · exact (((hmem v).mp hv'.1).2 hs).elim
    · exact hs
  let E : Set (Sym2 V) := {e | ∃ u ∈ P, ∃ v ∈ P, e = s(u,v) ∧ EdgeComplete G W u v}
  let F : Set (Sym2 V) := {e | ∃ u ∈ C, ∃ v ∈ C, e = s(u,v) ∧ EdgeComplete G W u v}
  have he0 : s(z,a) ∈ F := ⟨z,hz,a,ha,rfl,hza,hzW,haW⟩
  have he1 : s(z,b) ∈ F := ⟨z,hz,b,hb,rfl,hzb,hzW,hbW⟩
  have hEF : E ⊆ F := by
    rintro e ⟨u,hu,v,hv,he,hc⟩
    exact ⟨u,((hmem u).mp hu).1,v,((hmem v).mp hv).1,he,hc⟩
  have hsplit : F = insert s(z,a) (insert s(z,b) E) := by
    apply Set.Subset.antisymm
    · rintro e ⟨u,hu,v,hv,rfl,hc⟩
      by_cases huz : u = z
      · rcases honly v hv (huz ▸ hc.1) with hvb | hvb
        · exact Or.inl (by rw [huz, hvb])
        · exact Or.inr (Or.inl (by rw [huz, hvb]))
      by_cases hvz : v = z
      · rcases honly u hu (hvz ▸ hc.1.symm) with hua | hua
        · exact Or.inl (by rw [hvz, hua, Sym2.eq_swap])
        · exact Or.inr (Or.inl (by rw [hvz, hua, Sym2.eq_swap]))
      · exact Or.inr (Or.inr ⟨u,(hmem u).mpr ⟨hu,huz⟩,
          v,(hmem v).mpr ⟨hv,hvz⟩,rfl,hc⟩)
    · rintro e (rfl | rfl | he)
      · exact he0
      · exact he1
      · exact hEF he
  have hno : ∀ t, s(z,t) ∉ E := by
    rintro t ⟨u,hu,v,hv,he,_⟩
    have hzuv : z = u ∨ z = v := by
      have hm : z ∈ s(u,v) := he ▸ (Sym2.mem_mk_left z t)
      simpa only [Sym2.mem_iff] using hm
    rcases hzuv with hzuv | hzuv
    · exact hzP (hzuv ▸ hu)
    · exact hzP (hzuv ▸ hv)
  have he01 : s(z,a) ≠ s(z,b) := by
    intro he
    have he' := Sym2.eq_iff.mp he
    rcases he' with ⟨_,he'⟩ | ⟨he',he''⟩
    · exact hab he'
    · exact hza.ne he''.symm
  have hcard : F.ncard = E.ncard + 2 := by
    rw [hsplit, Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, not_or]; exact ⟨he01,hno a⟩),
      Set.ncard_insert_of_notMem (hno b)]
  have hEpos : 0 < E.ncard := by
    apply (Set.ncard_pos (Set.toFinite E)).mpr
    obtain ⟨u,v,s,t,hu,hv,hs,ht,huv,hst,hus,hut,hvs,hvt⟩ := hW.2.2
    by_cases huvz : u ≠ z ∧ v ≠ z
    · exact ⟨s(u,v),u,(hmem u).mpr ⟨hu,huvz.1⟩,
        v,(hmem v).mpr ⟨hv,huvz.2⟩,rfl,huv⟩
    · have hsz : s ≠ z := by
        intro he
        exact huvz ⟨fun h => hus (h.trans he.symm), fun h => hvs (h.trans he.symm)⟩
      have htz : t ≠ z := by
        intro he
        exact huvz ⟨fun h => hut (h.trans he.symm), fun h => hvt (h.trans he.symm)⟩
      exact ⟨s(s,t),s,(hmem s).mpr ⟨hs,hsz⟩,
        t,(hmem t).mpr ⟨ht,htz⟩,rfl,hst⟩
  have hFeven : Even F.ncard := by
    rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hG W hW.2.1.2.1 C
      (Or.inr hW.1.1) hW.2.1.2.2).2 hW.1.1 with he | ⟨u,v,huv,_,_⟩
    · exact he
    · have hpair : ∀ w ∈ C, VertexComplete G w W → w = u ∨ w = v := by
        intro w hw hc
        have hm : w ∈ {t | t ∈ C ∧ VertexComplete G t W} := ⟨hw,hc⟩
        rw [huv] at hm
        exact hm
      have hzuv := hpair z hz hzW
      have hauv := hpair a ha haW
      have hbuv := hpair b hb hbW
      have hza' := hza.ne
      have hzb' := hzb.ne
      rcases hzuv with hzuv | hzuv <;> rcases hauv with hauv | hauv <;>
        rcases hbuv with hbuv | hbuv <;> simp_all
  obtain ⟨k,hk⟩ := hFeven
  change 2 ≤ E.ncard
  omega

end Workspace.ProofLemmas.Thm192Claim2RimPath
