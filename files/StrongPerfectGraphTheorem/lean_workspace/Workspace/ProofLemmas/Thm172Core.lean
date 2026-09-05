import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S17.Thm_17_1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# The Roussel--Rubio strip conclusion in 17.2

This module follows the proof of 17.2 sentence by sentence.  The first two
claims build the nonadjacent vertices with opposite end attachments.  The last
part shows that neither vertex can have another neighbour in the connected set.
-/

namespace Workspace.ProofLemmas.Thm172Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem gidx {W : Type*} (L : List W) {i j : ℕ} (h : i = j)
    (hi : i < L.length) (hj : j < L.length) : L[i]'hi = L[j]'hj := by
  subst j
  rfl

private theorem two_le_length_of_ends_ne {G : SimpleGraph V} {P : List V} {x y : V}
    (hP : IsPathFrom G P x y) (hxy : x ≠ y) : 2 ≤ P.length := by
  have hpos : 0 < P.length := PathBasics.path_length_pos hP.1
  rcases (show P.length = 1 ∨ 2 ≤ P.length by omega) with h1 | h2
  · exfalso
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
    have hx : c = x := by simpa using hP.2.1
    have hy : c = y := by simpa using hP.2.2
    exact hxy (hx.symm.trans hy)
  · exact h2

private theorem rotate_index_eq {H : List V} (hnd : H.Nodup)
    {i j : ℕ} (hj : j < H.length) {w : V}
    (hhead : (H.rotate i).head? = some w) (hjw : H[j]'hj = w) :
    H.rotate i = H.rotate j := by
  have hpos : 0 < H.length := by omega
  have hmod : i % H.length < H.length := Nat.mod_lt _ hpos
  have hg : (H.rotate i).head? = H[(0 + i) % H.length]? := by
    rw [List.head?_eq_getElem?, List.getElem?_rotate hpos]
  rw [hg, Nat.zero_add, List.getElem?_eq_getElem hmod] at hhead
  have heq : H[i % H.length]'hmod = w := Option.some.inj hhead
  have hij : i % H.length = j := hnd.getElem_inj_iff.mp (heq.trans hjw.symm)
  rw [← List.rotate_mod H i, hij]

private theorem singleton_anticonnected (G : SimpleGraph V) (v : V) :
    AnticonnectedSet G ({v} : Set V) := by
  intro x y
  have hxy : x = y := Subtype.ext (x.2.trans y.2.symm)
  subst y
  exact SimpleGraph.Reachable.refl x

private theorem triangle_ne {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z :=
  ⟨hxy.ne, hxz.ne, hyz.ne⟩

/-- Two distinct vertices of the first triangle have adjacent partners in a reflection. -/
private theorem reflection_pair {G : SimpleGraph V} {a₁ a₂ a₃ b₁ b₂ b₃ u v : V}
    (h : IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃)
    (hu : u ∈ ({a₁, a₂, a₃} : Set V))
    (hv : v ∈ ({a₁, a₂, a₃} : Set V)) (huv : u ≠ v) :
    ∃ bu ∈ ({b₁, b₂, b₃} : Set V), ∃ bv ∈ ({b₁, b₂, b₃} : Set V),
      G.Adj u bu ∧ G.Adj v bv ∧ G.Adj bu bv := by
  obtain ⟨hA, hB, -, hiff⟩ := h
  have hbne : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ := by
    have hpair : ∀ a b : V, ({a, b} : Set V).ncard ≤ 2 := by
      intro a b
      have hh := Set.ncard_insert_le a ({b} : Set V)
      simpa using hh
    have hcard := hB.1
    refine ⟨?_, ?_, ?_⟩ <;> intro he
    · have hs : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by ext t; simp [he]
      rw [hs] at hcard
      exact (by have := hpair b₂ b₃; omega)
    · have hs : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by ext t; simp [he]
      rw [hs] at hcard
      exact (by have := hpair b₂ b₃; omega)
    · have hs : ({b₁, b₂, b₃} : Set V) = ({b₁, b₃} : Set V) := by ext t; simp [he]
      rw [hs] at hcard
      exact (by have := hpair b₁ b₃; omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · exact ⟨b₁, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.1⟩
  · exact ⟨b₁, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.2.1⟩
  · exact ⟨b₂, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) hbne.1.symm⟩
  · exact absurd rfl huv
  · exact ⟨b₂, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.2.2⟩
  · exact ⟨b₃, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) hbne.2.1.symm⟩
  · exact ⟨b₃, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hbne.2.2.symm⟩
  · exact absurd rfl huv

/-- The first parity paragraph of 17.2: the bridge hole has no `Y`-complete
vertex on its `a`--`b` path. -/
private theorem no_complete_on_bridge_path
    (G : SimpleGraph V) (hBerge : Berge G)
    (hnoOddWheel : ¬ ∃ (C : List V) (Z : Set V), IsOddWheel G C Z)
    (Y : Set V) (hY : AnticonnectedSet G Y)
    (P : List V) (a b a₀ b₀ : V) (hP : IsPathFrom G P a b)
    (hP3 : 3 ≤ P.length) (hC : IsHoleList G (b₀ :: a₀ :: P))
    (hCY : ∀ w ∈ b₀ :: a₀ :: P, w ∉ Y)
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (haY : ¬ VertexComplete G a Y) (hbY : ¬ VertexComplete G b Y)
    (ha₀P : ∀ w ∈ P, G.Adj a₀ w ↔ w = a)
    (hb₀P : ∀ w ∈ P, G.Adj b₀ w ↔ w = b) :
    ∀ w ∈ P, ¬ VertexComplete G w Y := by
  intro z hzP hzY
  have ha₀b₀ : G.Adj a₀ b₀ := by
    have hh := hC.2.2 0 1 (by simp) (by simp)
    have hadj : G.Adj b₀ a₀ := hh.mpr (by simp)
    exact hadj.symm
  have he0 : s(a₀, b₀) ∈ HoleYEdgeParity.yEdges G Y (b₀ :: a₀ :: P) :=
    ⟨a₀, by simp, b₀, by simp, rfl, ha₀b₀, ha₀Y, hb₀Y⟩
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hY
    (b₀ :: a₀ :: P) (Or.inr hC) hCY).2 hC
  have hsecond : ∃ e ∈ HoleYEdgeParity.yEdges G Y (b₀ :: a₀ :: P),
      e ≠ s(a₀, b₀) := by
    rcases h23 with heven | ⟨u, v, hpair, -, -⟩
    · have hpos : 0 < (HoleYEdgeParity.yEdges G Y (b₀ :: a₀ :: P)).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨s(a₀, b₀), he0⟩
      have hneone : (HoleYEdgeParity.yEdges G Y (b₀ :: a₀ :: P)).ncard ≠ 1 := by
        intro hone
        change Even (HoleYEdgeParity.yEdges G Y (b₀ :: a₀ :: P)).ncard at heven
        rw [hone] at heven
        norm_num at heven
      have htwo : 1 < (HoleYEdgeParity.yEdges G Y (b₀ :: a₀ :: P)).ncard := by omega
      exact Set.exists_ne_of_one_lt_ncard htwo s(a₀, b₀)
    · exfalso
      have hma : a₀ ∈ ({u, v} : Set V) := by rw [← hpair]; exact ⟨by simp, ha₀Y⟩
      have hmb : b₀ ∈ ({u, v} : Set V) := by rw [← hpair]; exact ⟨by simp, hb₀Y⟩
      have hmz : z ∈ ({u, v} : Set V) := by rw [← hpair]; exact ⟨by simp [hzP], hzY⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hma hmb hmz
      have hza₀ : z ≠ a₀ := by
        intro he
        subst z
        exact (List.nodup_cons.mp (List.nodup_cons.mp hC.2.1).2).1 hzP
      have hzb₀ : z ≠ b₀ := by
        intro he
        subst z
        exact (List.nodup_cons.mp hC.2.1).1 (by simp [hzP])
      rcases hma with rfl | rfl <;> rcases hmb with rfl | rfl <;>
        rcases hmz with rfl | rfl <;> simp_all
  obtain ⟨e, he, hene⟩ := hsecond
  obtain ⟨u, huC, v, hvC, rfl, huvE⟩ := he
  have endpoint_cases : ∀ q ∈ b₀ :: a₀ :: P, q = b₀ ∨ q = a₀ ∨ q ∈ P := by
    intro q hq
    simpa using hq
  have hu_ne_a₀ : u ≠ a₀ := by
    intro he; subst u
    rcases endpoint_cases v hvC with rfl | rfl | hvP
    · exact hene rfl
    · exact G.irrefl huvE.1
    · have hva : v = a := (ha₀P v hvP).1 huvE.1
      subst v
      exact haY huvE.2.2
  have hu_ne_b₀ : u ≠ b₀ := by
    intro he; subst u
    rcases endpoint_cases v hvC with rfl | rfl | hvP
    · exact G.irrefl huvE.1
    · exact hene Sym2.eq_swap
    · have hvb : v = b := (hb₀P v hvP).1 huvE.1
      subst v
      exact hbY huvE.2.2
  have hv_ne_a₀ : v ≠ a₀ := by
    intro he; subst v
    rcases endpoint_cases u huC with rfl | rfl | huP
    · exact hene Sym2.eq_swap
    · exact G.irrefl huvE.1
    · have hua : u = a := (ha₀P u huP).1 huvE.1.symm
      subst u
      exact haY huvE.2.1
  have hv_ne_b₀ : v ≠ b₀ := by
    intro he; subst v
    rcases endpoint_cases u huC with rfl | rfl | huP
    · exact G.irrefl huvE.1
    · exact hene rfl
    · have hub : u = b := (hb₀P u huP).1 huvE.1.symm
      subst u
      exact hbY huvE.2.1
  have hWheel : IsWheel G (b₀ :: a₀ :: P) Y := by
    refine ⟨⟨hC, ?_⟩, ⟨?_, hY, hCY⟩,
      a₀, b₀, u, v, by simp, by simp, huC, hvC,
      ⟨ha₀b₀, ha₀Y, hb₀Y⟩, huvE,
      hu_ne_a₀.symm, hv_ne_a₀.symm, hu_ne_b₀.symm, hv_ne_b₀.symm⟩
    · have heven := hBerge.1 _ hC
      rw [Nat.even_iff] at heven
      simp only [holeLength, List.length_cons]
      simp only [holeLength, List.length_cons] at heven
      omega
    · by_contra hnull
      have : Y = ∅ := Set.not_nonempty_iff_eq_empty.mp hnull
      subst Y
      exact haY (by simp [VertexComplete])
  have hseg : IsSegment G (b₀ :: a₀ :: P) Y [b₀, a₀] := by
    have htake : ((b₀ :: a₀ :: P).rotate 0).take 2 = [b₀, a₀] := by simp
    rw [← htake]
    apply SegmentBasics.isSegment_of_run hC (k := 0) (L := 2) (by omega) (by simp; omega)
    · intro t ht
      interval_cases t
      · exact ⟨b₀, by simp, hb₀Y⟩
      · exact ⟨a₀, by simp, ha₀Y⟩
    · intro hnext
      obtain ⟨d, hdpos, hdY⟩ := hnext
      have hdpos' : d = a := by
        have hlt : 2 < (b₀ :: a₀ :: P).length := by simp; omega
        rw [Nat.mod_eq_of_lt hlt] at hdpos
        have hhead : (b₀ :: a₀ :: P)[2]? = some a := by
          simp only [List.getElem?_cons_succ]
          rw [← List.head?_eq_getElem?]
          exact hP.2.1
        exact Option.some.inj (hdpos.symm.trans hhead)
      exact haY (hdpos' ▸ hdY)
    · intro hprev
      obtain ⟨d, hdpos, hdY⟩ := hprev
      have hdpos' : d = b := by
        have hpos : 0 < (b₀ :: a₀ :: P).length := by simp
        have hlt : (b₀ :: a₀ :: P).length - 1 < (b₀ :: a₀ :: P).length := by omega
        simp only [Nat.zero_add] at hdpos
        rw [Nat.mod_eq_of_lt hlt] at hdpos
        have hlast : (b₀ :: a₀ :: P)[(b₀ :: a₀ :: P).length - 1]? = some b := by
          rw [← List.getLast?_eq_getElem?]
          rw [List.getLast?_cons_of_ne_nil (by simp : a₀ :: P ≠ []),
            List.getLast?_cons_of_ne_nil (by intro h; simp [h] at hP3 : P ≠ [])]
          exact hP.2.2
        exact Option.some.inj (hdpos.symm.trans hlast)
      exact hbY (hdpos' ▸ hdY)
  exact hnoOddWheel ⟨b₀ :: a₀ :: P, Y, hWheel, [b₀, a₀], hseg,
    by simp [pathLength]⟩

/-- The hat branch of 2.10 in 17.2 contradicts 17.1. -/
private theorem no_hat_on_bridge
    (G : SimpleGraph V) (hG : InF7 G) (F Y : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F)
    (a₀ b₀ a b : V) (ha₀Fout : a₀ ∉ F) (hb₀Fout : b₀ ∉ F)
    (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (ha₀b₀ : G.Adj a₀ b₀)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (C : List V) (haC : a ∈ C) (hbC : b ∈ C)
    (hEvery : ∀ y ∈ Y, ∃ f ∈ F, G.Adj y f)
    (y : V) (hyY : y ∈ Y) (hhat : IsHatForHole G C a₀ b₀ y) : False := by
  let T : Set V := {a₀, b₀, y}
  have ha₀y : G.Adj a₀ y := hhat.2.2.2.2.1.symm
  have hb₀y : G.Adj b₀ y := hhat.2.2.2.2.2.1.symm
  have htri : IsTriangle G T := by
    have hne := triangle_ne ha₀b₀ ha₀y hb₀y
    refine ⟨Set.ncard_eq_three.mpr ⟨a₀, b₀, y, hne.1, hne.2.1, hne.2.2, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact ha₀b₀
    · exact ha₀y
    · exact ha₀b₀.symm
    · exact (huv rfl).elim
    · exact hb₀y
    · exact ha₀y.symm
    · exact hb₀y.symm
    · exact (huv rfl).elim
  have hyFout : y ∉ F := fun hyF => Set.disjoint_left.mp hFY hyF hyY
  have hFT : F ⊆ Tᶜ := by
    intro f hfF hfT
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hfT
    rcases hfT with rfl | rfl | rfl
    · exact ha₀Fout hfF
    · exact hb₀Fout hfF
    · exact hyFout hfF
  have hcatch : Catches G F T := by
    refine ⟨htri, hF, Set.disjoint_left.mpr hFT, ?_⟩
    intro v hv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv | hv
    · exact ⟨a, ha, by
        have hm : a ∈ {f ∈ F | G.Adj a₀ f} := by rw [ha₀F]; simp
        simpa [hv] using hm.2⟩
    · exact ⟨b, hb, by
        have hm : b ∈ {f ∈ F | G.Adj b₀ f} := by rw [hb₀F]; simp
        simpa [hv] using hm.2⟩
    · obtain ⟨q, hqF, hyq⟩ := hEvery y hyY
      exact ⟨q, hqF, by simpa [hv] using hyq⟩
  have hyna : ¬ G.Adj y a := by
    exact hhat.2.2.2.2.2.2 a haC
      (fun he => ha₀Fout (he ▸ ha)) (fun he => hb₀Fout (he ▸ ha))
  have hynb : ¬ G.Adj y b := by
    exact hhat.2.2.2.2.2.2 b hbC
      (fun he => ha₀Fout (he ▸ hb)) (fun he => hb₀Fout (he ▸ hb))
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T htri F hFT hcatch with
      href | ⟨f, hfF, htwo⟩
  · obtain ⟨r₁, r₂, r₃, s₁, s₂, s₃, hTeq, hsF, hrefl⟩ := href
    have ha₀R : a₀ ∈ ({r₁, r₂, r₃} : Set V) := by rw [← hTeq]; simp [T]
    have hb₀R : b₀ ∈ ({r₁, r₂, r₃} : Set V) := by rw [← hTeq]; simp [T]
    obtain ⟨sa, hsaS, sb, hsbS, ha₀sa, hb₀sb, hsasb⟩ :=
      reflection_pair hrefl ha₀R hb₀R ha₀b₀.ne
    have hsaF : sa ∈ F := hsF hsaS
    have hsbF : sb ∈ F := hsF hsbS
    have hsa : sa = a := by
      have hm : sa ∈ {f ∈ F | G.Adj a₀ f} := ⟨hsaF, ha₀sa⟩
      rw [ha₀F] at hm
      simpa using hm
    have hsb : sb = b := by
      have hm : sb ∈ {f ∈ F | G.Adj b₀ f} := ⟨hsbF, hb₀sb⟩
      rw [hb₀F] at hm
      simpa using hm
    exact hnab (hsa ▸ hsb ▸ hsasb)
  · have hle : (G.neighborSet f ∩ T).ncard ≤ 1 := by
      apply (Set.ncard_le_one (Set.toFinite _)).2
      intro u hu v hv
      obtain ⟨hfu, huT⟩ := hu
      obtain ⟨hfv, hvT⟩ := hv
      have hfu' : G.Adj f u := by simpa only [SimpleGraph.mem_neighborSet] using hfu
      have hfv' : G.Adj f v := by simpa only [SimpleGraph.mem_neighborSet] using hfv
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at huT hvT
      rcases huT with huT | huT | huT <;> rcases hvT with hvT | hvT | hvT
      · exact huT.trans hvT.symm
      · have hfa : f = a := by
          have hm : f ∈ {q ∈ F | G.Adj a₀ q} := ⟨hfF, by simpa [huT] using hfu'.symm⟩
          rw [ha₀F] at hm
          simpa using hm
        have hfb : f = b := by
          have hm : f ∈ {q ∈ F | G.Adj b₀ q} := ⟨hfF, by simpa [hvT] using hfv'.symm⟩
          rw [hb₀F] at hm
          simpa using hm
        exact False.elim (hab (hfa.symm.trans hfb))
      · have hfa : f = a := by
          have hm : f ∈ {q ∈ F | G.Adj a₀ q} := ⟨hfF, by simpa [huT] using hfu'.symm⟩
          rw [ha₀F] at hm
          simpa using hm
        exact (hyna (by simpa [hfa, hvT] using hfv'.symm)).elim
      · have hfb : f = b := by
          have hm : f ∈ {q ∈ F | G.Adj b₀ q} := ⟨hfF, by simpa [huT] using hfu'.symm⟩
          rw [hb₀F] at hm
          simpa using hm
        have hfa : f = a := by
          have hm : f ∈ {q ∈ F | G.Adj a₀ q} := ⟨hfF, by simpa [hvT] using hfv'.symm⟩
          rw [ha₀F] at hm
          simpa using hm
        exact False.elim (hab (hfa.symm.trans hfb))
      · exact huT.trans hvT.symm
      · have hfb : f = b := by
          have hm : f ∈ {q ∈ F | G.Adj b₀ q} := ⟨hfF, by simpa [huT] using hfu'.symm⟩
          rw [hb₀F] at hm
          simpa using hm
        exact (hynb (by simpa [hfb, hvT] using hfv'.symm)).elim
      · have hfa : f = a := by
          have hm : f ∈ {q ∈ F | G.Adj a₀ q} := ⟨hfF, by simpa [hvT] using hfv'.symm⟩
          rw [ha₀F] at hm
          simpa using hm
        exact (hyna (by simpa [hfa, huT] using hfu'.symm)).elim
      · have hfb : f = b := by
          have hm : f ∈ {q ∈ F | G.Adj b₀ q} := ⟨hfF, by simpa [hvT] using hfv'.symm⟩
          rw [hb₀F] at hm
          simpa using hm
        exact (hynb (by simpa [hfb, huT] using hfu'.symm)).elim
      · exact huT.trans hvT.symm
    omega

/-- Read the genuine orientation of a leap on the canonical bridge hole
`b₀-a₀-P-b₀`.  Its two vertices attach to the two ends of `P` in opposite
orders. -/
private theorem leap_on_bridge_ends
    (G : SimpleGraph V) (P : List V) (a b a₀ b₀ x y : V)
    (hP : IsPathFrom G P a b) (hP3 : 3 ≤ P.length)
    (hC : IsHoleList G (b₀ :: a₀ :: P))
    (hxa₀ : x ≠ a₀) (hxb₀ : x ≠ b₀) (hya₀ : y ≠ a₀) (hyb₀ : y ≠ b₀)
    (hleap : IsLeapForHole G (b₀ :: a₀ :: P) b₀ a₀ x y ∨
      IsLeapForHole G (b₀ :: a₀ :: P) a₀ b₀ x y) :
    ¬ G.Adj x y ∧ G.Adj x a ∧ ¬ G.Adj x b ∧ G.Adj y b ∧ ¬ G.Adj y a ∧
      (∀ w ∈ P, G.Adj x w ↔ w = a) ∧ (∀ w ∈ P, G.Adj y w ↔ w = b) := by
  have hnd := hC.2.1
  have hPpos : 0 < P.length := by omega
  have hP0 : P[0]'hPpos = a := PathBasics.getElem_zero_of_head? hP.2.1 hPpos
  have hPlast : P[P.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hP.2.2 hPpos
  rcases hleap with hleap | hleap
  · obtain ⟨-, i, hhead, hlast, -, -, hxy, hnxy, hAdjX, hAdjY⟩ := hleap
    have hrot : (b₀ :: a₀ :: P).rotate i = (b₀ :: a₀ :: P).rotate 1 :=
      rotate_index_eq hnd (j := 1) (by simp) hhead (by simp)
    have hshape : (b₀ :: a₀ :: P).rotate 1 = a₀ :: (P ++ [b₀]) := by
      rw [List.rotate_cons_succ]
      simp
    rw [hrot, hshape] at hAdjX hAdjY
    let R : List V := a₀ :: (P ++ [b₀])
    have hRlen : R.length = P.length + 2 := by simp [R]
    have hR1 : R[1]'(by simp [R]) = a := by
      simp only [R, List.getElem_cons_succ]
      rw [List.getElem_append_left hPpos, hP0]
    have hRP : P.length < R.length := by rw [hRlen]; omega
    have hRb : R[P.length]'hRP = b := by
      have hi : P.length - 1 < P.length := by omega
      have hj : (P.length - 1) + 1 < R.length := by rw [hRlen]; omega
      calc
        R[P.length]'hRP = R[(P.length - 1) + 1]'hj := gidx R (by omega) _ _
        _ = P[P.length - 1]'hi := by
          simp only [R, List.getElem_cons_succ]
          exact List.getElem_append_left hi
        _ = b := hPlast
    have bridge : ∀ (c w : V), c ≠ a₀ → c ≠ b₀ →
        ((G.deleteEdges {s(b₀, a₀)}).Adj c w ↔ G.Adj c w) := by
      intro c w hca hcb
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hcb h1
      · exact hca h1
    have hnxyG : ¬ G.Adj x y := fun h => hnxy ((bridge x y hxa₀ hxb₀).2 h)
    have hxa : G.Adj x a := by
      have hd := (hAdjX 1 (by rw [hRlen]; omega)).2 (Or.inr (Or.inl rfl))
      rw [hR1] at hd
      exact (bridge x a hxa₀ hxb₀).1 hd
    have hxb : ¬ G.Adj x b := by
      intro h
      have hd : (G.deleteEdges {s(b₀, a₀)}).Adj x (R[P.length]'hRP) := by
        rw [hRb]
        exact (bridge x b hxa₀ hxb₀).2 h
      have hi := (hAdjX P.length hRP).1 hd
      rw [hRlen] at hi
      omega
    have hyb : G.Adj y b := by
      have hd := (hAdjY P.length hRP).2 (Or.inr (Or.inl (by rw [hRlen]; omega)))
      rw [hRb] at hd
      exact (bridge y b hya₀ hyb₀).1 hd
    have hya : ¬ G.Adj y a := by
      intro h
      have hd : (G.deleteEdges {s(b₀, a₀)}).Adj y (R[1]'(by rw [hRlen]; omega)) := by
        rw [hR1]
        exact (bridge y a hya₀ hyb₀).2 h
      have hi := (hAdjY 1 (by rw [hRlen]; omega)).1 hd
      rw [hRlen] at hi
      omega
    have hxP : ∀ w ∈ P, G.Adj x w ↔ w = a := by
      intro w hw
      constructor
      · intro hxw
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
        have hRj : j + 1 < R.length := by rw [hRlen]; omega
        have helem : R[j + 1]'hRj = P[j]'hj := by
          simp only [R, List.getElem_cons_succ]
          exact List.getElem_append_left hj
        have hd : (G.deleteEdges {s(b₀, a₀)}).Adj x (R[j + 1]'hRj) := by
          rw [helem]
          exact (bridge x _ hxa₀ hxb₀).2 hxw
        have hj0 := (hAdjX (j + 1) hRj).1 hd
        rw [hRlen] at hj0
        have : j = 0 := by omega
        subst j
        exact hP0
      · rintro rfl
        exact hxa
    have hyP : ∀ w ∈ P, G.Adj y w ↔ w = b := by
      intro w hw
      constructor
      · intro hyw
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
        have hRj : j + 1 < R.length := by rw [hRlen]; omega
        have helem : R[j + 1]'hRj = P[j]'hj := by
          simp only [R, List.getElem_cons_succ]
          exact List.getElem_append_left hj
        have hd : (G.deleteEdges {s(b₀, a₀)}).Adj y (R[j + 1]'hRj) := by
          rw [helem]
          exact (bridge y _ hya₀ hyb₀).2 hyw
        have hjlast := (hAdjY (j + 1) hRj).1 hd
        rw [hRlen] at hjlast
        have he : j = P.length - 1 := by omega
        exact (gidx P he hj (by omega)).trans hPlast
      · rintro rfl
        exact hyb
    exact ⟨hnxyG, hxa, hxb, hyb, hya, hxP, hyP⟩
  · obtain ⟨-, i, hhead, hlast, -⟩ := hleap
    have hrot : (b₀ :: a₀ :: P).rotate i = (b₀ :: a₀ :: P).rotate 0 :=
      rotate_index_eq hnd (j := 0) (by simp) hhead (by simp)
    rw [hrot, List.rotate_zero] at hlast
    have hlen : (b₀ :: a₀ :: P).length = P.length + 2 := by simp
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show (b₀ :: a₀ :: P).length - 1 <
        (b₀ :: a₀ :: P).length by rw [hlen]; omega)] at hlast
    have ha₀1 : (b₀ :: a₀ :: P)[1]'(by simp) = a₀ := by simp
    have hidx := hnd.getElem_inj_iff.mp ((Option.some.inj hlast).trans ha₀1.symm)
    rw [hlen] at hidx
    omega

/-- Claim (1) of the proof of 17.2.  Under the standing assumption that every
hub vertex meets `F`, 2.10 supplies two nonadjacent hub vertices with the two
opposite end-attachment patterns. -/
private theorem exists_opposite_end_pair
    (G : SimpleGraph V) (hG : InF7 G) (F Y : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F) (hY : AnticonnectedSet G Y)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (ha : a ∈ F) (hb : b ∈ F)
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (haY : ¬ VertexComplete G a Y) (hbY : ¬ VertexComplete G b Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (hEvery : ∀ y ∈ Y, ∃ f ∈ F, G.Adj y f) :
    ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, ¬ G.Adj y₁ y₂ ∧
      G.Adj y₁ a ∧ ¬ G.Adj y₁ b ∧ G.Adj y₂ b ∧ ¬ G.Adj y₂ a := by
  have haa₀ : G.Adj a a₀ := by
    have hh := hpath.2.2 0 1 (by simp) (by simp)
    exact hh.2 (by simp)
  have ha₀b₀ : G.Adj a₀ b₀ := by
    have hh := hpath.2.2 1 2 (by simp) (by simp)
    exact hh.2 (by simp)
  have hb₀b : G.Adj b₀ b := by
    have hh := hpath.2.2 2 3 (by simp) (by simp)
    exact hh.2 (by simp)
  have hnab : ¬ G.Adj a b := by
    intro hadj
    have hh := (hpath.2.2 0 3 (by simp) (by simp)).1 hadj
    simp at hh
  have hna₀b : ¬ G.Adj a₀ b := by
    intro hadj
    have hh := (hpath.2.2 1 3 (by simp) (by simp)).1 hadj
    simp at hh
  have hnb₀a : ¬ G.Adj b₀ a := by
    intro hadj
    have hh := (hpath.2.2 0 2 (by simp) (by simp)).1 hadj.symm
    simp at hh
  have hpathFrom : IsPathFrom G [a, a₀, b₀, b] a b := ⟨hpath, by simp, by simp⟩
  have hab : a ≠ b := PathBasics.isPathFrom_ends_ne hpathFrom (by simp [pathLength])
  obtain ⟨P, hP, hPF⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hF ha hb
  have hP3 : 3 ≤ P.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hP hab hnab
  have haP : a ∈ P := PathBasics.head_mem hP.2.1
  have hbP : b ∈ P := PathBasics.getLast_mem hP.2.2
  have ha₀Pout : a₀ ∉ P := fun hm => ha₀ (Or.inl (hPF a₀ hm))
  have hb₀Pout : b₀ ∉ P := fun hm => hb₀ (Or.inl (hPF b₀ hm))
  have ha₀P : ∀ w ∈ P, G.Adj a₀ w ↔ w = a := by
    intro w hw
    constructor
    · intro hadj
      have hm : w ∈ {f ∈ F | G.Adj a₀ f} := ⟨hPF w hw, hadj⟩
      rw [ha₀F] at hm
      simpa using hm
    · rintro rfl
      exact haa₀.symm
  have hb₀P : ∀ w ∈ P, G.Adj b₀ w ↔ w = b := by
    intro w hw
    constructor
    · intro hadj
      have hm : w ∈ {f ∈ F | G.Adj b₀ f} := ⟨hPF w hw, hadj⟩
      rw [hb₀F] at hm
      simpa using hm
    · rintro rfl
      exact hb₀b
  have hC : IsHoleList G (b₀ :: a₀ :: P) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hP (by
      simp only [pathLength]; omega) haa₀.symm hb₀b ha₀b₀
      ha₀Pout hb₀Pout hna₀b hnb₀a ?_ ?_
    · intro w hw hadj
      have hwP := PathBasics.interior_subset hw
      have hwa : w = a := (ha₀P w hwP).1 hadj
      exact (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw |>.2.1 hwa
    · intro w hw hadj
      have hwP := PathBasics.interior_subset hw
      have hwb : w = b := (hb₀P w hwP).1 hadj
      exact (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw |>.2.2 hwb
  have hCY : ∀ w ∈ b₀ :: a₀ :: P, w ∉ Y := by
    intro w hw hwY
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hb₀ (Or.inr hwY)
    · rcases List.mem_cons.mp hw with rfl | hwP
      · exact ha₀ (Or.inr hwY)
      · exact Set.disjoint_left.mp hFY (hPF w hwP) hwY
  have hnone := no_complete_on_bridge_path G hG.1.1.1.1 hG.2.1 Y hY
    P a b a₀ b₀ hP hP3 hC hCY ha₀Y hb₀Y haY hbY ha₀P hb₀P
  have honly : ∀ w ∈ b₀ :: a₀ :: P, VertexComplete G w Y → w = b₀ ∨ w = a₀ := by
    intro w hw hwY
    rcases List.mem_cons.mp hw with h | hw
    · exact Or.inl h
    · rcases List.mem_cons.mp hw with h | hwP
      · exact Or.inr h
      · exact (hnone w hwP hwY).elim
  have hlen : 4 < holeLength (b₀ :: a₀ :: P) := by
    simp only [holeLength, List.length_cons]
    omega
  have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hG.1.1.1.1 Y hY
    (b₀ :: a₀ :: P) hC hCY hlen b₀ a₀ (by simp) (by simp) ha₀b₀.symm
    hb₀Y ha₀Y honly
  rcases h210 with ⟨y, hyY, hhat⟩ | ⟨y₁, hy₁Y, y₂, hy₂Y, hleap⟩
  · exact False.elim (no_hat_on_bridge G hG F Y hFY hF b₀ a₀ b a
      (fun h => hb₀ (Or.inl h)) (fun h => ha₀ (Or.inl h)) hb ha hab.symm
      (fun h => hnab h.symm) ha₀b₀.symm hb₀F ha₀F
      (b₀ :: a₀ :: P) (by simp [hbP]) (by simp [haP]) hEvery y hyY hhat)
  · have hy₁a₀ : y₁ ≠ a₀ := fun he => ha₀ (Or.inr (he ▸ hy₁Y))
    have hy₁b₀ : y₁ ≠ b₀ := fun he => hb₀ (Or.inr (he ▸ hy₁Y))
    have hy₂a₀ : y₂ ≠ a₀ := fun he => ha₀ (Or.inr (he ▸ hy₂Y))
    have hy₂b₀ : y₂ ≠ b₀ := fun he => hb₀ (Or.inr (he ▸ hy₂Y))
    obtain ⟨hy₁y₂, hy₁a, hy₁b, hy₂b, hy₂a, -, -⟩ :=
      leap_on_bridge_ends G P a b a₀ b₀ y₁ y₂ hP hP3 hC
        hy₁a₀ hy₁b₀ hy₂a₀ hy₂b₀ hleap
    exact ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁y₂, hy₁a, hy₁b, hy₂b, hy₂a⟩

/-- Claim (2) of the proof of 17.2, for one chosen `a`--`b` path. -/
private theorem no_pair_neighbor_in_path_interior
    (G : SimpleGraph V) (hG : InF7 G) (Y : Set V) (hY : AnticonnectedSet G Y)
    (P : List V) (a b a₀ b₀ y₁ y₂ : V)
    (hP : IsPathFrom G P a b) (hP3 : 3 ≤ P.length)
    (hC : IsHoleList G (b₀ :: a₀ :: P))
    (hCY : ∀ w ∈ b₀ :: a₀ :: P, w ∉ Y)
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (hy₁Y : y₁ ∈ Y) (hy₂Y : y₂ ∈ Y) (hy₁y₂ : ¬ G.Adj y₁ y₂)
    (hy₁a : G.Adj y₁ a) (hy₁b : ¬ G.Adj y₁ b)
    (hy₂b : G.Adj y₂ b) (hy₂a : ¬ G.Adj y₂ a)
    (ha₀P : ∀ w ∈ P, G.Adj a₀ w ↔ w = a)
    (hb₀P : ∀ w ∈ P, G.Adj b₀ w ↔ w = b) :
    ¬ ∃ w ∈ SPGT.interior P, G.Adj y₁ w ∨ G.Adj y₂ w := by
  intro hinter
  let Z : Set V := {y₁, y₂}
  have hy₁ne₂ : y₁ ≠ y₂ := by
    intro he
    subst y₂
    exact hy₂a hy₁a
  have hZanti : AnticonnectedSet G Z := by
    intro u v
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.refl u
    · apply SimpleGraph.Adj.reachable
      change Gᶜ.Adj (u : V) (v : V)
      apply (SimpleGraph.compl_adj G (u : V) (v : V)).2
      refine ⟨fun he => huv (Subtype.ext he), ?_⟩
      have huM := u.2
      have hvM := v.2
      simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at huM hvM
      rcases huM with hu | hu <;> rcases hvM with hv | hv
      · exact False.elim (huv (Subtype.ext (hu.trans hv.symm)))
      · simpa [hu, hv] using hy₁y₂
      · simpa [hu, hv] using fun h => hy₁y₂ h.symm
      · exact False.elim (huv (Subtype.ext (hu.trans hv.symm)))
  have hCZ : ∀ w ∈ b₀ :: a₀ :: P, w ∉ Z := by
    intro w hw hwZ
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hwZ
    rcases hwZ with he | he
    · exact hCY w hw (by simpa [he] using hy₁Y)
    · exact hCY w hw (by simpa [he] using hy₂Y)
  have ha₀Z : VertexComplete G a₀ Z := by
    intro z hz
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with he | he
    · simpa [he] using ha₀Y y₁ hy₁Y
    · simpa [he] using ha₀Y y₂ hy₂Y
  have hb₀Z : VertexComplete G b₀ Z := by
    intro z hz
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with he | he
    · simpa [he] using hb₀Y y₁ hy₁Y
    · simpa [he] using hb₀Y y₂ hy₂Y
  have haZ : ¬ VertexComplete G a Z := by
    intro hc
    exact hy₂a (hc y₂ (by simp [Z])).symm
  have hbZ : ¬ VertexComplete G b Z := by
    intro hc
    exact hy₁b (hc y₁ (by simp [Z])).symm
  have hPnone := no_complete_on_bridge_path G hG.1.1.1.1 hG.2.1 Z hZanti
    P a b a₀ b₀ hP hP3 hC hCZ ha₀Z hb₀Z haZ hbZ ha₀P hb₀P
  have hsome : ∃ w ∈ P, VertexComplete G w Z := by
    by_contra hn
    have hnone : ∀ w ∈ P, ¬ VertexComplete G w Z := by
      intro w hw hc
      exact hn ⟨w, hw, hc⟩
    have honly : ∀ w ∈ b₀ :: a₀ :: P, VertexComplete G w Z → w = b₀ ∨ w = a₀ := by
      intro w hw hwZ
      rcases List.mem_cons.mp hw with h | hw
      · exact Or.inl h
      · rcases List.mem_cons.mp hw with h | hwP
        · exact Or.inr h
        · exact (hnone w hwP hwZ).elim
    have hlen : 4 < holeLength (b₀ :: a₀ :: P) := by
      simp only [holeLength, List.length_cons]
      omega
    have ha₀b₀ : G.Adj a₀ b₀ := by
      have hh := hC.2.2 0 1 (by simp) (by simp)
      exact (hh.2 (by simp)).symm
    have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hG.1.1.1.1 Z hZanti
      (b₀ :: a₀ :: P) hC hCZ hlen b₀ a₀ (by simp) (by simp) ha₀b₀.symm
      hb₀Z ha₀Z honly
    rcases h210 with ⟨z, hzZ, hhat⟩ | ⟨x, hxZ, y, hyZ, hleap⟩
    · have haP : a ∈ P := PathBasics.head_mem hP.2.1
      have hbP : b ∈ P := PathBasics.getLast_mem hP.2.2
      have ha₀Pout : a₀ ∉ P := (List.nodup_cons.mp (List.nodup_cons.mp hC.2.1).2).1
      have hb₀Pout : b₀ ∉ P := fun h => (List.nodup_cons.mp hC.2.1).1 (by simp [h])
      have hza : ¬ G.Adj z a := hhat.2.2.2.2.2.2 a (by simp [haP])
        (fun he => hb₀Pout (he ▸ haP)) (fun he => ha₀Pout (he ▸ haP))
      have hzb : ¬ G.Adj z b := hhat.2.2.2.2.2.2 b (by simp [hbP])
        (fun he => hb₀Pout (he ▸ hbP)) (fun he => ha₀Pout (he ▸ hbP))
      simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hzZ
      rcases hzZ with rfl | rfl
      · exact hza hy₁a
      · exact hzb hy₂b
    · have hxa₀ : x ≠ a₀ := fun he => hCZ x (by simp [he]) hxZ
      have hxb₀ : x ≠ b₀ := fun he => hCZ x (by simp [he]) hxZ
      have hya₀ : y ≠ a₀ := fun he => hCZ y (by simp [he]) hyZ
      have hyb₀ : y ≠ b₀ := fun he => hCZ y (by simp [he]) hyZ
      obtain ⟨hxy, hxa, hxb, hyb, hya, hxP, hyP⟩ :=
        leap_on_bridge_ends G P a b a₀ b₀ x y hP hP3 hC
          hxa₀ hxb₀ hya₀ hyb₀ hleap
      simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hxZ hyZ
      rcases hxZ with hx | hx <;> rcases hyZ with hy | hy
      · exact hya (by simpa [hx, hy] using hxa)
      · obtain ⟨w, hw, hwadj⟩ := hinter
        have hwi := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
        rcases hwadj with hwadj | hwadj
        · exact hwi.2.1 ((hxP w hwi.1).1 (by simpa [hx] using hwadj))
        · exact hwi.2.2 ((hyP w hwi.1).1 (by simpa [hy] using hwadj))
      · exact hy₂a (by simpa [hx] using hxa)
      · exact hya (by simpa [hx, hy] using hxa)
  obtain ⟨w, hwP, hwZ⟩ := hsome
  exact hPnone w hwP hwZ

/-- Claim (2), uniformly for every induced `a`--`b` path contained in `F`. -/
private theorem no_pair_neighbor_in_F_path
    (G : SimpleGraph V) (hG : InF7 G) (F Y : Set V)
    (hFY : Disjoint F Y) (hY : AnticonnectedSet G Y)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (y₁ y₂ : V) (hy₁Y : y₁ ∈ Y) (hy₂Y : y₂ ∈ Y)
    (hy₁y₂ : ¬ G.Adj y₁ y₂)
    (hy₁a : G.Adj y₁ a) (hy₁b : ¬ G.Adj y₁ b)
    (hy₂b : G.Adj y₂ b) (hy₂a : ¬ G.Adj y₂ a)
    (P : List V) (hP : IsPathFrom G P a b) (hPF : ∀ w ∈ P, w ∈ F) :
    ¬ ∃ w ∈ SPGT.interior P, G.Adj y₁ w ∨ G.Adj y₂ w := by
  have haa₀ : G.Adj a a₀ := (hpath.2.2 0 1 (by simp) (by simp)).2 (by simp)
  have ha₀b₀ : G.Adj a₀ b₀ := (hpath.2.2 1 2 (by simp) (by simp)).2 (by simp)
  have hb₀b : G.Adj b₀ b := (hpath.2.2 2 3 (by simp) (by simp)).2 (by simp)
  have hnab : ¬ G.Adj a b := by
    intro hadj
    have := (hpath.2.2 0 3 (by simp) (by simp)).1 hadj
    simp at this
  have hna₀b : ¬ G.Adj a₀ b := by
    intro hadj
    have := (hpath.2.2 1 3 (by simp) (by simp)).1 hadj
    simp at this
  have hnb₀a : ¬ G.Adj b₀ a := by
    intro hadj
    have := (hpath.2.2 0 2 (by simp) (by simp)).1 hadj.symm
    simp at this
  have hfour : IsPathFrom G [a, a₀, b₀, b] a b := ⟨hpath, by simp, by simp⟩
  have hab : a ≠ b := PathBasics.isPathFrom_ends_ne hfour (by simp [pathLength])
  have hP3 : 3 ≤ P.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hP hab hnab
  have ha₀Pout : a₀ ∉ P := fun hm => ha₀ (Or.inl (hPF a₀ hm))
  have hb₀Pout : b₀ ∉ P := fun hm => hb₀ (Or.inl (hPF b₀ hm))
  have ha₀P : ∀ w ∈ P, G.Adj a₀ w ↔ w = a := by
    intro w hw
    constructor
    · intro hadj
      have hm : w ∈ {f ∈ F | G.Adj a₀ f} := ⟨hPF w hw, hadj⟩
      rw [ha₀F] at hm
      simpa using hm
    · rintro rfl
      exact haa₀.symm
  have hb₀P : ∀ w ∈ P, G.Adj b₀ w ↔ w = b := by
    intro w hw
    constructor
    · intro hadj
      have hm : w ∈ {f ∈ F | G.Adj b₀ f} := ⟨hPF w hw, hadj⟩
      rw [hb₀F] at hm
      simpa using hm
    · rintro rfl
      exact hb₀b
  have hC : IsHoleList G (b₀ :: a₀ :: P) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hP (by
      simp only [pathLength]; omega) haa₀.symm hb₀b ha₀b₀
      ha₀Pout hb₀Pout hna₀b hnb₀a ?_ ?_
    · intro w hw hadj
      have hwP := PathBasics.interior_subset hw
      exact (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw |>.2.1
        ((ha₀P w hwP).1 hadj)
    · intro w hw hadj
      have hwP := PathBasics.interior_subset hw
      exact (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw |>.2.2
        ((hb₀P w hwP).1 hadj)
  have hCY : ∀ w ∈ b₀ :: a₀ :: P, w ∉ Y := by
    intro w hw hwY
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hb₀ (Or.inr hwY)
    · rcases List.mem_cons.mp hw with rfl | hwP
      · exact ha₀ (Or.inr hwY)
      · exact Set.disjoint_left.mp hFY (hPF w hwP) hwY
  exact no_pair_neighbor_in_path_interior G hG Y hY P a b a₀ b₀ y₁ y₂
    hP hP3 hC hCY ha₀Y hb₀Y hy₁Y hy₂Y hy₁y₂ hy₁a hy₁b hy₂b hy₂a
    ha₀P hb₀P

/-- The two connected deletion hypotheses provide a connected set avoiding both
ends, attached to both ends and containing any prescribed third vertex. -/
private theorem exists_connector_through
    (G : SimpleGraph V) (F : Set V) (a b x : V)
    (ha : a ∈ F) (hb : b ∈ F) (hx : x ∈ F)
    (hab : a ≠ b) (hax : a ≠ x) (hxb : x ≠ b)
    (hFa : ConnectedSet G (F \ {a})) (hFb : ConnectedSet G (F \ {b})) :
    ∃ S : Set V, S ⊆ F \ {a, b} ∧ ConnectedSet G S ∧ x ∈ S ∧
      (∃ u ∈ S, G.Adj a u) ∧ (∃ v ∈ S, G.Adj b v) := by
  have hxFa : x ∈ F \ {a} := ⟨hx, by simpa using hax.symm⟩
  have hbFa : b ∈ F \ {a} := ⟨hb, by simpa using hab.symm⟩
  obtain ⟨Q, hQ, hQsub⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hFa hxFa hbFa
  have haFb : a ∈ F \ {b} := ⟨ha, by simpa using hab⟩
  have hxFb : x ∈ F \ {b} := ⟨hx, by simpa using hxb⟩
  obtain ⟨R, hR, hRsub⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hFb haFb hxFb
  have hQ2 : 2 ≤ Q.length := two_le_length_of_ends_ne hQ hxb
  have hR2 : 2 ≤ R.length := two_le_length_of_ends_ne hR hax
  have hQdropPath : IsPathList G Q.dropLast := by
    rw [List.dropLast_eq_take]
    exact PathBasics.isPathList_take hQ.1 (by omega)
  have hRtailPath : IsPathList G R.tail := by
    rw [← List.drop_one]
    exact PathBasics.isPathList_drop hR.1 (by omega)
  let QS : Set V := {w : V | w ∈ Q.dropLast}
  let RS : Set V := {w : V | w ∈ R.tail}
  have hQSconn : ConnectedSet G QS :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQdropPath
  have hRSconn : ConnectedSet G RS :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hRtailPath
  have hQlast : Q.getLast hQ.1.1 = b := by
    simpa [List.getLast?_eq_some_getLast hQ.1.1] using hQ.2.2
  have hxQ : x ∈ Q := PathBasics.head_mem hQ.2.1
  have hxQD : x ∈ Q.dropLast :=
    (PathBasics.mem_dropLast_iff hQ.1.2.1 hQ.1.1).2
      ⟨hxQ, by simpa [hQlast] using hxb⟩
  have hxR : x ∈ R := PathBasics.getLast_mem hR.2.2
  have hxRT : x ∈ R.tail := by
    rcases R with _ | ⟨r, T⟩
    · simp at hR2
    · simp only [List.tail_cons]
      have hra : r = a := by simpa using hR.2.1
      rcases List.mem_cons.mp hxR with he | hm
      · exact False.elim (hax (hra.symm.trans he.symm))
      · exact hm
  let S : Set V := QS ∪ RS
  have hSconn : ConnectedSet G S :=
    ConnectedSetUnionAttach.connectedSet_union hQSconn hRSconn
      (Or.inl ⟨x, hxQD, hxRT⟩)
  have hSsub : S ⊆ F \ {a, b} := by
    intro w hw
    change w ∈ QS ∨ w ∈ RS at hw
    rcases hw with hw | hw
    · have hmem := (PathBasics.mem_dropLast_iff hQ.1.2.1 hQ.1.1).1 hw
      have hwFa := hQsub w hmem.1
      exact ⟨hwFa.1, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨by simpa using hwFa.2, by simpa [hQlast] using hmem.2⟩⟩
    · have hwR : w ∈ R := by
        change w ∈ R.tail at hw
        rcases R with _ | ⟨r, T⟩
        · simp only [List.tail_nil, List.not_mem_nil] at hw
        · exact List.mem_cons_of_mem r hw
      have hwFb := hRsub w hwR
      have hwa : w ≠ a := by
        intro he
        subst w
        rcases R with _ | ⟨r, T⟩
        · simp at hR2
        · have hra : r = a := by simpa using hR.2.1
          exact (List.nodup_cons.mp hR.1.2.1).1 (hra ▸ hw)
      exact ⟨hwFb.1, by simp [hwa, hwFb.2]⟩
  have hnextR : R[1]'(by omega) ∈ R.tail := by
    rcases R with _ | ⟨r, T⟩
    · simp at hR2
    · simp only [List.tail_cons, List.getElem_cons_succ]
      exact List.getElem_mem (by simpa using hR2)
  have haNext : G.Adj a (R[1]'(by omega)) := by
    have hadj := PathBasics.path_adj_succ hR.1 (i := 0) (by omega)
    have hR0 : R[0]'(by omega) = a :=
      PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
    simpa [hR0] using hadj
  let qprev := Q[Q.length - 2]'(by omega)
  have hqprevQ : qprev ∈ Q := List.getElem_mem _
  have hqprevne : qprev ≠ b := by
    intro he
    have hlast : Q[Q.length - 1]'(by omega) = b :=
      PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
    have := hQ.1.2.1.getElem_inj_iff.mp (he.trans hlast.symm)
    omega
  have hqprevD : qprev ∈ Q.dropLast :=
    (PathBasics.mem_dropLast_iff hQ.1.2.1 hQ.1.1).2
      ⟨hqprevQ, by simpa [hQlast] using hqprevne⟩
  have hbPrev : G.Adj b qprev := by
    have hadj := PathBasics.path_adj_succ hQ.1 (i := Q.length - 2) (by omega)
    have hlast : Q[Q.length - 1]'(by omega) = b :=
      PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
    have he : Q[Q.length - 2 + 1]'(by omega) = Q[Q.length - 1]'(by omega) :=
      gidx Q (by omega) _ _
    rw [he, hlast] at hadj
    exact hadj.symm
  exact ⟨S, hSsub, hSconn, Or.inl hxQD,
    ⟨R[1]'(by omega), Or.inr hnextR, haNext⟩,
    ⟨qprev, Or.inl hqprevD, hbPrev⟩⟩

/-- The property minimised in the last paragraph of the proof of 17.2. -/
private def GoodConnector (G : SimpleGraph V) (F : Set V)
    (a b y₁ y₂ : V) (S : Set V) : Prop :=
  S ⊆ F \ {a, b} ∧ ConnectedSet G S ∧
    (∃ u ∈ S, G.Adj a u) ∧ (∃ v ∈ S, G.Adj b v) ∧
    ((∃ w ∈ S, G.Adj y₁ w) ∨ ∃ w ∈ S, G.Adj y₂ w)

/-- The minimal connected set in 17.2 remains connected after deleting a chosen
hub-neighbour, and both hub vertices are anticomplete to what remains. -/
private theorem minimal_connector_delete
    (G : SimpleGraph V) (F : Set V) (a b y₁ y₂ : V)
    (haF : a ∈ F) (hbF : b ∈ F) (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (F₀ : Set V) (hF₀ : GoodConnector G F a b y₁ y₂ F₀)
    (hmin : ∀ S : Set V, GoodConnector G F a b y₁ y₂ S → F₀.ncard ≤ S.ncard)
    (x : V) (hxF₀ : x ∈ F₀) (hxy : G.Adj y₁ x ∨ G.Adj y₂ x)
    (hNo : ∀ (P : List V), IsPathFrom G P a b → (∀ w ∈ P, w ∈ F) →
      ¬ ∃ w ∈ SPGT.interior P, G.Adj y₁ w ∨ G.Adj y₂ w) :
    ConnectedSet G (F₀ \ {x}) ∧
      (∃ d ∈ F₀ \ {x}, G.Adj x d) ∧
      (∃ u ∈ F₀ \ {x}, G.Adj a u) ∧
      (∃ v ∈ F₀ \ {x}, G.Adj b v) ∧
      VertexAnticomplete G y₁ (F₀ \ {x}) ∧
      VertexAnticomplete G y₂ (F₀ \ {x}) := by
  rcases hF₀ with ⟨hF₀sub, hF₀conn, haAtt, hbAtt, hyAtt⟩
  have haF₀ : a ∉ F₀ := by
    intro ha
    exact (hF₀sub ha).2 (by simp)
  have hbF₀ : b ∉ F₀ := by
    intro hb
    exact (hF₀sub hb).2 (by simp)
  obtain ⟨P, hP, hP3, hPint, hKconn, haK, hbK⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hF₀conn hab hnab
      haF₀ hbF₀ haAtt hbAtt
  let K : Set V := {w : V | w ∈ SPGT.interior P}
  have hPF : ∀ w ∈ P, w ∈ F := by
    intro w hw
    by_cases hwa : w = a
    · simpa [hwa] using haF
    by_cases hwb : w = b
    · simpa [hwb] using hbF
    have hwK : w ∈ SPGT.interior P :=
      (PathBasics.mem_interior_iff_of_pathFrom hP).2 ⟨hw, hwa, hwb⟩
    exact (hF₀sub (hPint w hwK)).1
  have hxK : x ∉ K := by
    intro hx
    exact hNo P hP hPF ⟨x, hx, hxy⟩
  obtain ⟨k, hkK, hak⟩ := haK
  obtain ⟨l, hlK, hbl⟩ := hbK
  have hkF₀ : k ∈ F₀ := hPint k hkK
  obtain ⟨R, hR, hRF₀⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hF₀conn hxF₀ hkF₀
  have hxk : x ≠ k := fun he => hxK (by simpa [K, he] using hkK)
  have hR2 : 2 ≤ R.length := two_le_length_of_ends_ne hR hxk
  let T : Set V := {w : V | w ∈ R}
  have hTconn : ConnectedSet G T :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1
  let U : Set V := T ∪ K
  have hUconn : ConnectedSet G U :=
    ConnectedSetUnionAttach.connectedSet_union hTconn hKconn
      (Or.inl ⟨k, PathBasics.getLast_mem hR.2.2, hkK⟩)
  have hUsubF₀ : U ⊆ F₀ := by
    intro w hw
    change w ∈ T ∨ w ∈ K at hw
    rcases hw with hw | hw
    · exact hRF₀ w hw
    · exact hPint w hw
  have hxT : x ∈ T := PathBasics.head_mem hR.2.1
  have hUGood : GoodConnector G F a b y₁ y₂ U := by
    refine ⟨fun w hw => hF₀sub (hUsubF₀ hw), hUconn, ?_, ?_, ?_⟩
    · exact ⟨k, Or.inr hkK, hak⟩
    · exact ⟨l, Or.inr hlK, hbl⟩
    · rcases hxy with h | h
      · exact Or.inl ⟨x, Or.inl hxT, h⟩
      · exact Or.inr ⟨x, Or.inl hxT, h⟩
  have hUeq : U = F₀ :=
    Set.eq_of_subset_of_ncard_le hUsubF₀ (hmin U hUGood) (Set.toFinite _)
  have hRcons : R = x :: R.tail := by
    rcases R with _ | ⟨r, L⟩
    · simp at hR2
    · have hrx : r = x := by simpa using hR.2.1
      simp [hrx]
  have hxRT : x ∉ R.tail := by
    rw [hRcons] at hR
    exact (List.nodup_cons.mp hR.1.2.1).1
  have hRTpath : IsPathList G R.tail := by
    rw [← List.drop_one]
    exact PathBasics.isPathList_drop hR.1 (by omega)
  let RT : Set V := {w : V | w ∈ R.tail}
  have hRTconn : ConnectedSet G RT :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hRTpath
  have hkRT : k ∈ RT := by
    have hkR : k ∈ R := PathBasics.getLast_mem hR.2.2
    rw [hRcons] at hkR
    rcases List.mem_cons.mp hkR with he | hm
    · exact False.elim (hxk he.symm)
    · exact hm
  have hDconn : ConnectedSet G (RT ∪ K) :=
    ConnectedSetUnionAttach.connectedSet_union hRTconn hKconn
      (Or.inl ⟨k, hkRT, hkK⟩)
  have hDeq : F₀ \ {x} = RT ∪ K := by
    ext w
    constructor
    · intro hw
      have hwF₀ : w ∈ F₀ := hw.1
      rw [← hUeq] at hwF₀
      change w ∈ T ∨ w ∈ K at hwF₀
      rcases hwF₀ with hwR | hwK
      · change w ∈ R at hwR
        have hmem : w = x ∨ w ∈ R.tail := by
          rw [hRcons] at hwR
          exact List.mem_cons.mp hwR
        rcases hmem with he | hm
        · exact False.elim (hw.2 (by subst w; rfl))
        · exact Or.inl hm
      · exact Or.inr hwK
    · intro hw
      refine ⟨?_, ?_⟩
      · rw [← hUeq]
        change w ∈ T ∨ w ∈ K
        rcases hw with hwR | hwK
        · apply Or.inl
          change w ∈ R
          rw [hRcons]
          exact List.mem_cons_of_mem x hwR
        · exact Or.inr hwK
      · rcases hw with hwR | hwK
        · simp only [Set.mem_singleton_iff]
          intro he
          subst w
          exact hxRT hwR
        · simp only [Set.mem_singleton_iff]
          intro he
          subst w
          exact hxK hwK
  have hDconn' : ConnectedSet G (F₀ \ {x}) := by rw [hDeq]; exact hDconn
  have hnextRT : R[1]'(by omega) ∈ RT := by
    change R[1]'(by omega) ∈ R.tail
    rcases R with _ | ⟨r, L⟩
    · simp at hR2
    · simp only [List.tail_cons, List.getElem_cons_succ]
      exact List.getElem_mem (by simpa using hR2)
  have hxD : ∃ d ∈ F₀ \ {x}, G.Adj x d := by
    refine ⟨R[1]'(by omega), ?_, ?_⟩
    · rw [hDeq]
      exact Or.inl hnextRT
    · have hadj := PathBasics.path_adj_succ hR.1 (i := 0) (by omega)
      have hR0 : R[0]'(by omega) = x :=
        PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
      simpa [hR0] using hadj
  have haD : ∃ u ∈ F₀ \ {x}, G.Adj a u := by
    refine ⟨k, ⟨hPint k hkK, ?_⟩, hak⟩
    simpa using fun he => hxK (by simpa [K, he] using hkK)
  have hbD : ∃ v ∈ F₀ \ {x}, G.Adj b v := by
    refine ⟨l, ⟨hPint l hlK, ?_⟩, hbl⟩
    simpa using fun he => hxK (by simpa [K, he] using hlK)
  have anti_of (y : V) (hy : y = y₁ ∨ y = y₂) :
      VertexAnticomplete G y (F₀ \ {x}) := by
    intro w hwD hyw
    have hDGood : GoodConnector G F a b y₁ y₂ (F₀ \ {x}) := by
      refine ⟨fun z hz => hF₀sub hz.1, hDconn', haD, hbD, ?_⟩
      rcases hy with rfl | rfl
      · exact Or.inl ⟨w, hwD, hyw⟩
      · exact Or.inr ⟨w, hwD, hyw⟩
    have hlt : (F₀ \ {x}).ncard < F₀.ncard :=
      Set.ncard_diff_singleton_lt_of_mem hxF₀ (Set.toFinite F₀)
    exact (not_lt_of_ge (hmin (F₀ \ {x}) hDGood)) hlt
  exact ⟨hDconn', hxD, haD, hbD,
    anti_of y₁ (Or.inl rfl), anti_of y₂ (Or.inr rfl)⟩

/-- The final parity argument of 17.2, abstracted so that its two symmetric
applications (`x`--`b` and `x`--`a`) share all list bookkeeping. -/
private theorem force_end_edge
    (G : SimpleGraph V) (hBerge : Berge G) (D : Set V)
    (x e r s c d : V) (hxe : x ≠ e)
    (hD : ConnectedSet G D)
    (hxD : ∃ w ∈ D, G.Adj x w) (heD : ∃ w ∈ D, G.Adj e w)
    (hxOut : x ∉ D) (heOut : e ∉ D)
    (hrOut : r ∉ D) (hsOut : s ∉ D) (hcOut : c ∉ D) (hdOut : d ∉ D)
    (hreNe : r ≠ e) (hsxNe : s ≠ x)
    (hcxNe : c ≠ x) (hdxNe : d ≠ x) (hdeNe : d ≠ e)
    (hrx : G.Adj r x) (hre : ¬ G.Adj r e) (hse : G.Adj s e)
    (hrs : ¬ G.Adj r s)
    (hrD : VertexAnticomplete G r D) (hsD : VertexAnticomplete G s D)
    (hcr : G.Adj c r) (hce : G.Adj c e) (hcx : ¬ G.Adj c x)
    (hcD : VertexAnticomplete G c D)
    (hdr : G.Adj d r) (hds : G.Adj d s)
    (hdx : ¬ G.Adj d x) (hde : ¬ G.Adj d e)
    (hdD : VertexAnticomplete G d D) :
    G.Adj s x ∧ G.Adj x e := by
  obtain ⟨Q, hQ, hQint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hD hxOut heOut hxD heD
  have hQ2 : 2 ≤ Q.length := two_le_length_of_ends_ne hQ hxe
  have hQlen1 : 1 ≤ pathLength Q := by simp only [pathLength]; omega
  have not_mem_Q (z : V) (hzx : z ≠ x) (hze : z ≠ e) (hzD : z ∉ D) : z ∉ Q := by
    intro hzQ
    have hzInt : z ∈ SPGT.interior Q :=
      (PathBasics.mem_interior_iff_of_pathFrom hQ).2 ⟨hzQ, hzx, hze⟩
    exact hzD (hQint z hzInt)
  have hrQ : r ∉ Q := not_mem_Q r hrx.ne hreNe hrOut
  have hsQ : s ∉ Q := not_mem_Q s hsxNe hse.ne hsOut
  have hcQ : c ∉ Q := not_mem_Q c hcxNe hce.ne hcOut
  have hdQ : d ∉ Q := not_mem_Q d hdxNe hdeNe hdOut
  have hC₁ : IsHoleList G (c :: r :: Q) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hQ hQlen1 hrx hce hcr.symm
      hrQ hcQ hre hcx ?_ ?_
    · intro w hw
      exact hrD w (hQint w hw)
    · intro w hw
      exact hcD w (hQint w hw)
  have hQodd : Odd (pathLength Q) := by
    have hev := hBerge.1 _ hC₁
    rw [PrismBasics.holeLength_cons_cons r c (PathBasics.path_ne_nil hQ.1)] at hev
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 2, by omega⟩
  have hsx : G.Adj s x := by
    by_contra hnsx
    have hrOther : ∀ w ∈ Q, w ≠ x → ¬ G.Adj r w := by
      intro w hwQ hwx
      by_cases hwe : w = e
      · simpa [hwe] using hre
      have hwInt : w ∈ SPGT.interior Q :=
        (PathBasics.mem_interior_iff_of_pathFrom hQ).2 ⟨hwQ, hwx, hwe⟩
      exact hrD w (hQint w hwInt)
    have hRQ : IsPathFrom G (r :: Q) r e :=
      PathAttach.isPathFrom_cons hQ hrx hrQ hrOther
    have hsr : s ≠ r := by
      intro heq
      exact hre (heq ▸ hse)
    have hdRQ : d ∉ r :: Q := by
      intro hm
      rcases List.mem_cons.mp hm with heq | hmQ
      · exact hdr.ne heq
      · exact hdQ hmQ
    have hsRQ : s ∉ r :: Q := by
      intro hm
      rcases List.mem_cons.mp hm with heq | hmQ
      · exact hsr heq
      · exact hsQ hmQ
    have intRQ_Q : ∀ w ∈ SPGT.interior (r :: Q), w ∈ Q ∧ w ≠ e := by
      intro w hw
      have hi := (PathBasics.mem_interior_iff_of_pathFrom hRQ).1 hw
      rcases List.mem_cons.mp hi.1 with heq | hwQ
      · exact False.elim (hi.2.1 heq)
      · exact ⟨hwQ, hi.2.2⟩
    have hdInt : ∀ w ∈ SPGT.interior (r :: Q), ¬ G.Adj d w := by
      intro w hw
      obtain ⟨hwQ, hwe⟩ := intRQ_Q w hw
      by_cases hwx : w = x
      · simpa [hwx] using hdx
      have hwInt : w ∈ SPGT.interior Q :=
        (PathBasics.mem_interior_iff_of_pathFrom hQ).2 ⟨hwQ, hwx, hwe⟩
      exact hdD w (hQint w hwInt)
    have hsInt : ∀ w ∈ SPGT.interior (r :: Q), ¬ G.Adj s w := by
      intro w hw
      obtain ⟨hwQ, hwe⟩ := intRQ_Q w hw
      by_cases hwx : w = x
      · simpa [hwx] using hnsx
      have hwInt : w ∈ SPGT.interior Q :=
        (PathBasics.mem_interior_iff_of_pathFrom hQ).2 ⟨hwQ, hwx, hwe⟩
      exact hsD w (hQint w hwInt)
    have hC₂ : IsHoleList G (s :: d :: r :: Q) := by
      refine PrismBasics.isHoleList_of_path_add_two_vertices hRQ (by
        rw [PathBasics.pathLength_cons]
        omega) hdr hse hds hdRQ hsRQ hde (fun hadj => hrs hadj.symm) hdInt hsInt
    have hev := hBerge.1 _ hC₂
    rw [PrismBasics.holeLength_cons_cons d s (PathBasics.path_ne_nil hRQ.1)] at hev
    have hlenRQ : pathLength (r :: Q) = pathLength Q + 1 := by
      rw [PathBasics.pathLength_cons, PathBasics.length_eq_pathLength_add_one hQ.1]
    rw [hlenRQ] at hev
    obtain ⟨k, hk⟩ := hQodd
    obtain ⟨l, hl⟩ := hev
    omega
  have hxeAdj : G.Adj x e := by
    by_contra hnxe
    have hshort : ¬ 2 ≤ pathLength Q := by
      intro hlong
      have hC₃ : IsHoleList G (s :: Q) :=
        PrismBasics.isHoleList_of_path_add_vertex hQ hlong hsx hse hsQ
          (fun w hw => hsD w (hQint w hw))
      have hev := hBerge.1 _ hC₃
      rw [PrismBasics.holeLength_cons s (PathBasics.path_ne_nil hQ.1)] at hev
      obtain ⟨k, hk⟩ := hQodd
      obtain ⟨l, hl⟩ := hev
      omega
    have hQlen : Q.length = 2 := by
      rw [PathBasics.length_eq_pathLength_add_one hQ.1]
      omega
    have hadj := PathBasics.path_adj_succ hQ.1 (i := 0) (by omega)
    have hQ0 : Q[0]'(by omega) = x :=
      PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
    have hQ1 : Q[1]'(by omega) = e := by
      have hlast := PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
      have heq : Q[1]'(by omega) = Q[Q.length - 1]'(by omega) :=
        gidx Q (by omega) _ _
      exact heq.trans hlast
    rw [hQ0, hQ1] at hadj
    exact hnxe hadj
  exact ⟨hsx, hxeAdj⟩

/-- Once claim (1) has supplied the two nonadjacent vertices, the last paragraph
of 17.2 shows that the first has no neighbour in `F \ {a}`. -/
private theorem firstNoExtra
    (G : SimpleGraph V) (hG : InF7 G) (F Y : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F) (hY : AnticonnectedSet G Y)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (ha : a ∈ F) (hb : b ∈ F)
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (haY : ¬ VertexComplete G a Y) (hbY : ¬ VertexComplete G b Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (hFa : ConnectedSet G (F \ {a})) (hFb : ConnectedSet G (F \ {b}))
    (y₁ y₂ : V) (hy₁Y : y₁ ∈ Y) (hy₂Y : y₂ ∈ Y)
    (hy₁y₂ : ¬ G.Adj y₁ y₂)
    (hy₁a : G.Adj y₁ a) (hy₁b : ¬ G.Adj y₁ b)
    (hy₂b : G.Adj y₂ b) (hy₂a : ¬ G.Adj y₂ a) :
    VertexAnticomplete G y₁ (F \ {a}) := by
  classical
  have haa₀ : G.Adj a a₀ := (hpath.2.2 0 1 (by simp) (by simp)).2 (by simp)
  have ha₀b₀ : G.Adj a₀ b₀ := (hpath.2.2 1 2 (by simp) (by simp)).2 (by simp)
  have hb₀b : G.Adj b₀ b := (hpath.2.2 2 3 (by simp) (by simp)).2 (by simp)
  have hnab : ¬ G.Adj a b := by
    intro hadj
    have := (hpath.2.2 0 3 (by simp) (by simp)).1 hadj
    simp at this
  have hna₀b : ¬ G.Adj a₀ b := by
    intro hadj
    have := (hpath.2.2 1 3 (by simp) (by simp)).1 hadj
    simp at this
  have hnb₀a : ¬ G.Adj b₀ a := by
    intro hadj
    have := (hpath.2.2 0 2 (by simp) (by simp)).1 hadj.symm
    simp at this
  have hfour : IsPathFrom G [a, a₀, b₀, b] a b := ⟨hpath, by simp, by simp⟩
  have hab : a ≠ b := PathBasics.isPathFrom_ends_ne hfour (by simp [pathLength])
  by_contra hnone
  have hExtra : ∃ f ∈ F \ {a}, G.Adj y₁ f := by
    by_contra hnoExtra
    apply hnone
    intro f hf hadj
    exact hnoExtra ⟨f, hf, hadj⟩
  have hNoPath : ∀ (P : List V), IsPathFrom G P a b → (∀ w ∈ P, w ∈ F) →
      ¬ ∃ w ∈ SPGT.interior P, G.Adj y₁ w ∨ G.Adj y₂ w := by
    intro P hP hPF
    exact no_pair_neighbor_in_F_path G hG F Y hFY hY a₀ b₀ a b ha₀ hb₀ hpath
      ha₀Y hb₀Y ha₀F hb₀F y₁ y₂ hy₁Y hy₂Y hy₁y₂ hy₁a hy₁b
      hy₂b hy₂a P hP hPF
  obtain ⟨x, hxFa, hy₁x⟩ := hExtra
  have hxa : a ≠ x := by
    have hxa' : x ≠ a := by simpa using hxFa.2
    exact hxa'.symm
  have hxb : x ≠ b := by
    intro he
    exact hy₁b (he ▸ hy₁x)
  obtain ⟨S, hSsub, hSconn, hxS, haS, hbS⟩ :=
    exists_connector_through G F a b x ha hb hxFa.1 hab hxa hxb hFa hFb
  have hSGood : GoodConnector G F a b y₁ y₂ S :=
    ⟨hSsub, hSconn, haS, hbS, Or.inl ⟨x, hxS, hy₁x⟩⟩
  obtain ⟨F₀, hF₀, hmin⟩ :=
    ExtremalChoice.exists_min_nat (GoodConnector G F a b y₁ y₂) Set.ncard
      ⟨S, hSGood⟩
  obtain ⟨x₀, hx₀F₀, hx₀y⟩ :
      ∃ x₀ ∈ F₀, G.Adj y₁ x₀ ∨ G.Adj y₂ x₀ := by
    rcases hF₀.2.2.2.2 with h | h
    · obtain ⟨x₀, hx₀, hyx₀⟩ := h
      exact ⟨x₀, hx₀, Or.inl hyx₀⟩
    · obtain ⟨x₀, hx₀, hyx₀⟩ := h
      exact ⟨x₀, hx₀, Or.inr hyx₀⟩
  obtain ⟨hDconn, hx₀D, haD, hbD, hy₁D, hy₂D⟩ :=
    minimal_connector_delete G F a b y₁ y₂ ha hb hab hnab F₀ hF₀ hmin
      x₀ hx₀F₀ hx₀y hNoPath
  let D : Set V := F₀ \ {x₀}
  have hF₀sub : F₀ ⊆ F \ {a, b} := hF₀.1
  have hx₀pair := hF₀sub hx₀F₀
  have hx₀F : x₀ ∈ F := hx₀pair.1
  have hx₀a : x₀ ≠ a := by
    intro he
    exact hx₀pair.2 (by simp [he])
  have hx₀b : x₀ ≠ b := by
    intro he
    exact hx₀pair.2 (by simp [he])
  have hDsubF : D ⊆ F := by
    intro w hw
    exact (hF₀sub hw.1).1
  have haDout : a ∉ D := by
    intro hw
    exact (hF₀sub hw.1).2 (by simp)
  have hbDout : b ∉ D := by
    intro hw
    exact (hF₀sub hw.1).2 (by simp)
  have hx₀Dout : x₀ ∉ D := by simp [D]
  have hy₁Fout : y₁ ∉ F := fun hyF => Set.disjoint_left.mp hFY hyF hy₁Y
  have hy₂Fout : y₂ ∉ F := fun hyF => Set.disjoint_left.mp hFY hyF hy₂Y
  have hy₁Dout : y₁ ∉ D := fun hyD => hy₁Fout (hDsubF hyD)
  have hy₂Dout : y₂ ∉ D := fun hyD => hy₂Fout (hDsubF hyD)
  have ha₀Fout : a₀ ∉ F := fun h => ha₀ (Or.inl h)
  have hb₀Fout : b₀ ∉ F := fun h => hb₀ (Or.inl h)
  have ha₀Dout : a₀ ∉ D := fun h => ha₀Fout (hDsubF h)
  have hb₀Dout : b₀ ∉ D := fun h => hb₀Fout (hDsubF h)
  have hy₁x₀ne : y₁ ≠ x₀ := fun he => hy₁Fout (he ▸ hx₀F)
  have hy₂x₀ne : y₂ ≠ x₀ := fun he => hy₂Fout (he ▸ hx₀F)
  have ha₀x₀ne : a₀ ≠ x₀ := fun he => ha₀Fout (he ▸ hx₀F)
  have hb₀x₀ne : b₀ ≠ x₀ := fun he => hb₀Fout (he ▸ hx₀F)
  have ha₀bne : a₀ ≠ b := fun he => ha₀Fout (he ▸ hb)
  have hb₀ane : b₀ ≠ a := fun he => hb₀Fout (he ▸ ha)
  have hy₁bne : y₁ ≠ b := by
    intro he
    exact hnab (by simpa [he] using hy₁a.symm)
  have hy₂ane : y₂ ≠ a := by
    intro he
    exact hnab (by simpa [he] using hy₂b)
  have ha₀_no (w : V) (hwF : w ∈ F) (hwa : w ≠ a) : ¬ G.Adj a₀ w := by
    intro hadj
    have hm : w ∈ {f ∈ F | G.Adj a₀ f} := ⟨hwF, hadj⟩
    rw [ha₀F] at hm
    exact hwa (by simpa using hm)
  have hb₀_no (w : V) (hwF : w ∈ F) (hwb : w ≠ b) : ¬ G.Adj b₀ w := by
    intro hadj
    have hm : w ∈ {f ∈ F | G.Adj b₀ f} := ⟨hwF, hadj⟩
    rw [hb₀F] at hm
    exact hwb (by simpa using hm)
  have ha₀x₀ : ¬ G.Adj a₀ x₀ := ha₀_no x₀ hx₀F hx₀a
  have hb₀x₀ : ¬ G.Adj b₀ x₀ := hb₀_no x₀ hx₀F hx₀b
  have ha₀D : VertexAnticomplete G a₀ D := by
    intro w hw
    exact ha₀_no w (hDsubF hw) (fun he => haDout (he.symm ▸ hw))
  have hb₀D : VertexAnticomplete G b₀ D := by
    intro w hw
    exact hb₀_no w (hDsubF hw) (fun he => hbDout (he.symm ▸ hw))
  change ConnectedSet G D at hDconn
  change (∃ w ∈ D, G.Adj x₀ w) at hx₀D
  change (∃ w ∈ D, G.Adj a w) at haD
  change (∃ w ∈ D, G.Adj b w) at hbD
  change VertexAnticomplete G y₁ D at hy₁D
  change VertexAnticomplete G y₂ D at hy₂D
  have forceB (hy₁x : G.Adj y₁ x₀) : G.Adj y₂ x₀ ∧ G.Adj x₀ b := by
    exact force_end_edge G hG.1.1.1.1 D x₀ b y₁ y₂ b₀ a₀ hx₀b hDconn
      hx₀D hbD hx₀Dout hbDout hy₁Dout hy₂Dout hb₀Dout ha₀Dout
      hy₁bne hy₂x₀ne hb₀x₀ne ha₀x₀ne ha₀bne hy₁x hy₁b hy₂b
      hy₁y₂ hy₁D hy₂D (hb₀Y y₁ hy₁Y) hb₀b hb₀x₀ hb₀D
      (ha₀Y y₁ hy₁Y) (ha₀Y y₂ hy₂Y) ha₀x₀ hna₀b ha₀D
  have forceA (hy₂x : G.Adj y₂ x₀) : G.Adj y₁ x₀ ∧ G.Adj x₀ a := by
    exact force_end_edge G hG.1.1.1.1 D x₀ a y₂ y₁ a₀ b₀ hx₀a hDconn
      hx₀D haD hx₀Dout haDout hy₂Dout hy₁Dout ha₀Dout hb₀Dout
      hy₂ane hy₁x₀ne ha₀x₀ne hb₀x₀ne hb₀ane hy₂x hy₂a hy₁a
      (fun hadj => hy₁y₂ hadj.symm) hy₂D hy₁D (ha₀Y y₂ hy₂Y) haa₀.symm
      ha₀x₀ ha₀D (hb₀Y y₂ hy₂Y) (hb₀Y y₁ hy₁Y) hb₀x₀ hnb₀a hb₀D
  have hx₀ends : G.Adj x₀ a ∧ G.Adj x₀ b := by
    rcases hx₀y with hy₁x | hy₂x
    · obtain ⟨hy₂x, hx₀b'⟩ := forceB hy₁x
      exact ⟨(forceA hy₂x).2, hx₀b'⟩
    · obtain ⟨hy₁x, hx₀a'⟩ := forceA hy₂x
      exact ⟨hx₀a', (forceB hy₁x).2⟩
  have hx₀a₀ : x₀ ≠ a₀ := ha₀x₀ne.symm
  have hx₀b₀ : x₀ ≠ b₀ := hb₀x₀ne.symm
  have hx₀P : x₀ ∉ [a, a₀, b₀, b] := by
    simp [hx₀a, hx₀a₀, hx₀b₀, hx₀b]
  have hx₀int : ∀ w ∈ SPGT.interior [a, a₀, b₀, b], ¬ G.Adj x₀ w := by
    intro w hw
    simp [SPGT.interior] at hw
    rcases hw with rfl | rfl
    · exact fun hadj => ha₀x₀ hadj.symm
    · exact fun hadj => hb₀x₀ hadj.symm
  have hfive : IsHoleList G (x₀ :: [a, a₀, b₀, b]) :=
    PrismBasics.isHoleList_of_path_add_vertex hfour (by simp [pathLength])
      hx₀ends.1 hx₀ends.2 hx₀P hx₀int
  have hev : Even (holeLength (x₀ :: [a, a₀, b₀, b])) :=
    hG.1.1.1.1.1 _ hfive
  norm_num [holeLength] at hev

/-- The conclusion of 17.2.  Claim (1) gives the two nonadjacent vertices.
Applying the last paragraph in both orientations shows that their only
neighbours in `F` are the corresponding ends. -/
theorem main
    (G : SimpleGraph V) (hG : InF7 G) (F Y : Set V)
    (hFY : Disjoint F Y) (hF : ConnectedSet G F) (hY : AnticonnectedSet G Y)
    (a₀ b₀ a b : V) (ha₀ : a₀ ∉ F ∪ Y) (hb₀ : b₀ ∉ F ∪ Y)
    (ha : a ∈ F) (hb : b ∈ F)
    (hpath : IsPathList G [a, a₀, b₀, b])
    (ha₀Y : VertexComplete G a₀ Y) (hb₀Y : VertexComplete G b₀ Y)
    (haY : ¬ VertexComplete G a Y) (hbY : ¬ VertexComplete G b Y)
    (ha₀F : {f ∈ F | G.Adj a₀ f} = {a})
    (hb₀F : {f ∈ F | G.Adj b₀ f} = {b})
    (hFa : ConnectedSet G (F \ {a})) (hFb : ConnectedSet G (F \ {b})) :
    (∃ y ∈ Y, VertexAnticomplete G y F) ∨
    (∃ y₁ ∈ Y, ∃ y₂ ∈ Y, ¬ G.Adj y₁ y₂ ∧
      {f ∈ F | G.Adj y₁ f} = {a} ∧ {f ∈ F | G.Adj y₂ f} = {b}) := by
  classical
  by_cases hfirst : ∃ y ∈ Y, VertexAnticomplete G y F
  · exact Or.inl hfirst
  · right
    have hEvery : ∀ y ∈ Y, ∃ f ∈ F, G.Adj y f := by
      intro y hy
      by_contra hnone
      apply hfirst
      refine ⟨y, hy, ?_⟩
      intro f hf hadj
      exact hnone ⟨f, hf, hadj⟩
    obtain ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁y₂, hy₁a, hy₁b, hy₂b, hy₂a⟩ :=
      exists_opposite_end_pair G hG F Y hFY hF hY a₀ b₀ a b ha₀ hb₀ ha hb
        hpath ha₀Y hb₀Y haY hbY ha₀F hb₀F hEvery
    have hy₁anti : VertexAnticomplete G y₁ (F \ {a}) :=
      firstNoExtra G hG F Y hFY hF hY a₀ b₀ a b ha₀ hb₀ ha hb hpath
        ha₀Y hb₀Y haY hbY ha₀F hb₀F hFa hFb y₁ y₂ hy₁Y hy₂Y hy₁y₂
        hy₁a hy₁b hy₂b hy₂a
    have hpathRev : IsPathList G [b, b₀, a₀, a] := by
      simpa using PathBasics.isPathList_reverse hpath
    have hy₂anti : VertexAnticomplete G y₂ (F \ {b}) :=
      firstNoExtra G hG F Y hFY hF hY b₀ a₀ b a hb₀ ha₀ hb ha hpathRev
        hb₀Y ha₀Y hbY haY hb₀F ha₀F hFb hFa y₂ y₁ hy₂Y hy₁Y
        (fun hadj => hy₁y₂ hadj.symm) hy₂b hy₂a hy₁a hy₁b
    have hy₁set : {f ∈ F | G.Adj y₁ f} = ({a} : Set V) := by
      ext f
      constructor
      · intro hf
        have hfa : f = a := by
          by_contra hne
          exact hy₁anti f ⟨hf.1, by simpa using hne⟩ hf.2
        simpa [hfa]
      · intro hf
        have hfa : f = a := by simpa using hf
        subst f
        exact ⟨ha, hy₁a⟩
    have hy₂set : {f ∈ F | G.Adj y₂ f} = ({b} : Set V) := by
      ext f
      constructor
      · intro hf
        have hfb : f = b := by
          by_contra hne
          exact hy₂anti f ⟨hf.1, by simpa using hne⟩ hf.2
        simpa [hfb]
      · intro hf
        have hfb : f = b := by simpa using hf
        subst f
        exact ⟨hb, hy₂b⟩
    exact ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁y₂, hy₁set, hy₂set⟩

end Workspace.ProofLemmas.Thm172Core
