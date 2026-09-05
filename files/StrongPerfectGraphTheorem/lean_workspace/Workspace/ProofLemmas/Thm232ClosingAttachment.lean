import Workspace.ProofLemmas.Thm232ClosingTriples
import Workspace.ProofLemmas.Thm232ClosingPath
import Workspace.Types.WheelSystems
import Workspace.Statements.S16.Thm_16_2

/-! Apply 16.2 in the last paragraph of 23.2 and identify its third outcome. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingAttachment

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Decode a rim triple in either of the orientations allowed by 16.2. -/
theorem triple_neighbours {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C)
    {a b c : V} (hblock : ∃ k, [a,b,c] <+: C.rotate k ∨ [c,b,a] <+: C.rotate k) :
    a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ IsRimNeighbours G C b a c := by
  obtain ⟨k, h | h⟩ := hblock
  · exact hole_triple hC ⟨k, h⟩
  · obtain ⟨hc, hb, ha, hn⟩ := hole_triple hC ⟨k, h⟩
    exact ⟨ha, hb, hc, isRimNeighbours_symm hn⟩

/-- The third outcome of 16.2 must go between `p,q`: its ends attach to `F`,
so neither is the anticomplete vertex `x`.  Its middle vertex is therefore `x`.
The first two outcomes are excluded by optimality and anticompleteness. -/
theorem path_from_attachments {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y F : Set V} (hopt : OptimalWheel G C Y)
    {x p q u v : V} (hnd : [u,p,x,q,v].Nodup)
    (hexh : ∀ a b : V, a ∈ C → b ∈ C → EdgeComplete G Y a b →
      ({a,b} : Set V) = {x,p} ∨ ({a,b} : Set V) = {p,u} ∨
      ({a,b} : Set V) = {v,q} ∨ ({a,b} : Set V) = {q,x})
    (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y)
    (hFconn : ConnectedSet G F) (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (hxF : VertexAnticomplete G x F)
    (hopp : ∃ a ∈ attachments G F {c : V | c ∈ C},
      ∃ b ∈ attachments G F {c : V | c ∈ C}, OppositeWheelParity G C Y a b)
    (hnadj : ∃ a ∈ attachments G F {c : V | c ∈ C},
      ∃ b ∈ attachments G F {c : V | c ∈ C}, a ≠ b ∧ ¬ G.Adj a b) :
    ∃ Q : List V, IsPathFrom G Q p q ∧ (∀ f ∈ SPGT.interior Q, f ∈ F) ∧
      (∀ c ∈ C, ∀ f ∈ SPGT.interior Q, G.Adj c f → c = p ∨ c = q) := by
  have hw := hopt.1
  have hshape : ∀ a b c : V,
      (∃ k, [a,b,c] <+: C.rotate k ∨ [c,b,a] <+: C.rotate k) →
      VertexComplete G a Y → VertexComplete G b Y → VertexComplete G c Y →
      a = x ∨ c = x ∨ (b = x ∧ ((a = p ∧ c = q) ∨ (a = q ∧ c = p))) := by
    intro a b c hblock haY hbY hcY
    obtain ⟨haC, hbC, hcC, hn⟩ := triple_neighbours hw.1.1 hblock
    exact Thm232ClosingTriples.triple_shape hnd hn.1
      (hexh a b haC hbC ⟨hn.2.2.2.1.symm, haY, hbY⟩)
      (hexh b c hbC hcC ⟨hn.2.2.2.2.1, hbY, hcY⟩)
  rcases Workspace.Statements.S16.SPGT.thm_16_2 G hG C Y hw F hFC hFY hFconn hFnc
      _ rfl hopp hnadj with ⟨f, hf, hnew⟩ | hsecond | hthird
  · exact (hopt.2 ⟨C, Y ∪ {f}, hnew, Set.subset_union_left,
      fun hsub => hFY f hf (hsub (Or.inr rfl))⟩).elim
  · obtain ⟨f, hf, _, a, b, c, _, hblock, ha, hb, hc, _⟩ := hsecond
    have haY : VertexComplete G a Y := fun t ht => ha t (Or.inl ht)
    have hbY : VertexComplete G b Y := fun t ht => hb t (Or.inl ht)
    have hcY : VertexComplete G c Y := fun t ht => hc t (Or.inl ht)
    rcases hshape a b c hblock haY hbY hcY with he | he | ⟨he, _⟩
    · exact (hxF f hf (he ▸ ha f (Or.inr rfl))).elim
    · exact (hxF f hf (he ▸ hc f (Or.inr rfl))).elim
    · exact (hxF f hf (he ▸ hb f (Or.inr rfl))).elim
  · obtain ⟨a, b, c, hblock, haY, hbY, hcY, P, hP, hPF, hiso⟩ := hthird
    obtain ⟨haC, hbC, hcC, hn⟩ := triple_neighbours hw.1.1 hblock
    have hPpos := PathBasics.path_length_pos hP.1
    have hP2 : 2 ≤ P.length := by
      by_contra hh
      have hfirst := PathBasics.getElem_zero_of_head? hP.2.1 hPpos
      have hlast := PathBasics.getElem_last_of_getLast? hP.2.2 hPpos
      exact hn.1 (hfirst.symm.trans ((hP.1.2.1.getElem_inj_iff.mpr (by omega)).trans hlast))
    have hP3 : 3 ≤ P.length := by
      by_contra hh
      exact rimNeighbours_not_adj hw.1.1 hbC hn
        (PathBasics.isPathFrom_ends_adj_of_length_one hP (by change P.length - 1 = 1; omega))
    have hax : a ≠ x := by
      intro he
      obtain ⟨f, hf, haf⟩ := Thm232ClosingPath.end_attaches hP hP3
      exact hxF f (hPF f hf) (he ▸ haf)
    have hcx : c ≠ x := by
      intro he
      obtain ⟨f, hf, hcf⟩ := Thm232ClosingPath.end_attaches
        (PathBasics.isPathFrom_reverse hP) (by simpa using hP3)
      exact hxF f (hPF f (PathBasics.mem_interior_reverse.mp hf)) (he ▸ hcf)
    have hclean : ∀ d ∈ C, ∀ f ∈ SPGT.interior P, G.Adj d f → d = a ∨ d = c := by
      intro d hd f hf hadj
      have hbx : b = x := ((hshape a b c hblock haY hbY hcY).resolve_left hax).resolve_left hcx |>.1
      by_cases hda : d = a
      · exact Or.inl hda
      by_cases hdc : d = c
      · exact Or.inr hdc
      have hdb : d ≠ b := fun he => hxF f (hPF f hf) ((he.trans hbx) ▸ hadj)
      exact (hiso f hf d hd hda hdb hdc hadj.symm).elim
    have hends := (((hshape a b c hblock haY hbY hcY).resolve_left hax).resolve_left hcx).2
    rcases hends with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · refine ⟨P, ?_, hPF, ?_⟩
      · simpa only [ha, hc] using hP
      · simpa only [ha, hc] using hclean
    · refine ⟨P.reverse, ?_, ?_, ?_⟩
      · simpa only [ha, hc] using PathBasics.isPathFrom_reverse hP
      · exact fun f hf => hPF f (PathBasics.mem_interior_reverse.mp hf)
      · intro d hd f hf hadj
        simpa only [ha, hc, or_comm] using hclean d hd f (PathBasics.mem_interior_reverse.mp hf) hadj

/-- Use the initial part of `T` outside the rim.  If it has only `p,q` as
attachments, it is already the required path.  Otherwise 16.2 applies. -/
theorem path_from_initial_path {G : SimpleGraph V} (hG : InF6 G)
    {C T : List V} {Y : Set V} (hopt : OptimalWheel G C Y)
    {x p q u v w : V} (hnd : [u,p,x,q,v].Nodup)
    (hpC : p ∈ C) (hp : IsRimNeighbours G C p x u)
    (hexh : ∀ a b : V, a ∈ C → b ∈ C → EdgeComplete G Y a b →
      ({a,b} : Set V) = {x,p} ∨ ({a,b} : Set V) = {p,u} ∨
      ({a,b} : Set V) = {v,q} ∨ ({a,b} : Set V) = {q,x})
    (hpar : ∀ c ∈ C, c ≠ p → c ≠ q → OppositeWheelParity G C Y c p)
    (hT : IsPathFrom G T p w) (hwC : w ∈ C) (hwp : w ≠ p)
    (havoid : ∀ a ∈ T, a ≠ x ∧ a ≠ u)
    (hint : ∀ a ∈ SPGT.interior T, a ∉ Y ∧ ¬ VertexComplete G a Y)
    (hxF : VertexAnticomplete G x {a : V | a ∈ SPGT.interior T}) :
    ∃ Q : List V, IsPathFrom G Q p q ∧
      (∀ a ∈ SPGT.interior Q, a ∈ SPGT.interior T) ∧
      (∀ c ∈ C, ∀ a ∈ SPGT.interior Q, G.Adj c a → c = p ∨ c = q) := by
  classical
  obtain ⟨P, b, hP, hP3, hbC, hbp, hpb, hPT, hPC⟩ :=
    Thm232ClosingPath.first_rim_path hopt.1.1.1 hpC hp hT hwC hwp havoid
  let F : Set V := {a : V | a ∈ SPGT.interior P}
  have hpF : p ∈ attachments G F {c : V | c ∈ C} :=
    ⟨hpC, Thm232ClosingPath.end_attaches hP hP3⟩
  have hbF : b ∈ attachments G F {c : V | c ∈ C} := by
    obtain ⟨a, ha, hba⟩ := Thm232ClosingPath.end_attaches
      (PathBasics.isPathFrom_reverse hP) (by simpa using hP3)
    exact ⟨hbC, a, PathBasics.mem_interior_reverse.mp ha, hba⟩
  by_cases hall : ∀ c ∈ attachments G F {c : V | c ∈ C}, c = p ∨ c = q
  · have hbq : b = q := (hall b hbF).resolve_left hbp
    refine ⟨P, ?_, hPT, ?_⟩
    · simpa only [hbq] using hP
    · exact fun c hc a ha hca => hall c ⟨hc, a, ha, hca⟩
  · push Not at hall
    obtain ⟨c, hc, hcp, hcq⟩ := hall
    have hconn : ConnectedSet G F := by
      change ConnectedSet G {a : V | a ∈ SPGT.interior P}
      rw [PathBasics.interior_eq_drop_take]
      exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain
        (((InducedPathExtraction.isChain_of_isPathList hP.1).drop 1).take (P.length - 2))
    obtain ⟨Q, hQ, hQF, hQiso⟩ := path_from_attachments hG hopt hnd hexh hPC
      (fun a ha => (hint a (hPT a ha)).1) hconn
      (fun a ha => (hint a (hPT a ha)).2) (fun a ha => hxF a (hPT a ha))
      ⟨c, hc, p, hpF, hpar c hc.1 hcp hcq⟩ ⟨p, hpF, b, hbF, hbp.symm, hpb⟩
    exact ⟨Q, hQ, fun a ha => hPT a (hQF a ha), hQiso⟩

end Workspace.ProofLemmas.Thm232ClosingAttachment
