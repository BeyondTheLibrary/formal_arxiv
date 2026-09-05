import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.Thm182DropLastIndex
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm174RRStrip

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm174Main

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem gidx {W : Type*} (l : List W) {i j : ℕ}
    (hij : i = j) (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst j
  rfl

private theorem path_shape_of_first_interior
    {H : SimpleGraph V} {q : List V} {a b x : V}
    (hq : IsPathFrom H q a b)
    (hx : (SPGT.interior q).head? = some x) :
    ∃ t : List V, q = a :: (x :: t ++ [b]) := by
  rcases q with _ | ⟨u, l⟩
  · simp [IsPathFrom, IsPathList] at hq
  have hua : u = a := by simpa using hq.2.1
  subst u
  have hdrop : l.dropLast.head? = some x := by simpa [SPGT.interior] using hx
  cases hdl : l.dropLast with
  | nil =>
      rw [hdl] at hdrop
      simp at hdrop
  | cons v t =>
      rw [hdl] at hdrop
      have hvx : v = x := by simpa using hdrop
      subst v
      have hlne : l ≠ [] := by
        intro hl
        subst l
        simp at hdl
      have hlastl : l.getLast? = some b := by
        simpa [List.getLast?_cons_of_ne_nil hlne] using hq.2.2
      have hsplit : l.dropLast ++ [b] = l :=
        List.dropLast_append_getLast? b (by simpa using hlastl)
      refine ⟨t, ?_⟩
      calc
        a :: l = a :: (l.dropLast ++ [b]) := congrArg (List.cons a) hsplit.symm
        _ = a :: (x :: t ++ [b]) := by rw [hdl]

private theorem prefix_shape_two_last
    {G : SimpleGraph V} {p : List V} {a b c : V} (hp : IsPathFrom G p a c)
    (hlen : 3 ≤ p.length)
    (hlast1 : p.dropLast.getLast? = some b) :
    ∃ s : List V, p = s ++ [b, c] := by
  have hpne : p ≠ [] := hp.1.1
  have hdne : p.dropLast ≠ [] := by
    intro he
    have : p.dropLast.length = 0 := by simp [he]
    simp only [List.length_dropLast] at this
    omega
  have hpLast : p.getLast? = some c := hp.2.2
  have h1 := List.dropLast_append_getLast? c (by simpa using hpLast)
  have h2 := List.dropLast_append_getLast? b (by simpa using hlast1)
  refine ⟨p.dropLast.dropLast, ?_⟩
  calc
    p = p.dropLast ++ [c] := h1.symm
    _ = (p.dropLast.dropLast ++ [b]) ++ [c] := by rw [h2]
    _ = p.dropLast.dropLast ++ [b, c] := by simp

theorem main (G : SimpleGraph V) (hG : InF7 G)
    (p : List V) (p₁ pn1 pₙ : V) (hp : IsPathList G p) (hlen : 1 < pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hlast1 : p.dropLast.getLast? = some pn1)
    (X Y : Set V) (hXP : ∀ w ∈ p, w ∉ X) (hYP : ∀ w ∈ p, w ∉ Y)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hXYa : AnticonnectedSet G (X ∪ Y))
    (hp₁X : VertexComplete G p₁ X)
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pₙ))
    (z : V) (hz : z ∉ X ∪ Y) (hzP : z ∉ p)
    (hzXY : VertexComplete G z (X ∪ Y))
    (hznb : VertexAnticomplete G z {w : V | w ∈ p})
    (hpₙX : ¬ VertexComplete G pₙ X)
    (y x₁ : V) (hy : y ∈ Y) (q : List V) (hq : IsAntipathFrom G q pₙ y)
    (hqint : ∀ w ∈ SPGT.interior q, w ∈ X)
    (hx₁ : (SPGT.interior q).head? = some x₁) :
    ¬ G.Adj pn1 x₁ := by
  classical
  intro hpn1x₁
  let H : SimpleGraph V := Gᶜ
  have hplen : 3 ≤ p.length := by
    simp only [pathLength] at hlen
    omega
  have hpfrom : IsPathFrom G p p₁ pₙ := ⟨hp, hhead, hlast⟩
  have hpn1idx : p[p.length - 2]'(by omega) = pn1 := by
    have he := Workspace.ProofLemmas.Thm182DropLastIndex.dropLast_getLast?_eq p (by omega)
    rw [hlast1] at he
    exact Option.some_injective _ he.symm
  have hpₙidx : p[p.length - 1]'(by omega) = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast (by omega)
  have hp₁idx : p[0]'(by omega) = p₁ :=
    PathBasics.getElem_zero_of_head? hhead (by omega)
  have hpn1mem : pn1 ∈ p := by rw [← hpn1idx]; exact List.getElem_mem _
  have hpₙmem : pₙ ∈ p := PathBasics.getLast_mem hlast
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpn1pₙ : G.Adj pn1 pₙ := by
    have hadj := PathBasics.path_adj_succ hp (i := p.length - 2) (by omega)
    have hsecond : p[p.length - 2 + 1]'(by omega) =
        p[p.length - 1]'(by omega) := gidx p (by omega) _ _
    rw [hpn1idx, hsecond, hpₙidx] at hadj
    exact hadj
  have hpn1nepₙ : pn1 ≠ pₙ := hpn1pₙ.ne
  obtain ⟨t, hqshape⟩ := path_shape_of_first_interior hq hx₁
  subst q
  let r : List V := x₁ :: t ++ [y]
  have hqpath : IsPathFrom H (pₙ :: r) pₙ y := by simpa [H, r] using hq
  have hrpath : IsPathList H r := by
    have hd := PathBasics.isPathList_drop hqpath.1 (k := 1) (by simp [r])
    simpa using hd
  have hrconn : ConnectedSet H {w : V | w ∈ r} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hrpath
  have hYconn : ConnectedSet H Y := by simpa [H] using hYa
  have hyr : y ∈ r := by simp [r]
  let F₀ : Set V := {w : V | w ∈ r} ∪ Y
  have hF₀conn : ConnectedSet H F₀ := by
    exact ConnectedSetUnionAttach.connectedSet_union hrconn hYconn
      (Or.inl ⟨y, hyr, hy⟩)
  have hpn1Y : ¬ VertexComplete G pn1 Y := by
    intro hc
    exact hpn1nepₙ ((hYuniq pn1 hpn1mem).mp hc)
  obtain ⟨y₀, hy₀Y, hpn1y₀⟩ : ∃ y₀ ∈ Y, ¬ G.Adj pn1 y₀ := by
    simpa [VertexComplete] using hpn1Y
  have hpn1notY : pn1 ∉ Y := hYP pn1 hpn1mem
  have hpn1Hy₀ : H.Adj pn1 y₀ := by
    change Gᶜ.Adj pn1 y₀
    exact (SimpleGraph.compl_adj G pn1 y₀).mpr
      ⟨fun he => hpn1notY (he ▸ hy₀Y), hpn1y₀⟩
  let F : Set V := F₀ ∪ {pn1}
  have hFconn : ConnectedSet H F := by
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hF₀conn
      ⟨y₀, Or.inr hy₀Y, hpn1Hy₀⟩
  have hintereq : SPGT.interior (pₙ :: r) = x₁ :: t := by
    simp only [r, SPGT.interior, List.tail_cons]
    rw [List.dropLast_concat]
  have hx₁int : x₁ ∈ SPGT.interior (pₙ :: r) := by rw [hintereq]; simp
  have hx₁X : x₁ ∈ X := hqint x₁ (by simpa [r] using hx₁int)
  have hx₁notY : x₁ ∉ Y := by
    intro hxY
    have hGadj : G.Adj pₙ x₁ := (hYuniq pₙ hpₙmem).mpr rfl x₁ hxY
    have hHadj : H.Adj pₙ x₁ := by
      have := PathBasics.path_adj_succ hqpath.1 (i := 0) (by simp [r])
      simpa [r] using this
    exact ((SimpleGraph.compl_adj G pₙ x₁).mp (by simpa [H] using hHadj)).2 hGadj
  have hrXY : ∀ w ∈ r, w ∈ X ∨ w ∈ Y := by
    intro w hw
    have hw' : w = x₁ ∨ w ∈ t ∨ w = y := by simpa [r] using hw
    rcases hw' with rfl | hwt | rfl
    · exact Or.inl hx₁X
    · exact Or.inl (hqint w (by rw [hintereq]; simp [hwt]))
    · exact Or.inr hy
  have hpn1notF₀ : pn1 ∉ F₀ := by
    intro hm
    rcases hm with hmr | hmY
    · rcases hrXY pn1 hmr with hx | hy'
      · exact hXP pn1 hpn1mem hx
      · exact hpn1notY hy'
    · exact hpn1notY hmY
  have hFa_eq : F \ {pn1} = F₀ := by
    ext w
    simp only [F, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hw | rfl, hne⟩
      · exact hw
      · exact absurd rfl hne
    · intro hw
      exact ⟨Or.inl hw, fun he => hpn1notF₀ (he ▸ hw)⟩
  have hFa : ConnectedSet H (F \ {pn1}) := by rw [hFa_eq]; exact hF₀conn
  have hrtailpath : IsPathList H (t ++ [y]) := by
    have hd := PathBasics.isPathList_drop hrpath (k := 1) (by simp [r])
    simpa [r] using hd
  have hrtailconn : ConnectedSet H {w : V | w ∈ t ++ [y]} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hrtailpath
  let F₁ : Set V := {w : V | w ∈ t ++ [y]} ∪ Y
  have hF₁conn : ConnectedSet H F₁ :=
    ConnectedSetUnionAttach.connectedSet_union hrtailconn hYconn
      (Or.inl ⟨y, by simp, hy⟩)
  have hx₁notTail : x₁ ∉ t ++ [y] := by
    have hnd : (x₁ :: (t ++ [y])).Nodup := by simpa [r] using hrpath.2.1
    exact (List.nodup_cons.mp hnd).1
  have hx₁nepn1 : x₁ ≠ pn1 := hpn1x₁.ne.symm
  have hFb_eq : F \ {x₁} = F₁ ∪ {pn1} := by
    ext w
    change ((((w ∈ r ∨ w ∈ Y) ∨ w = pn1) ∧ w ≠ x₁) ↔
      ((w ∈ t ++ [y] ∨ w ∈ Y) ∨ w = pn1))
    constructor
    · rintro ⟨((hwr | hwY) | hwpn1), hne⟩
      · have hc : w = x₁ ∨ w ∈ t ++ [y] := by simpa [r] using hwr
        rcases hc with he | hwt
        · exact absurd he hne
        · exact Or.inl (Or.inl hwt)
      · exact Or.inl (Or.inr hwY)
      · exact Or.inr hwpn1
    · rintro ((hwt | hwY) | hwpn1)
      · refine ⟨Or.inl (Or.inl ?_), ?_⟩
        · simpa [r] using (Or.inr hwt : w = x₁ ∨ w ∈ t ++ [y])
        · intro he
          exact hx₁notTail (he ▸ hwt)
      · exact ⟨Or.inl (Or.inr hwY), fun he => hx₁notY (he ▸ hwY)⟩
      · refine ⟨Or.inr hwpn1, ?_⟩
        intro he
        exact hx₁nepn1 (he.symm.trans hwpn1)
  have hFb : ConnectedSet H (F \ {x₁}) := by
    rw [hFb_eq]
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hF₁conn
      ⟨y₀, Or.inr hy₀Y, hpn1Hy₀⟩
  let A : Set V := {w : V | w ∈ p.take (p.length - 2)}
  have hApath : IsPathList G (p.take (p.length - 2)) :=
    PathBasics.isPathList_take hp (by omega)
  have hAconnG : ConnectedSet G A :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hApath
  have hAantiH : AnticonnectedSet H A := by
    change ConnectedSet Hᶜ A
    have he : Hᶜ = G := by simp [H]
    rwa [he]
  have hAsubp : ∀ w ∈ A, w ∈ p := by
    intro w hw
    exact List.take_subset _ _ hw
  have hp₁A : p₁ ∈ A := by
    rw [← hp₁idx]
    exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩
  have hprevA : p[p.length - 3]'(by omega) ∈ A := by
    exact List.mem_iff_getElem.mpr
      ⟨p.length - 3, by simp; omega, by simp⟩
  have hpn1notA : pn1 ∉ A := by
    intro hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hik : i < p.length - 2 := by
      have ht := hi
      simp only [List.length_take] at ht
      omega
    have hip : i < p.length := by omega
    have hget : (p.take (p.length - 2))[i]'hi = p[i]'hip := by simp
    have heq : p[i]'hip = p[p.length - 2]'(by omega) :=
      hget.symm.trans (he.trans hpn1idx.symm)
    have := hp.2.1.getElem_inj_iff.mp heq
    omega
  have hpₙnotA : pₙ ∉ A := by
    intro hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hik : i < p.length - 2 := by
      have ht := hi
      simp only [List.length_take] at ht
      omega
    have hip : i < p.length := by omega
    have hget : (p.take (p.length - 2))[i]'hi = p[i]'hip := by simp
    have heq : p[i]'hip = p[p.length - 1]'(by omega) :=
      hget.symm.trans (he.trans hpₙidx.symm)
    have := hp.2.1.getElem_inj_iff.mp heq
    omega
  have hAnoX : ∀ w ∈ A, w ∉ X := fun w hw => hXP w (hAsubp w hw)
  have hAnoY : ∀ w ∈ A, w ∉ Y := fun w hw => hYP w (hAsubp w hw)
  have hFA : Disjoint F A := Set.disjoint_left.mpr (by
    intro w hwF hwA
    change ((w ∈ r ∨ w ∈ Y) ∨ w = pn1) at hwF
    rcases hwF with (hwr | hwY) | rfl
    · rcases hrXY w hwr with hwX | hwY
      · exact hAnoX w hwA hwX
      · exact hAnoY w hwA hwY
    · exact hAnoY w hwA hwY
    · exact hpn1notA hwA)
  have hpnₙnotr : pₙ ∉ r := (List.nodup_cons.mp hqpath.1.2.1).1
  have hznotF : z ∉ F := by
    intro hzF
    change ((z ∈ r ∨ z ∈ Y) ∨ z = pn1) at hzF
    rcases hzF with (hzr | hzY) | hze
    · rcases hrXY z hzr with hzX | hzY
      · exact hz (Or.inl hzX)
      · exact hz (Or.inr hzY)
    · exact hz (Or.inr hzY)
    · exact hzP (hze ▸ hpn1mem)
  have hpₙnotF : pₙ ∉ F := by
    intro hpₙF
    change ((pₙ ∈ r ∨ pₙ ∈ Y) ∨ pₙ = pn1) at hpₙF
    rcases hpₙF with (hpr | hpY) | he
    · exact hpnₙnotr hpr
    · exact hYP pₙ hpₙmem hpY
    · exact hpn1nepₙ he.symm
  have hznotA : z ∉ A := fun hzA => hzP (hAsubp z hzA)
  have ha₀out : z ∉ F ∪ A := fun h => h.elim hznotF hznotA
  have hb₀out : pₙ ∉ F ∪ A := fun h => h.elim hpₙnotF hpₙnotA
  have hzHA : VertexComplete H z A := by
    intro w hwA
    change Gᶜ.Adj z w
    apply (SimpleGraph.compl_adj G z w).mpr
    exact ⟨fun he => hzP (he ▸ hAsubp w hwA), hznb w (hAsubp w hwA)⟩
  have hpₙHA : VertexComplete H pₙ A := by
    intro w hwA
    have hpₙw : ¬ G.Adj pₙ w := by
      intro hadj
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hwA
      have hik : i < p.length - 2 := by
        have ht := hi
        simp only [List.length_take] at ht
        omega
      have hip : i < p.length := by omega
      have hget : (p.take (p.length - 2))[i]'hi = p[i]'hip := by simp
      have hew : p[i]'hip = w := hget.symm.trans he
      have hadj' : G.Adj (p[p.length - 1]'(by omega)) (p[i]'hip) := by
        simpa only [hpₙidx, hew] using hadj
      rcases (PathBasics.path_adj_iff hp (by omega) hip).mp hadj' with h | h <;> omega
    change Gᶜ.Adj pₙ w
    exact (SimpleGraph.compl_adj G pₙ w).mpr
      ⟨fun he => hpₙnotA (he ▸ hwA), hpₙw⟩
  have hprevAdj : G.Adj (p[p.length - 3]'(by omega)) pn1 := by
    have hadj := PathBasics.path_adj_succ hp (i := p.length - 3) (by omega)
    have hsecond : p[p.length - 3 + 1]'(by omega) =
        p[p.length - 2]'(by omega) := gidx p (by omega) _ _
    rw [hsecond, hpn1idx] at hadj
    exact hadj
  have hpn1notCompA : ¬ VertexComplete H pn1 A := by
    intro hc
    have hh := hc (p[p.length - 3]'(by omega)) hprevA
    exact ((SimpleGraph.compl_adj G pn1 (p[p.length - 3]'(by omega))).mp
      (by simpa [H] using hh)).2 hprevAdj.symm
  have hx₁notCompA : ¬ VertexComplete H x₁ A := by
    intro hc
    have hh := hc p₁ hp₁A
    exact ((SimpleGraph.compl_adj G x₁ p₁).mp (by simpa [H] using hh)).2
      (hp₁X x₁ hx₁X).symm
  have hHpn1z : H.Adj pn1 z := by
    change Gᶜ.Adj pn1 z
    exact (SimpleGraph.compl_adj G pn1 z).mpr
      ⟨fun he => hzP (he.symm ▸ hpn1mem), fun hadj => hznb pn1 hpn1mem hadj.symm⟩
  have hHzpₙ : H.Adj z pₙ := by
    change Gᶜ.Adj z pₙ
    exact (SimpleGraph.compl_adj G z pₙ).mpr
      ⟨fun he => hzP (he ▸ hpₙmem), hznb pₙ hpₙmem⟩
  have hHpₙx₁ : H.Adj pₙ x₁ := by
    have hadj := PathBasics.path_adj_succ hqpath.1 (i := 0) (by simp [r])
    simpa [r] using hadj
  have hnHpn1pₙ : ¬ H.Adj pn1 pₙ := by
    intro hh
    exact ((SimpleGraph.compl_adj G pn1 pₙ).mp (by simpa [H] using hh)).2 hpn1pₙ
  have hnHpn1x₁ : ¬ H.Adj pn1 x₁ := by
    intro hh
    exact ((SimpleGraph.compl_adj G pn1 x₁).mp (by simpa [H] using hh)).2 hpn1x₁
  have hzx₁ : G.Adj z x₁ := hzXY x₁ (Or.inl hx₁X)
  have hnHzx₁ : ¬ H.Adj z x₁ := by
    intro hh
    exact ((SimpleGraph.compl_adj G z x₁).mp (by simpa [H] using hh)).2 hzx₁
  have hpathH : IsPathList H [pn1, z, pₙ, x₁] := by
    apply PathGlue.isPathList_four
    · simp [hHpn1z.ne, hHzpₙ.ne, hHpₙx₁.ne, hpn1nepₙ,
        hpn1x₁.ne, hzx₁.ne]
    · exact hHpn1z
    · exact hHzpₙ
    · exact hHpₙx₁
    · exact hnHpn1pₙ
    · exact hnHpn1x₁
    · exact hnHzx₁
  have hzFunique : {f ∈ F | H.Adj z f} = {pn1} := by
    ext f
    constructor
    · rintro ⟨hfF, hzf⟩
      change ((f ∈ r ∨ f ∈ Y) ∨ f = pn1) at hfF
      rcases hfF with (hfr | hfY) | hfpn1
      · rcases hrXY f hfr with hfX | hfY
        · have hgf : G.Adj z f := hzXY f (Or.inl hfX)
          exact False.elim (((SimpleGraph.compl_adj G z f).mp
            (by simpa [H] using hzf)).2 hgf)
        · have hgf : G.Adj z f := hzXY f (Or.inr hfY)
          exact False.elim (((SimpleGraph.compl_adj G z f).mp
            (by simpa [H] using hzf)).2 hgf)
      · have hgf : G.Adj z f := hzXY f (Or.inr hfY)
        exact False.elim (((SimpleGraph.compl_adj G z f).mp
          (by simpa [H] using hzf)).2 hgf)
      · simpa using hfpn1
    · intro hf
      have he : f = pn1 := by simpa using hf
      subst f
      exact ⟨by change ((pn1 ∈ r ∨ pn1 ∈ Y) ∨ pn1 = pn1); exact Or.inr rfl,
        hHpn1z.symm⟩
  have hpₙUniqueR : ∀ f ∈ r, H.Adj pₙ f → f = x₁ := by
    intro f hfr hpf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hfr
    have hqj : j + 1 < (pₙ :: r).length := by simp; omega
    have hq0 : 0 < (pₙ :: r).length := by simp
    have hadj : H.Adj ((pₙ :: r)[0]'hq0) ((pₙ :: r)[j + 1]'hqj) := by
      simpa using hpf
    have hrel := (PathBasics.path_adj_iff hqpath.1 hq0 hqj).mp hadj
    have hj0 : j = 0 := by rcases hrel with h | h <;> omega
    subst j
    simp [r]
  have hpₙFunique : {f ∈ F | H.Adj pₙ f} = {x₁} := by
    ext f
    constructor
    · rintro ⟨hfF, hpf⟩
      change ((f ∈ r ∨ f ∈ Y) ∨ f = pn1) at hfF
      rcases hfF with (hfr | hfY) | hfpn1
      · simpa using hpₙUniqueR f hfr hpf
      · have hgf : G.Adj pₙ f := (hYuniq pₙ hpₙmem).mpr rfl f hfY
        exact False.elim (((SimpleGraph.compl_adj G pₙ f).mp
          (by simpa [H] using hpf)).2 hgf)
      · subst f
        exact False.elim (hnHpn1pₙ hpf.symm)
    · intro hf
      have he : f = x₁ := by simpa using hf
      subst f
      exact ⟨by
        change ((x₁ ∈ r ∨ x₁ ∈ Y) ∨ x₁ = pn1)
        exact Or.inl (Or.inl (by simp [r])), hHpₙx₁⟩
  have hHF7 : InF7 H := by
    have hc : InF7 Gᶜ := (ClassLemmas.inF7_compl (G := G)).mpr hG
    simpa [H] using hc
  have hpn1F : pn1 ∈ F := by
    change ((pn1 ∈ r ∨ pn1 ∈ Y) ∨ pn1 = pn1)
    exact Or.inr rfl
  have hx₁F : x₁ ∈ F := by
    change ((x₁ ∈ r ∨ x₁ ∈ Y) ∨ x₁ = pn1)
    exact Or.inl (Or.inl (by simp [r]))
  obtain ⟨w, hwA, hwanti⟩ := Thm174RRStrip.oneSided H hHF7 F A hFA hFconn hAantiH
    z pₙ pn1 x₁ ha₀out hb₀out hpn1F hx₁F hpathH hzHA hpₙHA
    hpn1notCompA hx₁notCompA hzFunique hpₙFunique hFa hFb
  have hwY : VertexComplete G w Y := by
    intro v hvY
    have hvFdiff : v ∈ F \ {pn1} := by
      refine ⟨?_, ?_⟩
      · change ((v ∈ r ∨ v ∈ Y) ∨ v = pn1)
        exact Or.inl (Or.inr hvY)
      · intro he
        exact hpn1notY (he.symm ▸ hvY)
    by_contra hnwv
    have hn : w ≠ v := by
      intro he
      exact hAnoY w hwA (he ▸ hvY)
    have hh : H.Adj w v := by
      change Gᶜ.Adj w v
      exact (SimpleGraph.compl_adj G w v).mpr ⟨hn, hnwv⟩
    exact hwanti v hvFdiff hh
  have hwpₙ : w = pₙ := (hYuniq w (hAsubp w hwA)).mp hwY
  exact hpₙnotA (hwpₙ ▸ hwA)

end Workspace.ProofLemmas.Thm174Main
