import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm182DropLastIndex
import Workspace.ProofLemmas.Thm182EdgeSetTake
import Workspace.ProofLemmas.Thm182MaxIndex
import Workspace.ProofLemmas.Thm185TripleRRReduction
import Workspace.ProofLemmas.Thm185TripleRRSpecial

/-!
# The path-minimal reduction in 17.5

This file packages a counterexample with the two anticonnected sides and the
external vertex fixed, and proves printed claim (1): in a shortest
counterexample the first path vertex is the only vertex complete to the first
side.  Unlike the specialization used later in section 18, no disjointness of
the two sides is assumed here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm175Minimal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A counterexample to the parity conclusion of 17.5, with `G`, `X`, `Y`, and
`z` held fixed. -/
structure EvenRRConfig (G : SimpleGraph V) (X Y : Set V) (z : V) where
  p : List V
  p₁ : V
  pₙ : V
  hp : IsPathFrom G p p₁ pₙ
  hodd : Odd (pathLength p)
  hlong : 1 < pathLength p
  houtX : ∀ w ∈ p, w ∉ X
  houtY : ∀ w ∈ p, w ∉ Y
  hp₁X : VertexComplete G p₁ X
  hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pₙ)
  hzP : z ∉ p
  hzanti : VertexAnticomplete G z {w : V | w ∈ p}
  heven : Even {e : Sym2 V | ∃ u ∈ p, ∃ w ∈ p,
    e = s(u, w) ∧ EdgeComplete G X u w}.ncard

/-- Printed claim (1) of 17.5.  The construction of the antipath needed for
17.4 is valid even when `X` and `Y` overlap: take the first `Y`-vertex on an
antipath from the last path vertex into `Y`. -/
theorem shortest_first_unique
    (G : SimpleGraph V) (hG : InF7 G)
    (X Y : Set V)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hXYa : AnticonnectedSet G (X ∪ Y))
    (z : V) (hzXY : z ∉ X ∪ Y) (hzXYcomp : VertexComplete G z (X ∪ Y))
    (c : EvenRRConfig G X Y z)
    (hmin : ∀ d : EvenRRConfig G X Y z, d.p.length < c.p.length → False) :
    ∀ w ∈ c.p, (VertexComplete G w X ↔ w = c.p₁) := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hp₁mem : c.p₁ ∈ c.p := PathBasics.head_mem c.hp.2.1
  have hpₙmem : c.pₙ ∈ c.p := PathBasics.getLast_mem c.hp.2.2
  have hp₁nepₙ : c.p₁ ≠ c.pₙ :=
    PathBasics.isPathFrom_ends_ne c.hp (Nat.le_of_lt c.hlong)
  have hzX : VertexComplete G z X := fun x hx => hzXYcomp x (Or.inl hx)
  have hpₙX : ¬ VertexComplete G c.pₙ X := by
    intro hcomplete
    have hoddEdges := Thm185TripleRRSpecial.odd_complete_edges_of_complete_ends
      G hBerge X hXa c.p c.p₁ c.pₙ c.hp c.hodd c.houtX c.hp₁X hcomplete
      z hzX c.hzanti
    exact (Nat.not_odd_iff_even.mpr c.heven) hoddEdges
  have hlen3 : 3 ≤ c.p.length := by
    have hlong := c.hlong
    rw [PathBasics.pathLength_eq] at hlong
    omega
  let pn1 : V := c.p[c.p.length - 2]'(by omega)
  have hlast1 : c.p.dropLast.getLast? = some pn1 := by
    exact Thm182DropLastIndex.dropLast_getLast?_eq c.p (by omega)
  have hYne : Y.Nonempty := by
    by_contra hne
    have hYempty : Y = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hp₁Y : VertexComplete G c.p₁ Y := by simp [hYempty, VertexComplete]
    exact hp₁nepₙ ((c.hYuniq c.p₁ hp₁mem).mp hp₁Y)
  have hpₙXY : c.pₙ ∉ X ∪ Y := by
    rintro (hx | hy)
    · exact c.houtX c.pₙ hpₙmem hx
    · exact c.houtY c.pₙ hpₙmem hy
  have hpₙY : VertexComplete G c.pₙ Y :=
    (c.hYuniq c.pₙ hpₙmem).mpr rfl
  obtain ⟨y, hyY, q, hq, hqint, hqintne⟩ :=
    _root_.Workspace.ProofLemmas.Thm185TripleRRReduction.exists_antipath_to_Y_with_interior_in_X
      G X Y hXYa hYne c.pₙ hpₙXY hpₙY hpₙX
  let x₁ : V := (SPGT.interior q).head hqintne
  have hx₁head : (SPGT.interior q).head? = some x₁ :=
    List.head?_eq_some_head hqintne
  have hx₁int : x₁ ∈ SPGT.interior q := List.head_mem hqintne
  have hpn1X : ¬ VertexComplete G pn1 X := by
    intro hcomplete
    have h174 := _root_.Workspace.Statements.S17.SPGT.thm_17_4
      G hG c.p c.p₁ pn1 c.pₙ c.hp.1 c.hlong c.hp.2.1 c.hp.2.2 hlast1
      X Y c.houtX c.houtY hXa hYa hXYa c.hp₁X c.hYuniq
      z hzXY c.hzP hzXYcomp c.hzanti hpₙX y x₁ hyY q hq hqint hx₁head
    exact h174 (hcomplete x₁ (hqint x₁ hx₁int))
  have hpos : 0 < c.p.length := PathBasics.path_length_pos c.hp.1
  have hp₀ : c.p[0]'hpos = c.p₁ :=
    PathBasics.getElem_zero_of_head? c.hp.2.1 hpos
  have h₀X : VertexComplete G (c.p[0]'hpos) X := hp₀ ▸ c.hp₁X
  obtain ⟨m, hm, hmX, hmax⟩ :=
    Thm182MaxIndex.exists_max_complete_index G X c.p hpos h₀X
  have hpLast : c.p[c.p.length - 1]'(by omega) = c.pₙ :=
    PathBasics.getElem_last_of_getLast? c.hp.2.2 hpos
  have hmle : m ≤ c.p.length - 3 := by
    have hmNotLast : m ≠ c.p.length - 1 := by
      intro heq
      apply hpₙX
      rw [← hpLast]
      simpa [heq] using hmX
    have hmNotPen : m ≠ c.p.length - 2 := by
      intro heq
      apply hpn1X
      change VertexComplete G c.p[c.p.length - 2] X
      simpa [heq] using hmX
    omega
  have hmEven : Even m :=
    Thm185TripleRRSpecial.max_complete_index_even_of_even_edges
      G hBerge X hXa c.p c.p₁ c.hp.1 c.hp.2.1 c.houtX c.hp₁X
      m hm hmX hmax z hzX c.hzanti c.heven
  have hmzero : m = 0 := by
    by_contra hmne
    have hmpos : 0 < m := Nat.pos_of_ne_zero hmne
    let t : List V := (c.p.drop m).take ((c.p.length - 1) - m + 1)
    have htFrom₀ := PathBasics.isPathFrom_slice c.hp.1
      (show m < c.p.length - 1 by omega) (show c.p.length - 1 < c.p.length by omega)
    have htFrom : IsPathFrom G t (c.p[m]'hm) c.pₙ := by
      simpa [t, hpLast] using htFrom₀
    have htlen : t.length = (c.p.length - 1) - m + 1 := by
      exact PathBasics.length_slice c.p (show m ≤ c.p.length - 1 by omega)
        (show c.p.length - 1 < c.p.length by omega)
    have htplen : pathLength t = pathLength c.p - m := by
      rw [PathBasics.pathLength_eq, htlen, PathBasics.pathLength_eq]
      omega
    have htodd : Odd (pathLength t) := by
      obtain ⟨r, hr⟩ := c.hodd
      obtain ⟨s, hs⟩ := hmEven
      have hsr : s ≤ r := by
        have hpl := PathBasics.pathLength_eq c.p
        rw [hr] at hpl
        rw [hs] at hmle
        omega
      refine ⟨r - s, ?_⟩
      rw [htplen, hr, hs]
      omega
    have htlong : 1 < pathLength t := by
      rw [htplen, PathBasics.pathLength_eq]
      omega
    have htoutX : ∀ w ∈ t, w ∉ X := by
      intro w hw
      exact c.houtX w (List.drop_subset _ _ (List.take_subset _ _ hw))
    have htoutY : ∀ w ∈ t, w ∉ Y := by
      intro w hw
      exact c.houtY w (List.drop_subset _ _ (List.take_subset _ _ hw))
    have htYuniq : ∀ w ∈ t, (VertexComplete G w Y ↔ w = c.pₙ) := by
      intro w hw
      exact c.hYuniq w (List.drop_subset _ _ (List.take_subset _ _ hw))
    have htz : z ∉ t := fun hz =>
      c.hzP (List.drop_subset _ _ (List.take_subset _ _ hz))
    have htzanti : VertexAnticomplete G z {w : V | w ∈ t} := by
      intro w hw
      exact c.hzanti w (List.drop_subset _ _ (List.take_subset _ _ hw))
    have htXuniq : ∀ w ∈ t,
        (VertexComplete G w X ↔ w = c.p[m]'hm) := by
      intro w hw
      obtain ⟨k, hk, hmk, -, hkw⟩ :=
        (PathBasics.mem_slice_iff c.p (show m ≤ c.p.length - 1 by omega)
          (show c.p.length - 1 < c.p.length by omega)).mp hw
      constructor
      · intro hwX
        have hkm := hmax k hk (hkw ▸ hwX)
        have : k = m := by omega
        subst k
        exact hkw.symm
      · rintro rfl
        exact hmX
    have htEdgesEmpty : {e : Sym2 V | ∃ u ∈ t, ∃ w ∈ t,
        e = s(u, w) ∧ EdgeComplete G X u w} = ∅ := by
      ext e
      constructor
      · rintro ⟨u, hu, w, hw, rfl, hE⟩
        have huEq := (htXuniq u hu).mp hE.2.1
        have hwEq := (htXuniq w hw).mp hE.2.2
        rw [huEq, hwEq] at hE
        exact False.elim (G.irrefl hE.1)
      · simp
    have htEven : Even {e : Sym2 V | ∃ u ∈ t, ∃ w ∈ t,
        e = s(u, w) ∧ EdgeComplete G X u w}.ncard := by
      rw [htEdgesEmpty]
      simp
    let d : EvenRRConfig G X Y z :=
      { p := t
        p₁ := c.p[m]'hm
        pₙ := c.pₙ
        hp := htFrom
        hodd := htodd
        hlong := htlong
        houtX := htoutX
        houtY := htoutY
        hp₁X := hmX
        hYuniq := htYuniq
        hzP := htz
        hzanti := htzanti
        heven := htEven }
    have hdlt : d.p.length < c.p.length := by
      dsimp [d]
      rw [htlen]
      omega
    exact hmin d hdlt
  intro w hw
  constructor
  · intro hwX
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk0 : k = 0 := by
      have := hmax k hk hwX
      omega
    subst k
    exact hp₀
  · rintro rfl
    exact c.hp₁X

end Workspace.ProofLemmas.Thm175Minimal
