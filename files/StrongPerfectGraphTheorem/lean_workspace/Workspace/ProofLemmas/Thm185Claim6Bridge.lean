import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.TriangleCatching
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm182DropLastIndex
import Workspace.ProofLemmas.Thm182MaxIndex
import Workspace.ProofLemmas.Thm185TripleRRReduction
import Workspace.ProofLemmas.Thm185TripleRRSpecial
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S17.Thm_17_1
import Workspace.Statements.S17.Thm_17_5

/-!
# The one-vertex triple-RR instance in claim (6) of 18.5

The invocation of 17.5 in claim (6) has substantially more structure than the
general theorem.  Its second anticonnected set is obtained by adjoining one
vertex `v` to a set `B` which is complete to the first set `A`; `v` has a
nonneighbour in each side.  This file isolates exactly that remaining parity
bridge.  Keeping the stronger hypotheses in the interface is important: its
eventual direct proof can use the cut-vertex structure of the union instead of
formalizing all of the optimal-counterexample proof of general 17.5.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm185Claim6Bridge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A path counterexample to the parity conclusion of 17.5, with the two
anticonnected sides and the external complete/anticomplete vertex held fixed.
Packaging this predicate makes the paper's first, path-length minimality clause
usable without hiding any hypothesis. -/
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

/-- Claim (1) in the proof of 17.5, specialized to the disjoint one-vertex
extension setting needed by 18.5.  In a shortest even counterexample the first
path vertex is its only `X`-complete vertex.

The distinguished `y₀ ∈ Y` which is not `X`-complete supplies the antipath
needed by 17.4.  In the application it is the adjoined vertex `v`. -/
theorem minimal_config_first_unique
    (G : SimpleGraph V) (hG : InF7 G)
    (X Y : Set V) (hXY : Disjoint X Y)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hXYa : AnticonnectedSet G (X ∪ Y))
    (y₀ : V) (hy₀Y : y₀ ∈ Y) (hy₀X : ¬ VertexComplete G y₀ X)
    (z : V) (hzXY : z ∉ X ∪ Y) (hzXYcomp : VertexComplete G z (X ∪ Y))
    (c : EvenRRConfig G X Y z)
    (hmin : ∀ d : EvenRRConfig G X Y z, d.p.length < c.p.length → False) :
    ∀ w ∈ c.p, (VertexComplete G w X ↔ w = c.p₁) := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hp₁mem : c.p₁ ∈ c.p := PathBasics.head_mem c.hp.2.1
  have hpₙmem : c.pₙ ∈ c.p := PathBasics.getLast_mem c.hp.2.2
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
  have hy₀notX : y₀ ∉ X := by
    intro hyX
    exact Set.disjoint_left.mp hXY hyX hy₀Y
  have miss_of_not_complete : ∀ {u : V}, ¬ VertexComplete G u X →
      ∃ x ∈ X, ¬ G.Adj u x := by
    intro u hu
    by_contra hnone
    push Not at hnone
    exact hu hnone
  have hpₙY : VertexComplete G c.pₙ Y := (c.hYuniq c.pₙ hpₙmem).mpr rfl
  have hpₙy₀ : G.Adj c.pₙ y₀ := hpₙY y₀ hy₀Y
  have hpn1X : ¬ VertexComplete G pn1 X :=
    Thm185TripleRRReduction.penultimate_not_complete
      G hG c.p c.p₁ pn1 c.pₙ c.hp.1 c.hlong c.hp.2.1 c.hp.2.2 hlast1
      X Y c.houtX c.houtY hXa hYa hXYa c.hp₁X c.hYuniq
      z hzXY c.hzP hzXYcomp c.hzanti hpₙX y₀ hy₀Y hy₀notX
      (miss_of_not_complete hpₙX) (miss_of_not_complete hy₀X) hpₙy₀
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
    have htFrom₀ := PathBasics.isPathFrom_slice c.hp.1 (show m < c.p.length - 1 by omega)
      (show c.p.length - 1 < c.p.length by omega)
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

/-- The singleton first-side case in claim (3) of the source proof of 17.5.
After minimizing the path and applying `minimal_config_first_unique`, prefixing
the path by `z-a` gives a long odd path between `Y`-complete vertices with no
`Y`-complete internal vertex, contrary to 13.6. -/
theorem singleton_first_side_absurd
    (G : SimpleGraph V) (hG : InF7 G)
    (X Y : Set V) (hXY : Disjoint X Y)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hXYa : AnticonnectedSet G (X ∪ Y))
    (y₀ : V) (hy₀Y : y₀ ∈ Y) (hy₀X : ¬ VertexComplete G y₀ X)
    (z : V) (hzXY : z ∉ X ∪ Y) (hzXYcomp : VertexComplete G z (X ∪ Y))
    (a : V) (hXeq : X = {a})
    (c : EvenRRConfig G X Y z) : False := by
  classical
  subst X
  let BadLength : ℕ → Prop := fun n =>
    ∃ d : EvenRRConfig G ({a} : Set V) Y z, d.p.length = n
  have hex : ∃ n, BadLength n := ⟨c.p.length, c, rfl⟩
  let n : ℕ := Nat.find hex
  obtain ⟨d, hdlen⟩ := Nat.find_spec hex
  have hmin : ∀ e : EvenRRConfig G ({a} : Set V) Y z,
      e.p.length < d.p.length → False := by
    intro e he
    have hen : e.p.length < n := by simpa [n, hdlen] using he
    exact (Nat.find_min hex hen) ⟨e, rfl⟩
  have huniq := minimal_config_first_unique G hG ({a} : Set V) Y hXY hXa hYa hXYa
    y₀ hy₀Y hy₀X z hzXY hzXYcomp d hmin
  have haP : a ∉ d.p := by
    intro ha
    exact d.houtX a ha (by simp)
  have haY : a ∉ Y := by
    intro ha
    exact Set.disjoint_left.mp hXY (by simp) ha
  have hza : G.Adj z a := hzXYcomp a (Or.inl (by simp))
  have hp₁a : G.Adj a d.p₁ := (d.hp₁X a (by simp)).symm
  have haother : ∀ w ∈ d.p, w ≠ d.p₁ → ¬ G.Adj a w := by
    intro w hw hwne haw
    have hwX : VertexComplete G w ({a} : Set V) := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact haw.symm
    exact hwne ((huniq w hw).mp hwX)
  have haPath : IsPathFrom G (a :: d.p) a d.pₙ :=
    PathAttach.isPathFrom_cons d.hp hp₁a haP haother
  have hznotAPath : z ∉ a :: d.p := by
    simp only [List.mem_cons, not_or]
    exact ⟨fun hzaeq => hzXY (Or.inl (by simpa [hzaeq])), d.hzP⟩
  have hzother : ∀ w ∈ a :: d.p, w ≠ a → ¬ G.Adj z w := by
    intro w hw hwne
    simp only [List.mem_cons] at hw
    rcases hw with hw | hw
    · subst w
      exact False.elim (hwne rfl)
    · exact d.hzanti w hw
  have hbig : IsPathFrom G (z :: a :: d.p) z d.pₙ :=
    PathAttach.isPathFrom_cons haPath hza hznotAPath hzother
  have hbigodd : Odd (pathLength (z :: a :: d.p)) := by
    obtain ⟨r, hr⟩ := d.hodd
    have hdlen := PathBasics.pathLength_eq d.p
    rw [hr] at hdlen
    refine ⟨r + 1, ?_⟩
    rw [PathBasics.pathLength_eq]
    simp only [List.length_cons]
    omega
  have hbiglong : 3 < pathLength (z :: a :: d.p) := by
    have hdlong := d.hlong
    rw [PathBasics.pathLength_eq] at hdlong
    rw [PathBasics.pathLength_eq]
    simp only [List.length_cons]
    omega
  have hbigY : Y ⊆ {w : V | w ∈ z :: a :: d.p}ᶜ := by
    intro y hy hybig
    simp only [List.mem_cons] at hybig
    rcases hybig with rfl | rfl | hyp
    · exact hzXY (Or.inr hy)
    · exact haY hy
    · exact d.houtY y hyp hy
  have hzY : VertexComplete G z Y := fun y hy => hzXYcomp y (Or.inr hy)
  have hpₙY : VertexComplete G d.pₙ Y :=
    (d.hYuniq d.pₙ (PathBasics.getLast_mem d.hp.2.2)).mpr rfl
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1
      (z :: a :: d.p) z d.pₙ hbig hbigodd Y hbigY hYa hzY hpₙY with
      hedge | hshort
  · obtain ⟨u, hu, w, hw, hE⟩ := hedge
    have complete_vertex : ∀ q ∈ z :: a :: d.p,
        VertexComplete G q Y → q = z ∨ q = d.pₙ := by
      intro q hq hqY
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hqp
      · exact Or.inl rfl
      · exfalso
        apply hy₀X
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact (hqY y₀ hy₀Y).symm
      · exact Or.inr ((d.hYuniq q hqp).mp hqY)
    rcases complete_vertex u hu hE.2.1 with rfl | rfl <;>
      rcases complete_vertex w hw hE.2.2 with rfl | rfl
    · exact G.irrefl hE.1
    · exact d.hzanti d.pₙ (PathBasics.getLast_mem d.hp.2.2) hE.1
    · exact d.hzanti d.pₙ (PathBasics.getLast_mem d.hp.2.2) hE.1.symm
    · exact G.irrefl hE.1
  · exact (by omega : False)

/-- The smallest cut-vertex instance is already ruled out by triangle catching.
This is the base case for a direct proof of the one-vertex extension bridge. -/
theorem singleton_sides_absurd
    (G : SimpleGraph V) (hG : InF7 G) (a b v z : V)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hlen : 1 < pathLength p) (hhead : p.head? = some p₁)
    (hlast : p.getLast? = some pₙ)
    (hab : G.Adj a b) (hva : ¬ G.Adj v a) (hvb : ¬ G.Adj v b)
    (hvneA : v ≠ a) (hvneB : v ≠ b)
    (hzv : G.Adj z v) (hza : G.Adj z a) (hzb : G.Adj z b)
    (hzP : z ∉ p) (hvP : v ∉ p) (haP : a ∉ p) (hbP : b ∉ p)
    (hzanti : VertexAnticomplete G z {w : V | w ∈ p})
    (hp₁a : G.Adj p₁ a) (hpₙb : G.Adj pₙ b)
    (hauniq : ∀ w ∈ p, (G.Adj w a ↔ w = p₁))
    (hbuniq : ∀ w ∈ p, (G.Adj w b ↔ w = pₙ))
    (hvpₙ : G.Adj v pₙ) : False := by
  classical
  let T : Set V := {z, a, b}
  let F : Set V := {w : V | w ∈ p} ∪ {v}
  have hza' : z ≠ a := hza.ne
  have hzb' : z ≠ b := hzb.ne
  have hab' : a ≠ b := hab.ne
  have hTcard : T.ncard = 3 := by
    simp [T, hza', hzb', hab']
  have hTtri : IsTriangle G T := by
    refine ⟨hTcard, ?_⟩
    intro x hx y hy hxy
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals simp_all [SimpleGraph.adj_comm]
  have hPconn : ConnectedSet G {w : V | w ∈ p} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp
  have hFconn : ConnectedSet G F := by
    dsimp [F]
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hPconn
      ⟨pₙ, PathBasics.getLast_mem hlast, hvpₙ⟩
  have hvneZ : v ≠ z := hzv.ne'
  have hFT : F ⊆ Tᶜ := by
    intro x hx hxT
    rcases hx with hxP | hxv
    · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hxT
      rcases hxT with rfl | rfl | rfl
      · exact hzP hxP
      · exact haP hxP
      · exact hbP hxP
    · rw [Set.mem_singleton_iff] at hxv
      subst x
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hxT
      rcases hxT with h | h | h
      · exact hvneZ h
      · exact hvneA h
      · exact hvneB h
  have hcatch : Catches G F T := by
    refine ⟨hTtri, hFconn, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hxF hxT
      exact hFT hxF hxT
    · intro x hx
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨v, Or.inr rfl, hzv⟩
      · exact ⟨p₁, Or.inl (PathBasics.head_mem hhead), hp₁a.symm⟩
      · exact ⟨pₙ, Or.inl (PathBasics.getLast_mem hlast), hpₙb.symm⟩
  have hp₁nepₙ : p₁ ≠ pₙ :=
    PathBasics.isPathFrom_ends_ne ⟨hp, hhead, hlast⟩ (by omega)
  have hvnep₁ : v ≠ p₁ := fun h => hvP (h ▸ PathBasics.head_mem hhead)
  have hvnepₙ : v ≠ pₙ := fun h => hvP (h ▸ PathBasics.getLast_mem hlast)
  have hzchar : ∀ f ∈ F, (G.Adj f z ↔ f = v) := by
    intro f hf
    constructor
    · intro hfz
      rcases hf with hfP | hfv
      · exact False.elim ((hzanti f hfP) hfz.symm)
      · simpa using hfv
    · rintro rfl
      exact hzv.symm
  have hachar : ∀ f ∈ F, (G.Adj f a ↔ f = p₁) := by
    intro f hf
    constructor
    · intro hfa
      rcases hf with hfP | hfv
      · exact (hauniq f hfP).mp hfa
      · rw [Set.mem_singleton_iff] at hfv
        subst f
        exact absurd hfa hva
    · rintro rfl
      exact hp₁a
  have hbchar : ∀ f ∈ F, (G.Adj f b ↔ f = pₙ) := by
    intro f hf
    constructor
    · intro hfb
      rcases hf with hfP | hfv
      · exact (hbuniq f hfP).mp hfb
      · rw [Set.mem_singleton_iff] at hfv
        subst f
        exact absurd hfb hvb
    · rintro rfl
      exact hpₙb
  have hbound : ∀ f ∈ F, (G.neighborSet f ∩ T).ncard ≤ 1 := by
    intro f hf
    rw [Set.ncard_le_one]
    intro x hx y hy
    obtain ⟨hfx, hxT⟩ := hx
    obtain ⟨hfy, hyT⟩ := hy
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hxT hyT
    rcases hxT with rfl | rfl | rfl <;> rcases hyT with rfl | rfl | rfl
    · rfl
    · simp only [SimpleGraph.mem_neighborSet] at hfx hfy
      exact False.elim (hvnep₁ (((hzchar f hf).mp hfx).symm.trans ((hachar f hf).mp hfy)))
    · simp only [SimpleGraph.mem_neighborSet] at hfx hfy
      exact False.elim (hvnepₙ (((hzchar f hf).mp hfx).symm.trans ((hbchar f hf).mp hfy)))
    · simp only [SimpleGraph.mem_neighborSet] at hfx hfy
      exact False.elim (hvnep₁ (((hzchar f hf).mp hfy).symm.trans ((hachar f hf).mp hfx)))
    · rfl
    · simp only [SimpleGraph.mem_neighborSet] at hfx hfy
      exact False.elim (hp₁nepₙ (((hachar f hf).mp hfx).symm.trans ((hbchar f hf).mp hfy)))
    · simp only [SimpleGraph.mem_neighborSet] at hfx hfy
      exact False.elim (hvnepₙ (((hzchar f hf).mp hfy).symm.trans ((hbchar f hf).mp hfx)))
    · simp only [SimpleGraph.mem_neighborSet] at hfx hfy
      exact False.elim (hp₁nepₙ (((hachar f hf).mp hfy).symm.trans ((hbchar f hf).mp hfx)))
    · rfl
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T hTtri F hFT hcatch with
      ⟨a₁, a₂, a₃, b₁, b₂, b₃, hTeq, hRsub, href⟩ | ⟨f, hf, htwo⟩
  · let R : Set V := {b₁, b₂, b₃}
    have hmatch : ∀ x ∈ T, ∃ r ∈ R, G.Adj x r := by
      intro x hx
      have hx' : x ∈ ({a₁, a₂, a₃} : Set V) := by
        rw [← hTeq]
        exact hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl | rfl
      · refine ⟨b₁, by simp [R], ?_⟩
        exact (href.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
      · refine ⟨b₂, by simp [R], ?_⟩
        exact (href.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · refine ⟨b₃, by simp [R], ?_⟩
        exact (href.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    have hvR : v ∈ R := by
      obtain ⟨r, hrR, hzr⟩ := hmatch z (by simp [T])
      have hrF : r ∈ F := hRsub (by simpa [R] using hrR)
      have : r = v := (hzchar r hrF).mp hzr.symm
      simpa [this] using hrR
    have hp₁R : p₁ ∈ R := by
      obtain ⟨r, hrR, har⟩ := hmatch a (by simp [T])
      have hrF : r ∈ F := hRsub (by simpa [R] using hrR)
      have : r = p₁ := (hachar r hrF).mp har.symm
      simpa [this] using hrR
    have hpₙR : pₙ ∈ R := by
      obtain ⟨r, hrR, hbr⟩ := hmatch b (by simp [T])
      have hrF : r ∈ F := hRsub (by simpa [R] using hrR)
      have : r = pₙ := (hbchar r hrF).mp hbr.symm
      simpa [this] using hrR
    have hpends : G.Adj p₁ pₙ := href.2.1.2 p₁ (by simpa [R] using hp₁R)
      pₙ (by simpa [R] using hpₙR) hp₁nepₙ
    have hplen3 : 3 ≤ p.length := by
      rw [PathBasics.pathLength_eq] at hlen
      omega
    have h0 : p[0]'(by omega) = p₁ :=
      PathBasics.getElem_zero_of_head? hhead (by omega)
    have hn : p[p.length - 1]'(by omega) = pₙ :=
      PathBasics.getElem_last_of_getLast? hlast (by omega)
    rw [← h0, ← hn] at hpends
    exact PathBasics.path_not_adj_of_gap hp (by omega) (by omega) (by omega) (by omega) hpends
  · have := hbound f hf
    omega

/-- The exact one-sided triple-RR contradiction used in claim (6) of 18.5.

At present the short proof below records that this is precisely the indicated
specialization of 17.5.  The deliberately stronger `A`/`B`/`v` interface is the
standalone target for replacing that last dependency by the source proof.
-/
theorem even_complete_edges_absurd
    (G : SimpleGraph V) (hG : InF7 G)
    (A B : Set V) (hAB : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAa : AnticonnectedSet G A) (hBa : AnticonnectedSet G B)
    (hABcomplete : Complete G A B)
    (v : V) (hvAB : v ∉ A ∪ B)
    (hvA : ¬ VertexComplete G v A) (hvB : ¬ VertexComplete G v B)
    (hBvanti : AnticonnectedSet G (B ∪ {v}))
    (hABvanti : AnticonnectedSet G (A ∪ (B ∪ {v})))
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hodd : Odd (pathLength p)) (hlen : 1 < pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hpA : ∀ w ∈ p, w ∉ A) (hpB : ∀ w ∈ p, w ∉ B)
    (hpv : v ∉ p)
    (hp₁A : VertexComplete G p₁ A)
    (hBuniq : ∀ w ∈ p, (VertexComplete G w B ↔ w = pₙ))
    (hBvuniq : ∀ w ∈ p, (VertexComplete G w (B ∪ {v}) ↔ w = pₙ))
    (z : V) (hzABv : z ∉ A ∪ (B ∪ {v})) (hzP : z ∉ p)
    (hzABvComplete : VertexComplete G z (A ∪ (B ∪ {v})))
    (hzanti : VertexAnticomplete G z {w : V | w ∈ p})
    (heven : Even {e : Sym2 V | ∃ u ∈ p, ∃ w ∈ p,
        e = s(u, w) ∧ EdgeComplete G A u w}.ncard) : False := by
  have hpBv : ∀ w ∈ p, w ∉ B ∪ {v} := by
    intro w hw hmem
    rcases hmem with hwB | hwv
    · exact hpB w hw hwB
    · rw [Set.mem_singleton_iff] at hwv
      exact hpv (hwv ▸ hw)
  by_cases hAsub : A.Subsingleton
  · obtain ⟨a, haA⟩ := hAne
    have hAeq : A = {a} := by
      ext x
      constructor
      · intro hx
        exact Set.mem_singleton_iff.mpr (hAsub hx haA)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        simpa [hx] using haA
    have hABv : Disjoint A (B ∪ {v}) := by
      rw [Set.disjoint_left]
      intro x hxA hx
      rcases hx with hxB | hxv
      · exact Set.disjoint_left.mp hAB hxA hxB
      · rw [Set.mem_singleton_iff] at hxv
        subst x
        exact hvAB (Or.inl hxA)
    let c : EvenRRConfig G A (B ∪ {v}) z :=
      { p := p
        p₁ := p₁
        pₙ := pₙ
        hp := ⟨hp, hhead, hlast⟩
        hodd := hodd
        hlong := hlen
        houtX := hpA
        houtY := hpBv
        hp₁X := hp₁A
        hYuniq := hBvuniq
        hzP := hzP
        hzanti := hzanti
        heven := heven }
    exact singleton_first_side_absurd G hG A (B ∪ {v}) hABv hAa hBvanti
      hABvanti v (Or.inr rfl) hvA z hzABv hzABvComplete a hAeq c
  have hoddEdges := _root_.Workspace.Statements.S17.SPGT.thm_17_5
    G hG p p₁ pₙ hp hodd hlen hhead hlast A (B ∪ {v}) hpA hpBv
    hAa hBvanti hABvanti hp₁A hBvuniq z hzABv hzP hzABvComplete hzanti
  exact Nat.not_odd_iff_even.mpr heven hoddEdges

end Workspace.ProofLemmas.Thm185Claim6Bridge
