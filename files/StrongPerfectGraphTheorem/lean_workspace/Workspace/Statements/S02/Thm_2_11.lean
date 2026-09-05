/-  Proof attempt for statement 2.11 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 12).

    PRINTED PROOF (verbatim, `paper/proofs/2_11.md`):

      "The proof is similar to that of 2.9.  We may assume V(G) = V(P) u X u Y.  Let G0 be
       obtained from G \ Y by adding a new vertex y with neighbour set X u {p1, pn}.  If G0 is
       Berge then the result follows from 2.10, so we may assume G0 is not Berge.  Assume first
       that there is an odd hole C of length >= 7 in G0.  Hence there is an odd path Q in G \ Y
       of length >= 5, with both ends Y-complete and no internal vertices Y-complete.  So the
       ends of Q belong to X u {p1, pn} and its interior to V(P*).  By 2.1 Y contains a leap for
       Q; so there is an odd path R of length >= 5 with ends (y1, y2 say) in Y and with interior
       in V(P*).  Since R is odd and R* is a subpath of the even path P*, it follows that not
       both p2 and p_{n-1} belong to R; but then R can be completed to an odd hole via one of
       y2-pn-y1, y2-p1-y1, a contradiction.  This completes the case when there is an odd hole in
       G0 of length >= 7, so now we may assume that there is an odd antihole in G0, say D.  Again
       D must use y, and uses exactly two nonneighbours of y; so in G there is an odd antipath Q
       between adjacent vertices of P* (say u and v), and with interior in X u {pn}.  Since u and
       v are not Y-complete, they are also joined by an antipath R with interior in Y, and R must
       also be odd since its union with Q is an antihole.  Since one of p1, pn is nonadjacent to
       both of u, v, we may complete R to an odd antihole via one of u-p1-v, u-pn-v, a
       contradiction.  This proves 2.11."

    MAP ONTO THE LEAN PROOF.

    * "We may assume V(G) = V(P) u X u Y ... G \ Y" is `RestrictGraph.restrictTo G (auxW p X)`:
      the vertex type is NOT changed, the discarded vertices are *isolated* instead.  That is
      what `RestrictGraph.mem_of_mem_hole` / `mem_of_mem_compl_hole` /
      `notMem_compl_hole_of_isolated` deliver, and it avoids the `induce`-reassociation that
      this Mathlib checkout lacks.  `auxG0` is then `AddPendantVertexTransport.addPendantVertex`
      of that graph at `auxS X p1 pn = X u {p1, pn}`.
    * `branch_berge` is *"If G0 is Berge then the result follows from 2.10"*.  The hole fed to
      2.10 is `y :: p.map Sum.inl` (`PrismBasics.isHoleList_of_path_add_vertex`), the edge is
      `y p1`, and `X'` is `Sum.inl '' X` (anticonnected by
      `PendantTransport.anticonnectedSet_pendant_restrict`).  2.10's *hat* outcome is disjunct 1
      verbatim; its *leap* outcome is disjunct 2, the leap vertices being adjacent on `p.tail`
      only at `p2` resp. `pn`.  Of the two leap orientations only one is possible - the other
      would need a rotation of the hole with head `y` and last `p1`, but that rotation is the
      hole itself, whose last vertex is `pn`.
    * `branch_hole` is the printed odd-hole case, and also disposes of an odd hole of length 5
      through `PathGlue.isHoleList_compl_of_length_five` (*"an odd hole of length 5 is also an
      odd antihole"*).  *"R* is a subpath of the even path P*"* is
      `PathGlue.exists_pos_of_subpath`: its `|f s - f t| <= |s - t|` clause bounds `|R*|` below
      and injectivity of `f` into the index range bounds it above, forcing `|R*| = n - 2` and
      hence `R` even - contradicting `R` odd.  Otherwise `p2` or `p_{n-1}` is off `R`, and then
      `p1 :: R` resp. `pn :: R` is an odd hole.
    * `branch_antihole` is the printed odd-antihole case.  `HoleMinusVertexPath` supplies
      `D \ y` as a path after `y` is rotated to position 0.
    * ONE PRINTED SLIP.  The odd-antihole paragraph says the interior of `Q` lies in `X u {pn}`;
      with `N(y) = X u {p1, pn}` it is `X u {p1, pn}`, and the paragraph's own next-but-one
      sentence ("one of p1, pn is nonadjacent to both of u, v ... via one of u-p1-v, u-pn-v")
      uses both `p1` and `pn`.  The `X u {pn}` is inherited from 2.9, where `N(y) = X u {pn}`.
      The proof here uses the corrected reading.

    Together the two non-Berge branches show every hole and every antihole of `G0` is even, i.e.
    `G0` IS Berge - so the printed "we may assume G0 is not Berge" is a proof by contradiction
    whose net effect is to discharge the hypothesis of `branch_berge`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.RestrictGraph
import Workspace.ProofLemmas.PendantTransport
import Workspace.ProofLemmas.AddPendantVertexTransport
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_10

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.AddPendantVertexTransport

namespace SPGT

section Aux

variable {V : Type*}

/-- The kept vertex set: `V(P) ∪ X`.  (The paper's *"we may assume `V(G) = V(P) ∪ X ∪ Y`"*
followed by *"`G \ Y`"*.) -/
private def auxW (p : List V) (X : Set V) : Set V := {w | w ∈ p} ∪ X

/-- The neighbour set of the new vertex `y`: `X ∪ {p₁, pₙ}`. -/
private def auxS (X : Set V) (p₁ pn : V) : Set V := X ∪ {p₁, pn}

/-- `G \ Y`, realised by isolating rather than deleting. -/
private def auxG (G : SimpleGraph V) (p : List V) (X : Set V) : SimpleGraph V :=
  RestrictGraph.restrictTo G (auxW p X)

/-- `G₀`: `G \ Y` with the new vertex `y` attached to `X ∪ {p₁, pₙ}`. -/
private def auxG0 (G : SimpleGraph V) (p : List V) (X : Set V) (p₁ pn : V) : SimpleGraph (V ⊕ Unit) :=
  addPendantVertex (auxG G p X) (auxS X p₁ pn)

private theorem mem_auxW {p : List V} {X : Set V} {a : V} : a ∈ auxW p X ↔ (a ∈ p ∨ a ∈ X) := Iff.rfl

private theorem mem_auxS {X : Set V} {p₁ pn a : V} : a ∈ auxS X p₁ pn ↔ (a ∈ X ∨ a = p₁ ∨ a = pn) := by
  simp only [auxS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]

private theorem auxG0_adj_inl {G : SimpleGraph V} {p : List V} {X : Set V} {p₁ pn : V} (a b : V) :
    (auxG0 G p X p₁ pn).Adj (Sum.inl a) (Sum.inl b) ↔
      (G.Adj a b ∧ (a ∈ p ∨ a ∈ X) ∧ (b ∈ p ∨ b ∈ X)) := by
  rw [auxG0, adj_inl_inl]
  exact Iff.rfl

private theorem auxG0_adj_inr {G : SimpleGraph V} {p : List V} {X : Set V} {p₁ pn : V} (a : V)
    (t : Unit) :
    (auxG0 G p X p₁ pn).Adj (Sum.inl a) (Sum.inr t) ↔ (a ∈ X ∨ a = p₁ ∨ a = pn) := by
  rw [auxG0, adj_inl_inr]
  exact mem_auxS

private theorem auxG0_adj_inr' {G : SimpleGraph V} {p : List V} {X : Set V} {p₁ pn : V} (a : V)
    (t : Unit) :
    (auxG0 G p X p₁ pn).Adj (Sum.inr t) (Sum.inl a) ↔ (a ∈ X ∨ a = p₁ ∨ a = pn) := by
  rw [auxG0, adj_inr_inl]
  exact mem_auxS

end Aux

section Branch1

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem rotate_head_eq {α : Type*} {l : List α} (hnd : l.Nodup) {i k : ℕ}
    (hk : k < l.length) (h : (l.rotate i).head? = some (l[k]'hk)) :
    l.rotate i = l.rotate k := by
  have hpos : 0 < l.length := by omega
  have hposr : 0 < (l.rotate i).length := by rw [List.length_rotate]; omega
  have h0 : ((l.rotate i)[0]'hposr) = (l[k]'hk) := PathBasics.getElem_zero_of_head? h hposr
  have hmodlt : i % l.length < l.length := Nat.mod_lt _ hpos
  have hget : ((l.rotate i)[0]'hposr) = (l[i % l.length]'hmodlt) := by
    simp only [List.getElem_rotate, List.length_rotate, Nat.zero_add]
  rw [hget] at h0
  have hik : i % l.length = k := hnd.getElem_inj_iff.mp h0
  rw [← List.rotate_mod l i, hik]

private theorem branch_berge {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    (hXa : AnticonnectedSet G X) {p : List V} {p₁ pn : V}
    (hp : IsPathList G p) (hpX : ∀ w ∈ p, w ∉ X)
    (hn5 : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hBerge : Berge (auxG0 G p X p₁ pn)) :
    (∃ x ∈ X, ∀ w ∈ p.tail, ¬ G.Adj x w) ∨
    (∃ x₁ ∈ X, ∃ x₂ ∈ X, ¬ G.Adj x₁ x₂ ∧ IsPathList G (x₁ :: (p.tail ++ [x₂]))) := by
  classical
  have hpos : 0 < p.length := by omega
  have hp0 : (p[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
  have hplast : (p[p.length - 1]'(by omega)) = pn :=
    PathBasics.getElem_last_of_getLast? hlast (by omega)
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hPF : IsPathFrom G p p₁ pn := ⟨hp, hhead, hlast⟩
  have hne1n : p₁ ≠ pn := PathBasics.isPathFrom_ends_ne hPF (by simp only [pathLength]; omega)
  have hXW : X ⊆ auxW p X := fun z hz => Or.inr hz
  have hpW : ∀ z ∈ p, z ∈ auxW p X := fun z hz => Or.inl hz
  have hp' : IsPathFrom (auxG G p X) p p₁ pn :=
    (RestrictGraph.isPathFrom_iff_of_subset hpW).mpr hPF
  have hpmap : IsPathFrom (auxG0 G p X p₁ pn) (p.map Sum.inl) (Sum.inl p₁) (Sum.inl pn) :=
    (isPathFrom_map_inl (auxG G p X) (auxS X p₁ pn) p p₁ pn).mp hp'
  have hylen : (p.map (Sum.inl : V → V ⊕ Unit)).length = p.length := List.length_map ..
  have hyp1 : (auxG0 G p X p₁ pn).Adj (Sum.inr ()) (Sum.inl p₁) :=
    (auxG0_adj_inr' p₁ ()).mpr (Or.inr (Or.inl rfl))
  have hypn : (auxG0 G p X p₁ pn).Adj (Sum.inr ()) (Sum.inl pn) :=
    (auxG0_adj_inr' pn ()).mpr (Or.inr (Or.inr rfl))
  have hynotmem : (Sum.inr () : V ⊕ Unit) ∉ p.map Sum.inl := by
    intro h
    obtain ⟨z, -, hz⟩ := List.mem_map.mp h
    exact absurd hz (by simp)
  have hyint : ∀ z ∈ SPGT.interior (p.map (Sum.inl : V → V ⊕ Unit)),
      ¬ (auxG0 G p X p₁ pn).Adj (Sum.inr ()) z := by
    intro z hz
    rw [interior_map] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    have hw' := (PathBasics.mem_interior_iff_of_pathFrom hPF).mp hw
    rw [auxG0_adj_inr']
    rintro (hc | hc | hc)
    · exact hpX w hw'.1 hc
    · exact hw'.2.1 hc
    · exact hw'.2.2 hc
  have hplen2 : 2 ≤ pathLength (p.map (Sum.inl : V → V ⊕ Unit)) := by
    simp only [pathLength, hylen]
    omega
  have hhole : IsHoleList (auxG0 G p X p₁ pn) (Sum.inr () :: p.map Sum.inl) :=
    PrismBasics.isHoleList_of_path_add_vertex hpmap hplen2 hyp1 hypn hynotmem hyint
  have hX' : AnticonnectedSet (auxG0 G p X p₁ pn) (Sum.inl '' X) :=
    PendantTransport.anticonnectedSet_pendant_restrict hXW hXa
  have hmemC : ∀ z : V ⊕ Unit, z ∈ (Sum.inr () :: p.map Sum.inl) ↔
      (z = Sum.inr () ∨ ∃ w ∈ p, z = Sum.inl w) := by
    intro z
    rw [List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
        exact Or.inr ⟨w, hw, rfl⟩
    · rintro (h | ⟨w, hw, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have hcX : ∀ z ∈ (Sum.inr () :: p.map Sum.inl), z ∉ Sum.inl '' X := by
    intro z hz
    rcases (hmemC z).mp hz with rfl | ⟨w, hw, rfl⟩
    · exact PendantTransport.inr_notMem_image_inl
    · rintro ⟨x, hx, hxe⟩
      exact hpX w hw (Sum.inl_injective hxe ▸ hx)
  have hcu : VertexComplete (auxG0 G p X p₁ pn) (Sum.inr ()) (Sum.inl '' X) := by
    rintro z ⟨x, hx, rfl⟩
    exact (auxG0_adj_inr' x ()).mpr (Or.inl hx)
  have hcv : VertexComplete (auxG0 G p X p₁ pn) (Sum.inl p₁) (Sum.inl '' X) := by
    rintro z ⟨x, hx, rfl⟩
    exact (auxG0_adj_inl p₁ x).mpr
      ⟨(hXuniq p₁ hp₁mem).mpr rfl x hx, Or.inl hp₁mem, Or.inr hx⟩
  have honly : ∀ z ∈ (Sum.inr () :: p.map Sum.inl),
      VertexComplete (auxG0 G p X p₁ pn) z (Sum.inl '' X) → z = Sum.inr () ∨ z = Sum.inl p₁ := by
    intro z hz hzc
    rcases (hmemC z).mp hz with rfl | ⟨w, hw, rfl⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have hvc : VertexComplete G w X := by
        intro x hx
        exact ((auxG0_adj_inl w x).mp (hzc (Sum.inl x) ⟨x, hx, rfl⟩)).1
      rw [(hXuniq w hw).mp hvc]
  have hClen : 4 < holeLength (Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit)) := by
    simp only [holeLength, List.length_cons, hylen]
    omega
  have hymem : (Sum.inr () : V ⊕ Unit) ∈ (Sum.inr () :: p.map Sum.inl) := by simp
  have hp1mem' : (Sum.inl p₁ : V ⊕ Unit) ∈ (Sum.inr () :: p.map Sum.inl) := by
    exact (hmemC _).mpr (Or.inr ⟨p₁, hp₁mem, rfl⟩)
  have h210 := thm_2_10 (auxG0 G p X p₁ pn) hBerge (Sum.inl '' X) hX'
    (Sum.inr () :: p.map Sum.inl) hhole hcX hClen
    (Sum.inr ()) (Sum.inl p₁) hymem hp1mem' hyp1 hcu hcv honly
  -- `p = p₁ :: p.tail`
  have hpcons : p = p₁ :: p.tail := by
    cases hpe : p with
    | nil => rw [hpe] at hhead; simp at hhead
    | cons z t =>
      rw [hpe] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead]
  have hp₁notmem : p₁ ∉ p.tail := by
    have hnd := hp.2.1
    rw [hpcons] at hnd
    exact (List.nodup_cons.mp hnd).1
  have htailsub : ∀ w ∈ p.tail, w ∈ p := fun w hw => List.tail_subset p hw
  have htailidx : ∀ w ∈ p.tail, ∃ (k : ℕ) (hk : k < p.length), 1 ≤ k ∧ (p[k]'hk) = w := by
    intro w hw
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem (htailsub w hw)
    refine ⟨k, hk, ?_, hkeq⟩
    by_contra hc
    have hk0 : k = 0 := by omega
    subst hk0
    rw [hp0] at hkeq
    exact hp₁notmem (hkeq ▸ hw)
  have hmemtail : ∀ (k : ℕ) (hk : k < p.length), 1 ≤ k → (p[k]'hk) ∈ p.tail := by
    intro k hk hk1
    rw [← List.drop_one]
    have hlt : k - 1 < (p.drop 1).length := by simp only [List.length_drop]; omega
    have h1 : ((p.drop 1)[k - 1]'hlt) = (p[1 + (k - 1)]'(by simp only [List.length_drop] at hlt; omega)) :=
      List.getElem_drop ..
    have heq : ((p.drop 1)[k - 1]'hlt) = (p[k]'hk) := by
      rw [h1]
      exact hp.2.1.getElem_inj_iff.mpr (by omega)
    rw [← heq]
    exact List.getElem_mem hlt
  rcases h210 with ⟨hv, hvX, hhat⟩ | ⟨a, haX, b, hbX, hleap⟩
  · -- HAT: the paper's disjunct 1
    obtain ⟨x₀, hx₀X, rfl⟩ := hvX
    refine Or.inl ⟨x₀, hx₀X, ?_⟩
    intro w hw hadj
    have hwp : w ∈ p := htailsub w hw
    have hwne : w ≠ p₁ := fun h => hp₁notmem (h ▸ hw)
    exact hhat.2.2.2.2.2.2 (Sum.inl w) ((hmemC _).mpr (Or.inr ⟨w, hwp, rfl⟩))
      (by simp) (by simp [hwne]) ((auxG0_adj_inl x₀ w).mpr ⟨hadj, Or.inr hx₀X, Or.inl hwp⟩)
  · -- LEAP: the paper's disjunct 2
    obtain ⟨a₀, ha₀X, rfl⟩ := haX
    obtain ⟨b₀, hb₀X, rfl⟩ := hbX
    have hCne : (p.map (Sum.inl : V → V ⊕ Unit)) ≠ [] := by
      simpa using PathBasics.path_ne_nil hp
    have hClen1 : (Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit)).length = p.length + 1 := by simp
    have hCnd : (Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit)).Nodup := hhole.2.1
    have hC0 : ((Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit))[0]'(by omega)) = Sum.inr () := rfl
    have hC1 : ((Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit))[1]'(by omega)) = Sum.inl p₁ := by
      show ((p.map (Sum.inl : V → V ⊕ Unit))[0]'(by simpa using hpos)) = Sum.inl p₁
      rw [List.getElem_map, hp0]
    have hClast : (Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit)).getLast? = some (Sum.inl pn) := by
      rw [List.getLast?_cons_of_ne_nil hCne, List.getLast?_map, hlast]
      rfl
    -- transfer of adjacency across the edge deletion
    have hHinl : ∀ (e : Sym2 (V ⊕ Unit)) (x y : V),
        (∃ z : V ⊕ Unit, e = s(Sum.inr (), z) ∨ e = s(z, Sum.inr ())) →
        ((((auxG0 G p X p₁ pn).deleteEdges {e}).Adj (Sum.inl x) (Sum.inl y)) ↔
          (G.Adj x y ∧ (x ∈ p ∨ x ∈ X) ∧ (y ∈ p ∨ y ∈ X))) := by
      rintro e x y ⟨z, hz | hz⟩ <;> subst hz <;>
        rw [SimpleGraph.deleteEdges_adj, auxG0_adj_inl] <;>
        constructor <;> intro h
      · exact h.1
      · exact ⟨h, by simp [Sym2.eq_iff]⟩
      · exact h.1
      · exact ⟨h, by simp [Sym2.eq_iff]⟩
    -- the rotation whose head is `Sum.inl p₁` is `p.map inl ++ [y]`
    have hmain : ∀ (i : ℕ) (e : Sym2 (V ⊕ Unit)),
        (∃ z : V ⊕ Unit, e = s(Sum.inr (), z) ∨ e = s(z, Sum.inr ())) →
        ((Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit)).rotate i).head? = some (Sum.inl p₁) →
        IsLeapForPath (((auxG0 G p X p₁ pn).deleteEdges {e}))
          ((Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit)).rotate i) (Sum.inl a₀) (Sum.inl b₀) →
        (∀ w ∈ p.tail, (G.Adj a₀ w ↔ w = (p[1]'(by omega)))) ∧
        (∀ w ∈ p.tail, (G.Adj b₀ w ↔ w = pn)) ∧ ¬ G.Adj a₀ b₀ ∧ a₀ ≠ b₀ := by
      intro i e he hhd hlp
      have hreq : (Sum.inr () :: p.map (Sum.inl : V → V ⊕ Unit)).rotate i
          = p.map Sum.inl ++ [Sum.inr ()] := by
        rw [rotate_head_eq hCnd (k := 1) (by omega) (by rw [hC1]; exact hhd)]
        rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
      rw [hreq] at hlp
      obtain ⟨-, -, hab, hnab, hlpa, hlpb⟩ := hlp
      have hRlen : (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]).length = p.length + 1 := by
        simp
      have hRget : ∀ (k : ℕ) (hk : k < p.length)
          (hk' : k < (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]).length),
          ((p.map Sum.inl ++ [Sum.inr ()])[k]'hk') = Sum.inl (p[k]'hk) := by
        intro k hk hk'
        have hklt : k < (p.map (Sum.inl : V → V ⊕ Unit)).length := by simpa using hk
        rw [List.getElem_append_left hklt, List.getElem_map]
      have hAdj : ∀ (x : V), x ∈ X → ∀ (k : ℕ) (hk : k < p.length),
          (((auxG0 G p X p₁ pn).deleteEdges {e}).Adj (Sum.inl x)
            ((p.map Sum.inl ++ [Sum.inr ()])[k]'(by omega))) ↔ G.Adj x (p[k]'hk) := by
        intro x hx k hk
        rw [hRget k hk (by omega), hHinl e x (p[k]'hk) he]
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, Or.inr hx, Or.inl (List.getElem_mem hk)⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w hw
        obtain ⟨k, hk, hk1, rfl⟩ := htailidx w hw
        rw [← hAdj a₀ ha₀X k hk, hlpa k (by omega)]
        constructor
        · intro h
          have hk1' : k = 1 := by omega
          subst hk1'
          rfl
        · intro h
          have : k = 1 := hp.2.1.getElem_inj_iff.mp h
          omega
      · intro w hw
        obtain ⟨k, hk, hk1, rfl⟩ := htailidx w hw
        rw [← hAdj b₀ hb₀X k hk, hlpb k (by omega)]
        constructor
        · intro h
          have hk2 : k = p.length - 1 := by omega
          subst hk2
          exact hplast
        · intro h
          rw [← hplast] at h
          have : k = p.length - 1 := hp.2.1.getElem_inj_iff.mp h
          omega
      · intro hadj
        exact hnab ((hHinl e a₀ b₀ he).mpr ⟨hadj, Or.inr ha₀X, Or.inr hb₀X⟩)
      · intro hc
        exact hab (by rw [hc])
    -- the second orientation is impossible: its rotation is `C` itself, whose last vertex is `pₙ`
    have hprofiles : (∀ w ∈ p.tail, (G.Adj a₀ w ↔ w = (p[1]'(by omega)))) ∧
        (∀ w ∈ p.tail, (G.Adj b₀ w ↔ w = pn)) ∧ ¬ G.Adj a₀ b₀ ∧ a₀ ≠ b₀ ∨
        (∀ w ∈ p.tail, (G.Adj b₀ w ↔ w = (p[1]'(by omega)))) ∧
        (∀ w ∈ p.tail, (G.Adj a₀ w ↔ w = pn)) ∧ ¬ G.Adj b₀ a₀ ∧ b₀ ≠ a₀ := by
      rcases hleap with ⟨-, i, hhd, hlst, hlp⟩ | ⟨-, i, hhd, hlst, hlp⟩
      · exact Or.inl (hmain i _ ⟨Sum.inl p₁, Or.inl rfl⟩ hhd hlp)
      · exfalso
        rw [rotate_head_eq hCnd (k := 0) (by omega) (by rw [hC0]; exact hhd),
          List.rotate_zero] at hlst
        rw [hClast] at hlst
        exact hne1n (Sum.inl_injective (Option.some_injective _ hlst)).symm
    -- assemble the path `x₁-p₂-⋯-pₙ-x₂`
    have hbuild : ∀ (x₁ x₂ : V), x₁ ∈ X → x₂ ∈ X →
        (∀ w ∈ p.tail, (G.Adj x₁ w ↔ w = (p[1]'(by omega)))) →
        (∀ w ∈ p.tail, (G.Adj x₂ w ↔ w = pn)) → ¬ G.Adj x₁ x₂ → x₁ ≠ x₂ →
        IsPathList G (x₁ :: (p.tail ++ [x₂])) := by
      intro x₁ x₂ hx₁ hx₂ hA hB hnadj hne
      have htailpath : IsPathFrom G p.tail (p[1]'(by omega)) pn := by
        refine ⟨?_, ?_, ?_⟩
        · rw [← List.drop_one]
          exact PathBasics.isPathList_drop hp (by omega)
        · rw [← List.drop_one, List.head?_drop, List.getElem?_eq_getElem (by omega)]
        · rw [← List.drop_one, List.getLast?_drop, if_neg (by omega)]
          exact hlast
      have hx₁tail : x₁ ∉ p.tail := fun h => hpX x₁ (htailsub x₁ h) hx₁
      have hx₂tail : x₂ ∉ p.tail := fun h => hpX x₂ (htailsub x₂ h) hx₂
      refine (PathAttach.isPathFrom_cons_concat htailpath ?_ ?_ hnadj hne hx₁tail hx₂tail
        ?_ ?_).1
      · exact (hA _ (hmemtail 1 (by omega) (by omega))).mpr rfl
      · refine (hB pn ?_).mpr rfl
        rw [← hplast]
        exact hmemtail (p.length - 1) (by omega) (by omega)
      · intro z hz hzne hadj
        exact hzne ((hA z hz).mp hadj)
      · intro z hz hzne hadj
        exact hzne ((hB z hz).mp hadj)
    rcases hprofiles with ⟨hA, hB, hnadj, hne⟩ | ⟨hA, hB, hnadj, hne⟩
    · exact Or.inr ⟨a₀, ha₀X, b₀, hb₀X, hnadj, hbuild a₀ b₀ ha₀X hb₀X hA hB hnadj hne⟩
    · exact Or.inr ⟨b₀, hb₀X, a₀, ha₀X, hnadj, hbuild b₀ a₀ hb₀X ha₀X hA hB hnadj hne⟩

end Branch1


section Branch3

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem getElem_congr_idx {α : Type*} (l : List α) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (h : a = b) : (l[a]'ha) = (l[b]'hb) := by subst h; rfl

/-- The printed *"now we may assume that there is an odd antihole in `G₀`, say `D` … a
contradiction"*: every antihole of `G₀` has even length. -/
private theorem branch_antihole {G : SimpleGraph V} (hG : Berge G) {X Y : Set V}
    (hXY : Disjoint X Y) (hYa : AnticonnectedSet G Y) (hcompl : Complete G X Y)
    {p : List V} {p₁ pn : V}
    (hp : IsPathList G p) (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (hn5 : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ (w = p₁ ∨ w = pn)))
    (d : List (V ⊕ Unit)) (hd : IsHoleList ((auxG0 G p X p₁ pn)ᶜ) d) :
    Even (holeLength d) := by
  classical
  have hpos : 0 < p.length := by omega
  have hp0 : (p[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
  have hplast : (p[p.length - 1]'(by omega)) = pn :=
    PathBasics.getElem_last_of_getLast? hlast (by omega)
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hPF : IsPathFrom G p p₁ pn := ⟨hp, hhead, hlast⟩
  have hne1n : p₁ ≠ pn := PathBasics.isPathFrom_ends_ne hPF (by simp only [pathLength]; omega)
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hc => hpXY w hw (Or.inl hc)
  have hpY : ∀ w ∈ p, w ∉ Y := fun w hw hc => hpXY w hw (Or.inr hc)
  have hXnY : ∀ x ∈ X, x ∉ Y := fun x hx hc => (Set.disjoint_left.mp hXY) hx hc
  by_contra hnoteven
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hnoteven
  simp only [holeLength] at hnoteven
  have h4 : 4 ≤ d.length := hd.1
  have h5 : 5 ≤ d.length := by omega
  by_cases hy : (Sum.inr () : V ⊕ Unit) ∈ d
  case neg =>
    obtain ⟨d₀, hd₀eq, hd₀len⟩ := exists_eq_map_inl (fun x hx heq => hy (heq ▸ hx))
    have h1 : IsHoleList ((auxG G p X)ᶜ) d₀ :=
      (isHoleList_compl_map_inl (auxG G p X) (auxS X p₁ pn) d₀).mpr (by rw [← hd₀eq]; exact hd)
    have h3 := hG.2 d₀ (RestrictGraph.isHoleList_compl_of_restrict h1)
    rw [Nat.even_iff] at h3
    simp only [holeLength] at h3
    omega
  -- rotate `y` into position `0`
  obtain ⟨c, hc, hclen, hc0, hcmem⟩ :
      ∃ c : List (V ⊕ Unit), IsHoleList ((auxG0 G p X p₁ pn)ᶜ) c ∧ c.length = d.length ∧
        (∀ (h : 0 < c.length), ((c)[0]'h) = Sum.inr ()) ∧ (∀ z, z ∈ c ↔ z ∈ d) := by
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
    refine ⟨d.rotate j, HoleBasics.isHoleList_rotate hd j, List.length_rotate .., ?_,
      fun z => List.mem_rotate⟩
    intro h
    have hjlt : (0 + j) % d.length < d.length := Nat.mod_lt _ (by omega)
    have hget : ((d.rotate j)[0]'h) = ((d)[(0 + j) % d.length]'hjlt) := by
      simp only [List.getElem_rotate, List.length_rotate]
    rw [hget]
    exact (getElem_congr_idx d hjlt hj (by rw [Nat.zero_add, Nat.mod_eq_of_lt hj])).trans hjy
  have hc5 : 5 ≤ c.length := by omega
  have hcy : ((c)[0]'(by omega)) = Sum.inr () := hc0 (by omega)
  have hcnd : c.Nodup := hc.2.1
  -- every vertex of `c` other than `y` is an old vertex of `V(P) ∪ X`
  have hcvert : ∀ z ∈ c, z = Sum.inr () ∨ ∃ w : V, (w ∈ p ∨ w ∈ X) ∧ z = Sum.inl w := by
    intro z hz
    cases z with
    | inr t => exact Or.inl (by cases t; rfl)
    | inl w =>
      refine Or.inr ⟨w, ?_, rfl⟩
      by_contra hw
      refine RestrictGraph.notMem_compl_hole_of_isolated hc (z := Sum.inl w) ?_ hz
      intro u
      cases u with
      | inl u' => exact fun hadj => hw ((auxG0_adj_inl w u').mp hadj).2.1
      | inr t =>
        rw [auxG0_adj_inr]
        rintro (hcx | hcx | hcx)
        · exact hw (Or.inr hcx)
        · exact hw (Or.inl (hcx ▸ hp₁mem))
        · exact hw (Or.inl (hcx ▸ hpnmem))
  -- the two `G₀ᶜ`-neighbours of `y` are old vertices of `P*`
  have hnbr : ∀ (i : ℕ) (hi : i < c.length), (i = 1 ∨ i = c.length - 1) →
      ∃ w : V, w ∈ p ∧ w ≠ p₁ ∧ w ≠ pn ∧ ((c)[i]'hi) = Sum.inl w := by
    intro i hi hor
    have hadj : ((auxG0 G p X p₁ pn)ᶜ).Adj ((c)[0]'(by omega)) ((c)[i]'hi) :=
      (HoleMinusVertexPath.adj_head_iff hc hc5 hi).mpr hor
    have hne : ((c)[i]'hi) ≠ Sum.inr () := by
      rw [← hcy]
      intro h
      have hi0 : i = 0 := hcnd.getElem_inj_iff.mp h
      omega
    rcases hcvert _ (List.getElem_mem hi) with h | ⟨w, hw, hweq⟩
    · exact absurd h hne
    have hnadj : ¬ (auxG0 G p X p₁ pn).Adj (Sum.inr ()) (Sum.inl w) := by
      rw [← hcy, ← hweq]
      exact hadj.2
    rw [auxG0_adj_inr'] at hnadj
    push Not at hnadj
    rcases hw with hwp | hwX
    · exact ⟨w, hwp, hnadj.2.1, hnadj.2.2, hweq⟩
    · exact absurd hwX hnadj.1
  obtain ⟨u₀, hu₀p, hu₀1, hu₀n, hu₀eq⟩ := hnbr 1 (by omega) (Or.inl rfl)
  obtain ⟨v₀, hv₀p, hv₀1, hv₀n, hv₀eq⟩ := hnbr (c.length - 1) (by omega) (Or.inr rfl)
  have huvne : u₀ ≠ v₀ := by
    intro h
    exact HoleMinusVertexPath.ends_ne hc hc5 (by rw [hu₀eq, hv₀eq, h])
  have huvadj : G.Adj u₀ v₀ := by
    have h1 := HoleMinusVertexPath.ends_not_adj hc hc5
    rw [hu₀eq, hv₀eq] at h1
    by_contra hcon
    exact h1 ⟨fun hq => huvne (Sum.inl_injective hq),
      fun hq => hcon ((auxG0_adj_inl u₀ v₀).mp hq).1⟩
  have hQ : IsPathFrom ((auxG0 G p X p₁ pn)ᶜ) c.tail (Sum.inl u₀) (Sum.inl v₀) := by
    have h := HoleMinusVertexPath.isPathFrom_tail hc hc5
    rwa [hu₀eq, hv₀eq] at h
  have hQlen : c.tail.length = c.length - 1 := by simp
  have hQnoy : ∀ z ∈ c.tail, z ≠ Sum.inr () := by
    intro z hz
    rw [HoleMinusVertexPath.mem_tail_iff hc hc5] at hz
    rw [← hcy]
    exact hz.2
  obtain ⟨Q₀, hQ₀eq, hQ₀len⟩ := exists_eq_map_inl hQnoy
  have hQ₀W : ∀ w ∈ Q₀, w ∈ auxW p X := by
    intro w hw
    have hmt : (Sum.inl w : V ⊕ Unit) ∈ c.tail := by
      rw [hQ₀eq]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rcases hcvert _ (List.mem_of_mem_tail hmt) with h | ⟨w', hw', hw'eq⟩
    · exact absurd h (by simp)
    · rw [Sum.inl_injective hw'eq]
      exact hw'
  have hQ₀ : IsPathFrom Gᶜ Q₀ u₀ v₀ := by
    have h1 : IsPathFrom ((auxG G p X)ᶜ) Q₀ u₀ v₀ :=
      (isPathFrom_compl_map_inl (auxG G p X) (auxS X p₁ pn) Q₀ u₀ v₀).mpr (by
        rw [← hQ₀eq]; exact hQ)
    exact (RestrictGraph.isAntipathFrom_iff_of_subset hQ₀W).mp h1
  have hQ₀plen : pathLength Q₀ = c.length - 2 := by
    simp only [pathLength, hQ₀len, hQlen]
    omega
  have hQ₀odd : pathLength Q₀ % 2 = 1 := by omega
  have hQ₀int : ∀ w ∈ SPGT.interior Q₀, (w ∈ X ∨ w = p₁ ∨ w = pn) := by
    intro w hw
    have hmi : (Sum.inl w : V ⊕ Unit) ∈ SPGT.interior c.tail := by
      rw [hQ₀eq, interior_map]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [HoleMinusVertexPath.mem_interior_tail_iff hc hc5] at hmi
    obtain ⟨hmem, hn0, hn1, hnl⟩ := hmi
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hmem
    have hi0 : i ≠ 0 := fun h => hn0 (by subst h; exact hieq.symm)
    have hi1 : i ≠ 1 := fun h => hn1 (by subst h; exact hieq.symm)
    have hil : i ≠ c.length - 1 := fun h => hnl (by subst h; exact hieq.symm)
    have hnotadj : ¬ ((auxG0 G p X p₁ pn)ᶜ).Adj (Sum.inr ()) (Sum.inl w) := by
      rw [← hcy, ← hieq]
      intro hadj
      have := (HoleMinusVertexPath.adj_head_iff hc hc5 hi).mp hadj
      omega
    have hadj0 : (auxG0 G p X p₁ pn).Adj (Sum.inr ()) (Sum.inl w) := by
      by_contra hcon
      exact hnotadj ⟨by simp, hcon⟩
    rw [auxG0_adj_inr'] at hadj0
    exact hadj0
  -- the antipath `R` between `u₀` and `v₀` with interior in `Y`
  have hu₀nY : u₀ ∉ Y := hpY u₀ hu₀p
  have hv₀nY : v₀ ∉ Y := hpY v₀ hv₀p
  have hu₀nc : ∃ z ∈ Y, ¬ G.Adj u₀ z := by
    by_contra hcon
    push Not at hcon
    rcases (hYuniq u₀ hu₀p).mp hcon with h | h
    · exact hu₀1 h
    · exact hu₀n h
  have hv₀nc : ∃ z ∈ Y, ¬ G.Adj v₀ z := by
    by_contra hcon
    push Not at hcon
    rcases (hYuniq v₀ hv₀p).mp hcon with h | h
    · exact hv₀1 h
    · exact hv₀n h
  obtain ⟨R, hR, hRint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hYa hu₀nY hv₀nY hu₀nc hv₀nc
  have hRl : IsPathList Gᶜ R := hR.1
  have hRpos : 0 < R.length := PathBasics.path_length_pos hRl
  have hRlen1 : R.length = pathLength R + 1 := PathBasics.length_eq_pathLength_add_one hRl
  have hR2 : 2 ≤ R.length := by
    by_contra hcon
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by omega : R.length = 1)
    have e1 : a = u₀ := by simpa using hR.2.1
    have e2 : a = v₀ := by simpa using hR.2.2
    exact huvne (e1.symm.trans e2)
  have hR3 : 3 ≤ R.length := by
    by_contra hcon
    have h2 : pathLength R = 1 := by simp only [pathLength]; omega
    exact (PathBasics.isPathFrom_ends_adj_of_length_one hR h2).2 huvadj
  have hR0 : ((R)[0]'(by omega)) = u₀ := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
  have hRn : ((R)[R.length - 1]'(by omega)) = v₀ :=
    PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
  have hRnd : R.Nodup := hRl.2.1
  have hRinj : ∀ (i j : ℕ) (hi : i < R.length) (hj : j < R.length),
      (((R)[i]'hi) = ((R)[j]'hj)) ↔ i = j := fun i j hi hj => hRnd.getElem_inj_iff
  have hIR : IsPathFrom Gᶜ (SPGT.interior R) ((R)[1]'(by omega))
      ((R)[R.length - 2]'(by omega)) := PathGlue.isPathFrom_interior hRl (by omega)
  have hRrev : IsPathFrom Gᶜ (SPGT.interior R).reverse ((R)[R.length - 2]'(by omega))
      ((R)[1]'(by omega)) := PathBasics.isPathFrom_reverse hIR
  have hRB : ∀ z ∈ (SPGT.interior R).reverse, z ∈ Y :=
    fun z hz => hRint z (List.mem_reverse.mp hz)
  have hQsplit : ∀ x ∈ Q₀, x = u₀ ∨ x = v₀ ∨ x ∈ SPGT.interior Q₀ := by
    intro x hx
    by_cases h1 : x = u₀
    · exact Or.inl h1
    by_cases h2 : x = v₀
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hQ₀).mpr ⟨hx, h1, h2⟩))
  have hintQY : ∀ x ∈ SPGT.interior Q₀, ∀ z ∈ Y, G.Adj x z := by
    intro x hx z hz
    rcases hQ₀int x hx with h | h | h
    · exact hcompl x h z hz
    · rw [h]; exact ((hYuniq p₁ hp₁mem).mpr (Or.inl rfl)) z hz
    · rw [h]; exact ((hYuniq pn hpnmem).mpr (Or.inr rfl)) z hz
  have hdisj : ∀ x ∈ Q₀, x ∉ (SPGT.interior R).reverse := by
    intro x hx hxR
    have hxY : x ∈ Y := hRB x hxR
    rcases hQsplit x hx with h | h | hxi
    · exact hu₀nY (h ▸ hxY)
    · exact hv₀nY (h ▸ hxY)
    · exact G.irrefl (hintQY x hxi x hxY)
  have hcross : ∀ x ∈ Q₀, ∀ z ∈ (SPGT.interior R).reverse,
      (Gᶜ.Adj x z ↔ ((x = v₀ ∧ z = ((R)[R.length - 2]'(by omega))) ∨
        (x = u₀ ∧ z = ((R)[1]'(by omega))))) := by
    intro x hx z hz
    obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
      PathBasics.exists_getElem_of_mem_interior hRl (List.mem_reverse.mp hz)
    have hA_u : Gᶜ.Adj u₀ ((R)[k]'hk) ↔ k = 1 := by
      constructor
      · intro h
        rw [← hR0] at h
        have := (PathBasics.path_adj_iff hRl (by omega) hk).mp h
        omega
      · rintro rfl
        rw [← hR0]
        exact (PathBasics.path_adj_iff hRl (by omega) hk).mpr (Or.inl rfl)
    have hA_v : Gᶜ.Adj v₀ ((R)[k]'hk) ↔ k = R.length - 2 := by
      constructor
      · intro h
        rw [← hRn] at h
        have := (PathBasics.path_adj_iff hRl (by omega) hk).mp h
        omega
      · rintro rfl
        rw [← hRn]
        exact (PathBasics.path_adj_iff hRl (by omega) hk).mpr (Or.inr (by omega))
    have hE1 : (((R)[k]'hk) = ((R)[1]'(by omega : 1 < R.length))) ↔ k = 1 :=
      hRinj k 1 hk (by omega)
    have hE2 : (((R)[k]'hk) = ((R)[R.length - 2]'(by omega : R.length - 2 < R.length))) ↔
        k = R.length - 2 := hRinj k (R.length - 2) hk (by omega)
    rcases hQsplit x hx with hxu | hxv | hxi
    · rw [hxu]
      constructor
      · intro h
        exact Or.inr ⟨rfl, hE1.mpr (hA_u.mp h)⟩
      · rintro (⟨hcc, -⟩ | ⟨-, hcc⟩)
        · exact absurd hcc huvne
        · exact hA_u.mpr (hE1.mp hcc)
    · rw [hxv]
      constructor
      · intro h
        exact Or.inl ⟨rfl, hE2.mpr (hA_v.mp h)⟩
      · rintro (⟨-, hcc⟩ | ⟨hcc, -⟩)
        · exact hA_v.mpr (hE2.mp hcc)
        · exact absurd hcc.symm huvne
    · have hzY : ((R)[k]'hk) ∈ Y := hRint _ (List.mem_reverse.mp hz)
      have hGadj : G.Adj x ((R)[k]'hk) := hintQY x hxi _ hzY
      have hne := (PathBasics.mem_interior_iff_of_pathFrom hQ₀).mp hxi
      refine iff_of_false (fun hcc => hcc.2 hGadj) ?_
      rintro (⟨hcc, -⟩ | ⟨hcc, -⟩)
      · exact hne.2.2 hcc
      · exact hne.2.1 hcc
  have hQ₀len4 : 4 ≤ Q₀.length := by omega
  have hhole2 : IsHoleList Gᶜ (Q₀ ++ (SPGT.interior R).reverse) :=
    PathGlue.glue_hole hQ₀ hRrev hdisj hcross (by omega)
  have heven2 := hG.2 _ hhole2
  have hlenR : (SPGT.interior R).length = R.length - 2 := PathBasics.interior_length R
  have hlenhole : holeLength (Q₀ ++ (SPGT.interior R).reverse) = Q₀.length + (R.length - 2) := by
    simp only [holeLength, List.length_append, List.length_reverse, hlenR]
  rw [hlenhole, Nat.even_iff] at heven2
  have hRodd : pathLength R % 2 = 1 := by
    have : Q₀.length = pathLength Q₀ + 1 := PathBasics.length_eq_pathLength_add_one hQ₀.1
    omega
  -- one of `p₁`, `pₙ` is nonadjacent to both `u₀` and `v₀`
  obtain ⟨iu, hiu, hiu1, hiu2, hiueq⟩ :
      ∃ (i : ℕ) (hi : i < p.length), 1 ≤ i ∧ i + 2 ≤ p.length ∧ (p[i]'hi) = u₀ := by
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hu₀p
    refine ⟨i, hi, ?_, ?_, hieq⟩
    · by_contra hcon
      exact hu₀1 (by rw [← hieq, ← hp0]; exact hp.2.1.getElem_inj_iff.mpr (by omega))
    · by_contra hcon
      exact hu₀n (by rw [← hieq, ← hplast]; exact hp.2.1.getElem_inj_iff.mpr (by omega))
  obtain ⟨iv, hiv, hiv1, hiv2, hiveq⟩ :
      ∃ (i : ℕ) (hi : i < p.length), 1 ≤ i ∧ i + 2 ≤ p.length ∧ (p[i]'hi) = v₀ := by
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hv₀p
    refine ⟨i, hi, ?_, ?_, hieq⟩
    · by_contra hcon
      exact hv₀1 (by rw [← hieq, ← hp0]; exact hp.2.1.getElem_inj_iff.mpr (by omega))
    · by_contra hcon
      exact hv₀n (by rw [← hieq, ← hplast]; exact hp.2.1.getElem_inj_iff.mpr (by omega))
  have hadjidx : iu + 1 = iv ∨ iv + 1 = iu := by
    refine (PathBasics.path_adj_iff hp hiu hiv).mp ?_
    rw [hiueq, hiveq]; exact huvadj
  have hp₁adj : ∀ (k : ℕ) (hk : k < p.length), G.Adj p₁ ((p[k]'hk)) ↔ k = 1 := by
    intro k hk
    rw [← hp0, PathBasics.path_adj_iff hp (show 0 < p.length by omega) hk]
    omega
  have hpnadj : ∀ (k : ℕ) (hk : k < p.length), G.Adj pn ((p[k]'hk)) ↔ k = p.length - 2 := by
    intro k hk
    rw [← hplast, PathBasics.path_adj_iff hp (show p.length - 1 < p.length by omega) hk]
    omega
  have hclose : ∀ (x : V), (x = p₁ ∨ x = pn) → ¬ G.Adj x u₀ → ¬ G.Adj x v₀ → False := by
    intro x hxe hxu hxv
    have hxp : x ∈ p := by
      rcases hxe with h | h
      · rw [h]; exact hp₁mem
      · rw [h]; exact hpnmem
    have hxY : VertexComplete G x Y := (hYuniq x hxp).mpr hxe
    have hxu' : x ≠ u₀ := by
      rcases hxe with h | h
      · rw [h]; exact fun hcc => hu₀1 hcc.symm
      · rw [h]; exact fun hcc => hu₀n hcc.symm
    have hxv' : x ≠ v₀ := by
      rcases hxe with h | h
      · rw [h]; exact fun hcc => hv₀1 hcc.symm
      · rw [h]; exact fun hcc => hv₀n hcc.symm
    have hxR : x ∉ R := by
      intro hmem
      rcases (by
        by_cases h1 : x = u₀
        · exact Or.inl h1
        by_cases h2 : x = v₀
        · exact Or.inr (Or.inl h2)
        exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hmem, h1, h2⟩)) :
          x = u₀ ∨ x = v₀ ∨ x ∈ SPGT.interior R) with h | h | h
      · exact hxu' h
      · exact hxv' h
      · exact hpY x hxp (hRint x h)
    have heven3 := PrismBasics.even_of_antipath_closed_by_vertex' hG hR (by omega) hxR hxu' hxv'
      hxu hxv (fun z hz => hxY z (hRint z hz))
    rw [Nat.even_iff] at heven3
    omega
  rcases (by omega : ¬ (iu = 1 ∨ iv = 1) ∨ ¬ (iu = p.length - 2 ∨ iv = p.length - 2)) with
    hcase | hcase
  · refine hclose p₁ (Or.inl rfl) ?_ ?_
    · rw [← hiueq, hp₁adj iu hiu]; tauto
    · rw [← hiveq, hp₁adj iv hiv]; tauto
  · refine hclose pn (Or.inr rfl) ?_ ?_
    · rw [← hiueq, hpnadj iu hiu]; tauto
    · rw [← hiveq, hpnadj iv hiv]; tauto

end Branch3



section Branch2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The printed *"Assume first that there is an odd hole `C` of length `≥ 7` in `G₀` … a
contradiction"*, together with the length-`5` case (an odd hole of length `5` is also an odd
antihole, so `hanti` disposes of it).  Conclusion: every hole of `G₀` has even length. -/
private theorem branch_hole {G : SimpleGraph V} (hG : Berge G) {X Y : Set V}
    (hXY : Disjoint X Y) (hYa : AnticonnectedSet G Y) (hcompl : Complete G X Y)
    {p : List V} {p₁ pn : V}
    (hp : IsPathList G p) (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (heven : Even (pathLength p)) (hn5 : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ (w = p₁ ∨ w = pn)))
    (hanti : ∀ dd : List (V ⊕ Unit), IsHoleList ((auxG0 G p X p₁ pn)ᶜ) dd →
      Even (holeLength dd))
    (d : List (V ⊕ Unit)) (hd : IsHoleList (auxG0 G p X p₁ pn) d) :
    Even (holeLength d) := by
  classical
  have hpos : 0 < p.length := by omega
  have hp0 : (p[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
  have hplast : (p[p.length - 1]'(by omega)) = pn :=
    PathBasics.getElem_last_of_getLast? hlast (by omega)
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hPF : IsPathFrom G p p₁ pn := ⟨hp, hhead, hlast⟩
  have hne1n : p₁ ≠ pn := PathBasics.isPathFrom_ends_ne hPF (by simp only [pathLength]; omega)
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hcc => hpXY w hw (Or.inl hcc)
  have hpY : ∀ w ∈ p, w ∉ Y := fun w hw hcc => hpXY w hw (Or.inr hcc)
  have hXnY : ∀ x ∈ X, x ∉ Y := fun x hx hcc => (Set.disjoint_left.mp hXY) hx hcc
  have hpeven : pathLength p % 2 = 0 := Nat.even_iff.mp heven
  by_contra hnoteven
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hnoteven
  simp only [holeLength] at hnoteven
  have h4 : 4 ≤ d.length := hd.1
  -- length `5` is also an odd antihole
  have h7 : 7 ≤ d.length := by
    rcases (by omega : d.length = 5 ∨ 7 ≤ d.length) with h5 | h7
    · exfalso
      have := hanti _ (PathGlue.isHoleList_compl_of_length_five hd h5)
      rw [Nat.even_iff] at this
      simp only [holeLength, List.length_cons, List.length_nil] at this
      omega
    · exact h7
  -- `C` must use `y`
  by_cases hy : (Sum.inr () : V ⊕ Unit) ∈ d
  case neg =>
    obtain ⟨d₀, hd₀eq, hd₀len⟩ := exists_eq_map_inl (fun x hx heq => hy (heq ▸ hx))
    have h1 : IsHoleList (auxG G p X) d₀ :=
      (isHoleList_map_inl (auxG G p X) (auxS X p₁ pn) d₀).mpr (by rw [← hd₀eq]; exact hd)
    have h3 := hG.1 d₀ (RestrictGraph.isHoleList_of_restrict h1)
    rw [Nat.even_iff] at h3
    simp only [holeLength] at h3
    omega
  obtain ⟨c, hc, hclen, hc0, hcmem⟩ :
      ∃ c : List (V ⊕ Unit), IsHoleList (auxG0 G p X p₁ pn) c ∧ c.length = d.length ∧
        (∀ (h : 0 < c.length), ((c)[0]'h) = Sum.inr ()) ∧ (∀ z, z ∈ c ↔ z ∈ d) := by
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
    refine ⟨d.rotate j, HoleBasics.isHoleList_rotate hd j, List.length_rotate .., ?_,
      fun z => List.mem_rotate⟩
    intro h
    have hjlt : (0 + j) % d.length < d.length := Nat.mod_lt _ (by omega)
    have hget : ((d.rotate j)[0]'h) = ((d)[(0 + j) % d.length]'hjlt) := by
      simp only [List.getElem_rotate, List.length_rotate]
    rw [hget]
    exact (getElem_congr_idx d hjlt hj (by rw [Nat.zero_add, Nat.mod_eq_of_lt hj])).trans hjy
  have hc5 : 5 ≤ c.length := by omega
  have hc7 : 7 ≤ c.length := by omega
  have hcy : ((c)[0]'(by omega)) = Sum.inr () := hc0 (by omega)
  have hcnd : c.Nodup := hc.2.1
  -- every vertex of `c` other than `y` is an old vertex of `V(P) ∪ X`
  have hcvert : ∀ z ∈ c, z = Sum.inr () ∨ ∃ w : V, (w ∈ p ∨ w ∈ X) ∧ z = Sum.inl w := by
    intro z hz
    cases z with
    | inr t => exact Or.inl (by cases t; rfl)
    | inl w =>
      refine Or.inr ⟨w, ?_, rfl⟩
      by_contra hw
      obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hz
      have hsucc : (i + 1) % c.length < c.length := Nat.mod_lt _ (by omega)
      have hadj : (auxG0 G p X p₁ pn).Adj ((c)[i]'hi) ((c)[(i + 1) % c.length]'hsucc) :=
        (hc.2.2 i ((i + 1) % c.length) hi hsucc).mpr (Or.inl rfl)
      rw [hieq] at hadj
      cases hz2 : ((c)[(i + 1) % c.length]'hsucc) with
      | inl u' =>
        rw [hz2] at hadj
        exact hw ((auxG0_adj_inl w u').mp hadj).2.1
      | inr t =>
        rw [hz2] at hadj
        cases t
        rw [auxG0_adj_inr] at hadj
        rcases hadj with hcc | hcc | hcc
        · exact hw (Or.inr hcc)
        · exact hw (Or.inl (hcc ▸ hp₁mem))
        · exact hw (Or.inl (hcc ▸ hpnmem))
  -- the two `G₀`-neighbours of `y` lie in `X ∪ {p₁, pₙ}`
  have hnbr : ∀ (i : ℕ) (hi : i < c.length), (i = 1 ∨ i = c.length - 1) →
      ∃ w : V, (w ∈ X ∨ w = p₁ ∨ w = pn) ∧ ((c)[i]'hi) = Sum.inl w := by
    intro i hi hor
    have hadj : (auxG0 G p X p₁ pn).Adj ((c)[0]'(by omega)) ((c)[i]'hi) :=
      (HoleMinusVertexPath.adj_head_iff hc hc5 hi).mpr hor
    have hne : ((c)[i]'hi) ≠ Sum.inr () := by
      rw [← hcy]
      intro h
      have hi0 : i = 0 := hcnd.getElem_inj_iff.mp h
      omega
    rcases hcvert _ (List.getElem_mem hi) with h | ⟨w, hw, hweq⟩
    · exact absurd h hne
    refine ⟨w, ?_, hweq⟩
    rw [hcy, hweq, auxG0_adj_inr'] at hadj
    exact hadj
  -- `Q = C \ y`, pushed back to `V`
  have hQ : IsPathFrom (auxG0 G p X p₁ pn) c.tail ((c)[1]'(by omega))
      ((c)[c.length - 1]'(by omega)) := HoleMinusVertexPath.isPathFrom_tail hc hc5
  have hQlen : c.tail.length = c.length - 1 := by simp
  have hQnoy : ∀ z ∈ c.tail, z ≠ Sum.inr () := by
    intro z hz
    rw [HoleMinusVertexPath.mem_tail_iff hc hc5] at hz
    rw [← hcy]
    exact hz.2
  obtain ⟨Q₀, hQ₀eq, hQ₀len⟩ := exists_eq_map_inl hQnoy
  have hQ₀W : ∀ w ∈ Q₀, w ∈ auxW p X := by
    intro w hw
    have hmt : (Sum.inl w : V ⊕ Unit) ∈ c.tail := by
      rw [hQ₀eq]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rcases hcvert _ (List.mem_of_mem_tail hmt) with h | ⟨w', hw', hw'eq⟩
    · exact absurd h (by simp)
    · rw [Sum.inl_injective hw'eq]
      exact hw'
  have hQ₀l : IsPathList G Q₀ := by
    refine (RestrictGraph.isPathList_iff_of_subset hQ₀W).mp ?_
    refine (isPathList_map_inl (auxG G p X) (auxS X p₁ pn) Q₀).mpr ?_
    rw [← hQ₀eq]
    exact hQ.1
  have hQ₀plen : pathLength Q₀ = c.length - 2 := by
    simp only [pathLength, hQ₀len, hQlen]; omega
  have hQ₀odd : pathLength Q₀ % 2 = 1 := by omega
  have hQ₀5 : 5 ≤ pathLength Q₀ := by omega
  -- interior of `Q` consists of the vertices of `P*`
  have hQ₀int : ∀ w ∈ SPGT.interior Q₀, (w ∈ p ∧ w ≠ p₁ ∧ w ≠ pn) := by
    intro w hw
    have hmi : (Sum.inl w : V ⊕ Unit) ∈ SPGT.interior c.tail := by
      rw [hQ₀eq, interior_map]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [HoleMinusVertexPath.mem_interior_tail_iff hc hc5] at hmi
    obtain ⟨hmem, hn0, hn1, hnl⟩ := hmi
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hmem
    have hi0 : i ≠ 0 := fun h => hn0 (by subst h; exact hieq.symm)
    have hi1 : i ≠ 1 := fun h => hn1 (by subst h; exact hieq.symm)
    have hil : i ≠ c.length - 1 := fun h => hnl (by subst h; exact hieq.symm)
    have hnotadj : ¬ (auxG0 G p X p₁ pn).Adj (Sum.inr ()) (Sum.inl w) := by
      rw [← hcy, ← hieq]
      intro hadj
      have := (HoleMinusVertexPath.adj_head_iff hc hc5 hi).mp hadj
      omega
    rw [auxG0_adj_inr'] at hnotadj
    push Not at hnotadj
    rcases hQ₀W w (PathBasics.interior_subset hw) with hwp | hwX
    · exact ⟨hwp, hnotadj.2.1, hnotadj.2.2⟩
    · exact absurd hwX hnotadj.1
  have hmap_head : ∀ (L : List V) (z : V),
      (L.map (Sum.inl : V → V ⊕ Unit)).head? = some (Sum.inl z) → L.head? = some z := by
    intro L z h
    rw [List.head?_map] at h
    cases hL : L.head? with
    | none => rw [hL] at h; simp at h
    | some a => rw [hL] at h; simp only [Option.map_some, Option.some.injEq] at h
                exact congrArg some (Sum.inl_injective h)
  have hmap_last : ∀ (L : List V) (z : V),
      (L.map (Sum.inl : V → V ⊕ Unit)).getLast? = some (Sum.inl z) → L.getLast? = some z := by
    intro L z h
    rw [List.getLast?_map] at h
    cases hL : L.getLast? with
    | none => rw [hL] at h; simp at h
    | some a => rw [hL] at h; simp only [Option.map_some, Option.some.injEq] at h
                exact congrArg some (Sum.inl_injective h)
  obtain ⟨qa, hqa, hqaeq⟩ := hnbr 1 (by omega) (Or.inl rfl)
  obtain ⟨qb, hqb, hqbeq⟩ := hnbr (c.length - 1) (by omega) (Or.inr rfl)
  have hQ₀from : IsPathFrom G Q₀ qa qb :=
    ⟨hQ₀l, hmap_head Q₀ qa (by rw [← hQ₀eq, ← hqaeq]; exact hQ.2.1),
      hmap_last Q₀ qb (by rw [← hQ₀eq, ← hqbeq]; exact hQ.2.2)⟩
  have hQ₀Y : ∀ w ∈ Q₀, w ∉ Y := by
    intro w hw
    rcases hQ₀W w hw with h | h
    · exact hpY w h
    · exact hXnY w h
  have hYcompl : ∀ (z : V), (z ∈ X ∨ z = p₁ ∨ z = pn) → VertexComplete G z Y := by
    rintro z (h | h | h)
    · exact hcompl z h
    · rw [h]; exact (hYuniq p₁ hp₁mem).mpr (Or.inl rfl)
    · rw [h]; exact (hYuniq pn hpnmem).mpr (Or.inr rfl)
  have hnoedgeQ : ¬ ∃ u ∈ Q₀, ∃ v ∈ Q₀, EdgeComplete G Y u v := by
    rintro ⟨u, hu, v, hv, hadj, huc, hvc⟩
    have hends : ∀ w ∈ Q₀, VertexComplete G w Y → w = qa ∨ w = qb := by
      intro w hw hwc
      by_contra hcon
      push Not at hcon
      obtain ⟨hwp, hw1, hwn⟩ :=
        hQ₀int w ((PathBasics.mem_interior_iff_of_pathFrom hQ₀from).mpr ⟨hw, hcon.1, hcon.2⟩)
      rcases (hYuniq w hwp).mp hwc with h | h
      · exact hw1 h
      · exact hwn h
    have hqab : G.Adj qa qb := by
      rcases hends u hu huc with hu' | hu' <;> rcases hends v hv hvc with hv' | hv'
      · exact absurd (hu'.trans hv'.symm) (G.ne_of_adj hadj)
      · rw [← hu', ← hv']; exact hadj
      · rw [← hv', ← hu']; exact hadj.symm
      · exact absurd (hu'.trans hv'.symm) (G.ne_of_adj hadj)
    have h0 : (Q₀[0]'(by omega)) = qa :=
      PathBasics.getElem_zero_of_head? hQ₀from.2.1 (by omega)
    have hl : (Q₀[Q₀.length - 1]'(by omega)) = qb :=
      PathBasics.getElem_last_of_getLast? hQ₀from.2.2 (by omega)
    refine PathBasics.path_ends_not_adj hQ₀l (by omega) ?_
    rw [h0, hl]
    exact hqab
  rcases thm_2_1 G hG Y hYa Q₀ qa qb hQ₀from hQ₀Y (Nat.odd_iff.mpr hQ₀odd)
      (hYcompl qa hqa) (hYcompl qb hqb) with hcc1 | ⟨-, ya, hyaY, yb, hybY, hleap⟩ | ⟨hcc3, -⟩
  · exact hnoedgeQ hcc1
  · obtain ⟨-, -, hyab, hnyab, hAd, hBd⟩ := hleap
    have hIQ : IsPathFrom G (SPGT.interior Q₀) ((Q₀)[1]'(by omega))
        ((Q₀)[Q₀.length - 2]'(by omega)) := PathGlue.isPathFrom_interior hQ₀l (by omega)
    have hsu : G.Adj ya ((Q₀)[1]'(by omega)) := (hAd 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    have htv : G.Adj yb ((Q₀)[Q₀.length - 2]'(by omega)) :=
      (hBd (Q₀.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
    have hyaQ : ya ∉ SPGT.interior Q₀ := fun h => hQ₀Y ya (PathBasics.interior_subset h) hyaY
    have hybQ : yb ∉ SPGT.interior Q₀ := fun h => hQ₀Y yb (PathBasics.interior_subset h) hybY
    have hsother : ∀ x ∈ SPGT.interior Q₀, x ≠ ((Q₀)[1]'(by omega)) → ¬ G.Adj ya x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hQ₀l hx
      have hcv := (hAd k hk).mp hadj
      have hkne : k ≠ 1 := by intro h; exact hxne (by subst h; rfl)
      omega
    have htother : ∀ x ∈ SPGT.interior Q₀, x ≠ ((Q₀)[Q₀.length - 2]'(by omega)) →
        ¬ G.Adj yb x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hQ₀l hx
      have hcv := (hBd k hk).mp hadj
      have hkne : k ≠ Q₀.length - 2 := by intro h; exact hxne (by subst h; rfl)
      omega
    have hR : IsPathFrom G (ya :: (SPGT.interior Q₀ ++ [yb])) ya yb :=
      PathAttach.isPathFrom_cons_concat hIQ hsu htv hnyab hyab hyaQ hybQ hsother htother
    have hRint : SPGT.interior (ya :: (SPGT.interior Q₀ ++ [yb])) = SPGT.interior Q₀ := by
      simp [SPGT.interior]
    have hIQlen : (SPGT.interior Q₀).length = pathLength Q₀ - 1 := by
      have := PathBasics.length_eq_pathLength_add_one hQ₀l
      simp only [PathBasics.interior_length]
      omega
    -- the closing move: `R` completed through `p₁` or `pₙ` would be an odd hole
    have hfinish : ∀ (x : V), x ∈ p → VertexComplete G x Y → x ∉ SPGT.interior Q₀ →
        (∀ z ∈ SPGT.interior Q₀, ¬ G.Adj x z) → False := by
      intro x hxp hxY hxnint hxint
      have hxR : x ∉ (ya :: (SPGT.interior Q₀ ++ [yb])) := by
        rw [PathAttach.mem_cons_append_singleton]
        rintro (h | h | h)
        · exact hpY x hxp (h ▸ hyaY)
        · exact hxnint h
        · exact hpY x hxp (h ▸ hybY)
      have h4R : 4 ≤ (ya :: (SPGT.interior Q₀ ++ [yb])).length := by
        rw [PathAttach.length_cons_append_singleton]
        omega
      have hev := PrismBasics.even_of_path_closed_by_vertex hG hR h4R hxR (hxY ya hyaY)
        (hxY yb hybY) (by rw [hRint]; exact hxint)
      rw [PathAttach.length_cons_append_singleton, Nat.even_iff] at hev
      omega
    have hp₁adj : ∀ (k : ℕ) (hk : k < p.length), G.Adj p₁ ((p[k]'hk)) ↔ k = 1 := by
      intro k hk
      rw [← hp0, PathBasics.path_adj_iff hp (show 0 < p.length by omega) hk]
      omega
    have hpnadj : ∀ (k : ℕ) (hk : k < p.length), G.Adj pn ((p[k]'hk)) ↔ k = p.length - 2 := by
      intro k hk
      rw [← hplast, PathBasics.path_adj_iff hp (show p.length - 1 < p.length by omega) hk]
      omega
    have hp₁nint : p₁ ∉ SPGT.interior Q₀ := fun h => (hQ₀int p₁ h).2.1 rfl
    have hpnnint : pn ∉ SPGT.interior Q₀ := fun h => (hQ₀int pn h).2.2 rfl
    rcases Classical.em ((p[1]'(by omega)) ∈ SPGT.interior Q₀) with hb1 | hb1
    · rcases Classical.em ((p[p.length - 2]'(by omega)) ∈ SPGT.interior Q₀) with hb2 | hb2
      · -- both `p₂` and `p_{n-1}` lie on `R*`: then `R*` is all of `P*`, so `R` is even
        obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
          PathGlue.exists_pos_of_subpath hp hIQ.1 (fun z hz => (hQ₀int z hz).1)
        have hfrange : ∀ t, t < (SPGT.interior Q₀).length → 1 ≤ f t ∧ f t ≤ p.length - 2 := by
          intro t ht
          obtain ⟨hzp, hz1, hzn⟩ := hQ₀int _ (List.getElem_mem ht)
          have heq := hf2 t ht (hf1 t ht)
          have hlt := hf1 t ht
          constructor
          · by_contra hcon
            refine hz1 ?_
            rw [← heq, ← hp0]
            exact hp.2.1.getElem_inj_iff.mpr (by omega)
          · by_contra hcon
            refine hzn ?_
            rw [← heq, ← hplast]
            exact hp.2.1.getElem_inj_iff.mpr (by omega)
        obtain ⟨s, hs, hseq⟩ := List.getElem_of_mem hb1
        obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hb2
        have hfs : f s = 1 := hp.2.1.getElem_inj_iff.mp ((hf2 s hs (hf1 s hs)).trans hseq)
        have hft : f t = p.length - 2 := hp.2.1.getElem_inj_iff.mp ((hf2 t ht (hf1 t ht)).trans hteq)
        have hlow : p.length - 2 ≤ (SPGT.interior Q₀).length := by
          rcases le_total s t with hst | hst
          · obtain ⟨ha, hb⟩ := hf4 s t hst ht
            omega
          · obtain ⟨ha, hb⟩ := hf4 t s hst hs
            omega
        have hhigh : (SPGT.interior Q₀).length ≤ p.length - 2 := by
          have hmaps : ∀ a ∈ Finset.range (SPGT.interior Q₀).length,
              f a ∈ Finset.Icc 1 (p.length - 2) := by
            intro a ha
            rw [Finset.mem_range] at ha
            rw [Finset.mem_Icc]
            exact hfrange a ha
          have hinj : Set.InjOn f (Finset.range (SPGT.interior Q₀).length) := by
            intro a ha b hb hab
            simp only [Finset.coe_range, Set.mem_Iio] at ha hb
            exact hf3 a b ha hb hab
          have hcard := Finset.card_le_card_of_injOn f hmaps hinj
          simpa [Nat.card_Icc] using hcard
        have hplen : pathLength p = p.length - 1 := PathBasics.pathLength_eq p
        omega
      · refine hfinish pn hpnmem ((hYuniq pn hpnmem).mpr (Or.inr rfl)) hpnnint ?_
        intro z hz hadj
        obtain ⟨hzp, hz1, hzn⟩ := hQ₀int z hz
        obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hzp
        have hzk : (p[k]'hk) ∈ SPGT.interior Q₀ := by rw [hkeq]; exact hz
        have hadjk : G.Adj pn (p[k]'hk) := by rw [hkeq]; exact hadj
        have hkeq2 : k = p.length - 2 := (hpnadj k hk).mp hadjk
        refine hb2 ?_
        have heq3 : (p[p.length - 2]'(by omega)) = (p[k]'hk) :=
          hp.2.1.getElem_inj_iff.mpr (by omega)
        rw [heq3]
        exact hzk
    · refine hfinish p₁ hp₁mem ((hYuniq p₁ hp₁mem).mpr (Or.inl rfl)) hp₁nint ?_
      intro z hz hadj
      obtain ⟨hzp, hz1, hzn⟩ := hQ₀int z hz
      obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hzp
      have hzk : (p[k]'hk) ∈ SPGT.interior Q₀ := by rw [hkeq]; exact hz
      have hadjk : G.Adj p₁ (p[k]'hk) := by rw [hkeq]; exact hadj
      have hkeq2 : k = 1 := (hp₁adj k hk).mp hadjk
      refine hb1 ?_
      have heq3 : (p[1]'(by omega)) = (p[k]'hk) := hp.2.1.getElem_inj_iff.mpr (by omega)
      rw [heq3]
      exact hzk
  · omega

end Branch2



section Main

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.11** (printed p. 12)

PAPER: *"Let `G` be Berge, and let `X,Y` be disjoint nonempty anticonnected
subsets of `V(G)`, complete to each other.  Let `P` be a path in `G \ (X ∪ Y)`
with even length `≥ 4`, with vertices `p₁,…,pₙ` in order, such that `p₁` is the
unique `X`-complete vertex of `P`, and `p₁,pₙ` are the only `Y`-complete vertices
of `P`.  Then either:*

*1. there exists `x ∈ X` non-adjacent to all of `p₂,…,pₙ`, or*

*2. there are nonadjacent `x₁,x₂ ∈ X` such that `x₁`-`p₂`-`⋯`-`pₙ`-`x₂` is a
path."*

`{p₂,…,pₙ}` is `p.tail`. -/
theorem thm_2_11 (G : SimpleGraph V) (hG : Berge G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pn : V) (hp : IsPathList G p) (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (heven : Even (pathLength p)) (hlen : 4 ≤ pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ (w = p₁ ∨ w = pn))) :
    (∃ x ∈ X, ∀ w ∈ p.tail, ¬ G.Adj x w) ∨
    (∃ x₁ ∈ X, ∃ x₂ ∈ X, ¬ G.Adj x₁ x₂ ∧ IsPathList G (x₁ :: (p.tail ++ [x₂]))) := by
  have hn5 : 5 ≤ p.length := by
    have := PathBasics.length_eq_pathLength_add_one hp
    omega
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hcc => hpXY w hw (Or.inl hcc)
  -- "so we may assume `G₀` is not Berge … a contradiction": in fact `G₀` *is* Berge.
  have hanti : ∀ dd : List (V ⊕ Unit), IsHoleList ((auxG0 G p X p₁ pn)ᶜ) dd →
      Even (holeLength dd) :=
    fun dd hdd => branch_antihole hG hXY hYa hcompl hp hpXY hn5 hhead hlast hYuniq dd hdd
  have hB : Berge (auxG0 G p X p₁ pn) :=
    ⟨fun cc hcc =>
      branch_hole hG hXY hYa hcompl hp hpXY heven hn5 hhead hlast hYuniq hanti cc hcc, hanti⟩
  -- "If `G₀` is Berge then the result follows from 2.10"
  exact branch_berge hG hXa hp hpX hn5 hhead hlast hXuniq hB

end Main

end SPGT

end Workspace.Statements.S02
