import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.RestrictGraph
import Workspace.ProofLemmas.PendantTransport
import Workspace.ProofLemmas.AddPendantVertexTransport
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S02.Thm_2_2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm29Aux

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.AddPendantVertexTransport
open Workspace.Statements.S02.SPGT


section Aux

variable {V : Type*}

/-- The kept vertex set `V(P) ∪ X` (the paper's `V(G) = V(P) ∪ X ∪ Y` followed by `G \ Y`). -/
def cW (p : List V) (X : Set V) : Set V := {w | w ∈ p} ∪ X

/-- The neighbour set of the new vertex `y`.  **In 2.9 this is `X ∪ {pₙ}`** — unlike 2.11, where
it is `X ∪ {p₁, pₙ}`, because 2.9 assumes `pₙ` is the *unique* `Y`-complete vertex of `P`.  See
`FIXES.md` §F6. -/
def cS (X : Set V) (pn : V) : Set V := X ∪ {pn}

def cG (G : SimpleGraph V) (p : List V) (X : Set V) : SimpleGraph V :=
  RestrictGraph.restrictTo G (cW p X)

/-- `G₀ = (G \ Y) + y`, with `N(y) = X ∪ {pₙ}`. -/
def cG0 (G : SimpleGraph V) (p : List V) (X : Set V) (pn : V) : SimpleGraph (V ⊕ Unit) :=
  addPendantVertex (cG G p X) (cS X pn)

theorem mem_cW {p : List V} {X : Set V} {a : V} : a ∈ cW p X ↔ (a ∈ p ∨ a ∈ X) := Iff.rfl

theorem mem_cS {X : Set V} {pn a : V} : a ∈ cS X pn ↔ (a ∈ X ∨ a = pn) := by
  simp only [cS, Set.mem_union, Set.mem_singleton_iff]

theorem cG0_adj_inl {G : SimpleGraph V} {p : List V} {X : Set V} {pn : V} (a b : V) :
    (cG0 G p X pn).Adj (Sum.inl a) (Sum.inl b) ↔
      (G.Adj a b ∧ (a ∈ p ∨ a ∈ X) ∧ (b ∈ p ∨ b ∈ X)) := by
  rw [cG0, adj_inl_inl]
  exact Iff.rfl

theorem cG0_adj_inr {G : SimpleGraph V} {p : List V} {X : Set V} {pn : V} (a : V)
    (t : Unit) : (cG0 G p X pn).Adj (Sum.inl a) (Sum.inr t) ↔ (a ∈ X ∨ a = pn) := by
  rw [cG0, adj_inl_inr]
  exact mem_cS

theorem cG0_adj_inr' {G : SimpleGraph V} {p : List V} {X : Set V} {pn : V} (a : V)
    (t : Unit) : (cG0 G p X pn).Adj (Sum.inr t) (Sum.inl a) ↔ (a ∈ X ∨ a = pn) := by
  rw [cG0, adj_inr_inl]
  exact mem_cS

end Aux

section Closing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"In each case, either `(V(P \ p₁), X)` or `(V(P \ pₙ), Y)` is not balanced."*  This is a
uniform consequence of the three-way disjunction, so it is proved once. -/
theorem second_of_first {G : SimpleGraph V} {X Y : Set V} {p : List V} {p₁ pn : V}
    (hp : IsPathList G p) (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (heven : Even (pathLength p)) (hpos : 0 < pathLength p)
    (hfirst :
      ((4 ≤ pathLength p ∧ ∃ x₁ ∈ X, ∃ x₂ ∈ X, ¬ G.Adj x₁ x₂ ∧
          IsPathList G (x₁ :: (p.tail ++ [x₂]))) ∨
        (4 ≤ pathLength p ∧ ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, ¬ G.Adj y₁ y₂ ∧
          IsPathList G (y₁ :: (p.dropLast ++ [y₂]))) ∨
        (pathLength p = 2 ∧ ∃ c : V, p = [p₁, c, pn] ∧
          ∃ Q R : List V,
            (IsAntipathFrom G Q c pn ∧ ∀ w ∈ SPGT.interior Q, w ∈ X) ∧
            (IsAntipathFrom G R p₁ c ∧ ∀ w ∈ SPGT.interior R, w ∈ Y) ∧
            Xor' (Odd (pathLength Q)) (Odd (pathLength R))))) :
    (¬ SPGT.Balanced G ({w : V | w ∈ p} \ {p₁}) X ∨
      ¬ SPGT.Balanced G ({w : V | w ∈ p} \ {pn}) Y) := by
  have hplen : p.length = pathLength p + 1 := PathBasics.length_eq_pathLength_add_one hp
  have hnd : p.Nodup := hp.2.1
  have hne : p ≠ [] := PathBasics.path_ne_nil hp
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hPF : IsPathFrom G p p₁ pn := ⟨hp, hhead, hlast⟩
  have hne1n : p₁ ≠ pn := PathBasics.isPathFrom_ends_ne hPF (by omega)
  have hpcons : p = p₁ :: p.tail := by
    cases hpe : p with
    | nil => rw [hpe] at hhead; simp at hhead
    | cons z t =>
      rw [hpe] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead]
  have hp₁tail : p₁ ∉ p.tail := by
    have h := hnd
    rw [hpcons] at h
    exact (List.nodup_cons.mp h).1
  rcases hfirst with ⟨h4, x₁, hx₁, x₂, hx₂, hnadj, hpath⟩ |
    ⟨h4, y₁, hy₁, y₂, hy₂, hnadj, hpath⟩ | ⟨h2, c₀, hpdef, Q, R, ⟨hQ, hQint⟩, ⟨hR, hRint⟩, hxor⟩
  · refine Or.inl (fun hbal => ?_)
    have hgl : (x₁ :: (p.tail ++ [x₂])).getLast? = some x₂ := by
      rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp)]
      rfl
    refine hbal.1 x₁ x₂ (x₁ :: (p.tail ++ [x₂])) hx₁ hx₂ hnadj
      ⟨hpath, rfl, hgl⟩ ?_ ?_
    · intro w hw
      have hwt : w ∈ p.tail := by
        have : SPGT.interior (x₁ :: (p.tail ++ [x₂])) = p.tail := by simp [SPGT.interior]
        rwa [this] at hw
      exact ⟨List.tail_subset p hwt, fun hc => hp₁tail (hc ▸ hwt)⟩
    · rw [PathAttach.pathLength_cons_append_singleton, Nat.odd_iff]
      have : p.tail.length = p.length - 1 := by simp
      rw [Nat.even_iff] at heven
      omega
  · refine Or.inr (fun hbal => ?_)
    have hgl : (y₁ :: (p.dropLast ++ [y₂])).getLast? = some y₂ := by
      rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp)]
      rfl
    refine hbal.1 y₁ y₂ (y₁ :: (p.dropLast ++ [y₂])) hy₁ hy₂ hnadj
      ⟨hpath, rfl, hgl⟩ ?_ ?_
    · intro w hw
      have hwt : w ∈ p.dropLast := by
        have : SPGT.interior (y₁ :: (p.dropLast ++ [y₂])) = p.dropLast := by simp [SPGT.interior]
        rwa [this] at hw
      rw [PathBasics.mem_dropLast_iff hnd hne] at hwt
      have hgl : p.getLast hne = pn := by
        have h1 : p.getLast? = some (p.getLast hne) := List.getLast?_eq_some_getLast hne
        rw [hlast] at h1
        exact (Option.some_injective _ h1).symm
      exact ⟨hwt.1, fun hc => hwt.2 (hc.trans hgl.symm)⟩
    · rw [PathAttach.pathLength_cons_append_singleton, Nat.odd_iff]
      have : p.dropLast.length = p.length - 1 := by simp
      rw [Nat.even_iff] at heven
      omega
  · -- `P` has length 2: exactly one of `Q`, `R` is odd
    have hc₀p : c₀ ∈ p := by rw [hpdef]; simp
    have hpnp : pn ∈ p := by rw [hpdef]; simp
    have hp₁p : p₁ ∈ p := by rw [hpdef]; simp
    have hnd' : [p₁, c₀, pn].Nodup := by rw [← hpdef]; exact hnd
    have hc₀1 : c₀ ≠ p₁ := by rintro rfl; simp at hnd'
    have hc₀n : c₀ ≠ pn := by rintro rfl; simp at hnd'
    have hpl' : IsPathList G [p₁, c₀, pn] := by rw [← hpdef]; exact hp
    have hadjcn : G.Adj c₀ pn := by
      have h := PathBasics.path_adj_succ hpl' (i := 1) (by simp)
      simpa using h
    have hadj1c : G.Adj p₁ c₀ := by
      have h := PathBasics.path_adj_succ hpl' (i := 0) (by simp)
      simpa using h
    rcases hxor with ⟨hQodd, -⟩ | ⟨hRodd, -⟩
    · exact Or.inl (fun hbal =>
        hbal.2 c₀ pn Q ⟨hc₀p, hc₀1⟩ ⟨hpnp, fun hc => hne1n hc.symm⟩ hadjcn hQ hQint hQodd)
    · exact Or.inr (fun hbal =>
        hbal.2 p₁ c₀ R ⟨hp₁p, hne1n⟩ ⟨hc₀p, hc₀n⟩ hadj1c hR hRint hRodd)

end Closing


section Len2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"If `P` has length 2, choose an antipath `Q` between `p₂` and `p₃` with interior in `X`, and
an antipath `R` between `p₁` and `p₂` with interior in `Y`.  Then `p₂-Q-p₃-p₁-R-p₂` is an
antihole, and so exactly one of `Q`,`R` has odd length and the theorem holds."* -/
theorem branch_len2 {G : SimpleGraph V} (hG : Berge G) {X Y : Set V}
    (hXY : Disjoint X Y) (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    {p : List V} {p₁ pn : V} (hp : IsPathList G p) (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pn))
    (h2 : pathLength p = 2) :
    ∃ c : V, p = [p₁, c, pn] ∧ ∃ Q R : List V,
      (IsAntipathFrom G Q c pn ∧ ∀ w ∈ SPGT.interior Q, w ∈ X) ∧
      (IsAntipathFrom G R p₁ c ∧ ∀ w ∈ SPGT.interior R, w ∈ Y) ∧
      Xor' (Odd (pathLength Q)) (Odd (pathLength R)) := by
  classical
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hc => hpXY w hw (Or.inl hc)
  have hpY : ∀ w ∈ p, w ∉ Y := fun w hw hc => hpXY w hw (Or.inr hc)
  have hXnY : ∀ x ∈ X, x ∉ Y := fun x hx hc => (Set.disjoint_left.mp hXY) hx hc
  have hlen3 : p.length = 3 := by
    have := PathBasics.length_eq_pathLength_add_one hp
    omega
  obtain ⟨a, b, c, hpdef0⟩ := PrismBasics.length_eq_three hlen3
  have hae : a = p₁ := by rw [hpdef0] at hhead; simpa using hhead
  have hce : c = pn := by rw [hpdef0] at hlast; simpa using hlast
  have hpdef : p = [p₁, b, pn] := by rw [hpdef0, hae, hce]
  refine ⟨b, hpdef, ?_⟩
  have hbp : b ∈ p := by rw [hpdef]; simp
  have hpnp : pn ∈ p := by rw [hpdef]; simp
  have hp₁p : p₁ ∈ p := by rw [hpdef]; simp
  have hnd' : [p₁, b, pn].Nodup := by rw [← hpdef]; exact hp.2.1
  have hb1 : b ≠ p₁ := by rintro rfl; simp at hnd'
  have hbn : b ≠ pn := by rintro rfl; simp at hnd'
  have h1n : p₁ ≠ pn := by rintro rfl; simp at hnd'
  have hpl' : IsPathList G [p₁, b, pn] := by rw [← hpdef]; exact hp
  have hadj1b : G.Adj p₁ b := by
    have h := PathBasics.path_adj_succ hpl' (i := 0) (by simp)
    simpa using h
  have hadjbn : G.Adj b pn := by
    have h := PathBasics.path_adj_succ hpl' (i := 1) (by simp)
    simpa using h
  have hn1n : ¬ G.Adj p₁ pn := by
    have h := PathBasics.path_not_adj_of_gap hpl' (i := 0) (j := 2) (by simp) (by simp)
      (by omega) (by omega)
    simpa using h
  -- the two antipaths
  have hnc : ∀ (w : V), w ∈ p → w ≠ p₁ → ∃ x ∈ X, ¬ G.Adj w x := by
    intro w hw hwne
    by_contra hcon
    push Not at hcon
    exact hwne ((hXuniq w hw).mp hcon)
  have hncY : ∀ (w : V), w ∈ p → w ≠ pn → ∃ y ∈ Y, ¬ G.Adj w y := by
    intro w hw hwne
    by_contra hcon
    push Not at hcon
    exact hwne ((hYuniq w hw).mp hcon)
  obtain ⟨Q, hQ, hQint⟩ := InducedPathExtraction.exists_antipath_interior_in hXa
    (hpX b hbp) (hpX pn hpnp) (hnc b hbp hb1) (hnc pn hpnp (fun hc => h1n hc.symm))
  obtain ⟨R, hR, hRint⟩ := InducedPathExtraction.exists_antipath_interior_in hYa
    (hpY p₁ hp₁p) (hpY b hbp) (hncY p₁ hp₁p h1n) (hncY b hbp hbn)
  refine ⟨Q, R, ⟨hQ, hQint⟩, ⟨hR, hRint⟩, ?_⟩
  -- lengths
  have hQl : IsPathList Gᶜ Q := hQ.1
  have hRl : IsPathList Gᶜ R := hR.1
  have hQlen : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hQl
  have hRlen : R.length = pathLength R + 1 := PathBasics.length_eq_pathLength_add_one hRl
  have hQ2 : 2 ≤ Q.length := by
    by_contra hcon
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp (by omega : Q.length = 1)
    rw [hz] at hQ
    have e1 : z = b := by simpa using hQ.2.1
    have e2 : z = pn := by simpa using hQ.2.2
    exact hbn (e1.symm.trans e2)
  have hQ3 : 3 ≤ Q.length := by
    by_contra hcon
    have h1 : pathLength Q = 1 := by omega
    exact (PathBasics.isPathFrom_ends_adj_of_length_one hQ h1).2 hadjbn
  have hR2 : 2 ≤ R.length := by
    by_contra hcon
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp (by omega : R.length = 1)
    rw [hz] at hR
    have e1 : z = p₁ := by simpa using hR.2.1
    have e2 : z = b := by simpa using hR.2.2
    exact hb1 (e2.symm.trans e1)
  have hR3 : 3 ≤ R.length := by
    by_contra hcon
    have h1 : pathLength R = 1 := by omega
    exact (PathBasics.isPathFrom_ends_adj_of_length_one hR h1).2 hadj1b
  have hR0 : ((R)[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
  have hRn : ((R)[R.length - 1]'(by omega)) = b :=
    PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
  have hRnd : R.Nodup := hRl.2.1
  have hRinj : ∀ (i j : ℕ) (hi : i < R.length) (hj : j < R.length),
      (((R)[i]'hi) = ((R)[j]'hj)) ↔ i = j := fun i j hi hj => hRnd.getElem_inj_iff
  -- `R' = p₁-R-…`, the second arc of the antihole
  have hIR : IsPathFrom Gᶜ (SPGT.interior R) ((R)[1]'(by omega))
      ((R)[R.length - 2]'(by omega)) := PathGlue.isPathFrom_interior hRl (by omega)
  have hp₁R : p₁ ∉ SPGT.interior R := fun h => hpY p₁ hp₁p (hRint p₁ h)
  have hadjR1 : Gᶜ.Adj p₁ ((R)[1]'(by omega)) := by
    rw [← hR0]
    exact (PathBasics.path_adj_iff hRl (by omega) (by omega)).mpr (Or.inl rfl)
  have hother : ∀ z ∈ SPGT.interior R, z ≠ ((R)[1]'(by omega)) → ¬ Gᶜ.Adj p₁ z := by
    intro z hz hzne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hRl hz
    rw [← hR0] at hadj
    have hcc := (PathBasics.path_adj_iff hRl (by omega) hk).mp hadj
    have hkne : k ≠ 1 := by
      intro h
      exact hzne (by subst h; rfl)
    omega
  have hR' : IsPathFrom Gᶜ (p₁ :: SPGT.interior R) p₁ ((R)[R.length - 2]'(by omega)) :=
    PathAttach.isPathFrom_cons hIR hadjR1 hp₁R hother
  -- the antihole `p₂-Q-p₃-p₁-R-p₂`
  have hQsplit : ∀ x ∈ Q, x = b ∨ x = pn ∨ x ∈ SPGT.interior Q := by
    intro x hx
    by_cases h1 : x = b
    · exact Or.inl h1
    by_cases hh2 : x = pn
    · exact Or.inr (Or.inl hh2)
    exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, h1, hh2⟩))
  have hdisj : ∀ x ∈ Q, x ∉ (p₁ :: SPGT.interior R) := by
    intro x hx hxR
    rcases List.mem_cons.mp hxR with h | h
    · rcases hQsplit x hx with h' | h' | h'
      · exact hb1 (h'.symm.trans h)
      · exact h1n ((h'.symm.trans h).symm)
      · exact hpX p₁ hp₁p (h ▸ hQint x h')
    · have hxY : x ∈ Y := hRint x h
      rcases hQsplit x hx with h' | h' | h'
      · exact hpY b hbp (h' ▸ hxY)
      · exact hpY pn hpnp (h' ▸ hxY)
      · exact hXnY x (hQint x h') hxY
  have hcross : ∀ x ∈ Q, ∀ z ∈ (p₁ :: SPGT.interior R),
      (Gᶜ.Adj x z ↔ ((x = pn ∧ z = p₁) ∨
        (x = b ∧ z = ((R)[R.length - 2]'(by omega))))) := by
    intro x hx z hz
    have hp₁nY : p₁ ∉ Y := hpY p₁ hp₁p
    rcases List.mem_cons.mp hz with hzp | hzi
    · -- `z = p₁`
      have hRm2Y : ((R)[R.length - 2]'(by omega)) ∈ Y :=
        hRint _ (PathBasics.getElem_mem_interior hRl (by omega) (by omega) (by omega))
      have hne : z ≠ ((R)[R.length - 2]'(by omega)) := by
        rw [hzp]
        intro hc
        exact hp₁nY (hc ▸ hRm2Y)
      rcases hQsplit x hx with h' | h' | h'
      · rw [h', hzp]
        refine iff_of_false (fun hcc => hcc.2 hadj1b.symm) ?_
        rintro (⟨hcc, -⟩ | ⟨-, hcc⟩)
        · exact hbn hcc
        · exact hp₁nY (hcc ▸ hRm2Y)
      · rw [h', hzp]
        exact iff_of_true ⟨fun hcc => h1n hcc.symm, fun hcc => hn1n hcc.symm⟩ (Or.inl ⟨rfl, rfl⟩)
      · have hxX : x ∈ X := hQint x h'
        have hne' := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp h'
        refine iff_of_false ?_ ?_
        · rw [hzp]
          exact fun hcc => hcc.2 (((hXuniq p₁ hp₁p).mpr rfl) x hxX).symm
        · rintro (⟨hcc, -⟩ | ⟨hcc, -⟩)
          · exact hne'.2.2 hcc
          · exact hne'.2.1 hcc
    · -- `z ∈ R*`
      have hzY : z ∈ Y := hRint z hzi
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hRl hzi
      have hzp₁ : ((R)[k]'hk) ≠ p₁ := fun hc => hp₁nY (hc ▸ hzY)
      rcases hQsplit x hx with h' | h' | h'
      · -- `x = b = R[m-1]`
        have hA : Gᶜ.Adj b ((R)[k]'hk) ↔ k = R.length - 2 := by
          constructor
          · intro hcc
            rw [← hRn] at hcc
            have := (PathBasics.path_adj_iff hRl (by omega) hk).mp hcc
            omega
          · rintro rfl
            rw [← hRn]
            exact (PathBasics.path_adj_iff hRl (by omega) hk).mpr (Or.inr (by omega))
        have hE : (((R)[k]'hk) = ((R)[R.length - 2]'(by omega))) ↔ k = R.length - 2 :=
          hRinj k (R.length - 2) hk (by omega)
        rw [h', hA]
        constructor
        · intro hcc
          exact Or.inr ⟨rfl, hE.mpr hcc⟩
        · rintro (⟨hcc, -⟩ | ⟨-, hcc⟩)
          · exact absurd hcc hbn
          · exact hE.mp hcc
      · rw [h']
        refine iff_of_false (fun hcc => hcc.2 (((hYuniq pn hpnp).mpr rfl) _ hzY)) ?_
        rintro (⟨-, hcc⟩ | ⟨hcc, -⟩)
        · exact hzp₁ hcc
        · exact hbn hcc.symm
      · have hxX : x ∈ X := hQint x h'
        have hne' := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp h'
        refine iff_of_false (fun hcc => hcc.2 (hcompl x hxX _ hzY)) ?_
        rintro (⟨hcc, -⟩ | ⟨hcc, -⟩)
        · exact hne'.2.2 hcc
        · exact hne'.2.1 hcc
  have hhole : IsHoleList Gᶜ (Q ++ (p₁ :: SPGT.interior R)) := by
    refine PathGlue.glue_hole hQ hR' hdisj hcross ?_
    simp only [List.length_cons, PathBasics.interior_length]
    omega
  have heven := hG.2 _ hhole
  have hlenhole : holeLength (Q ++ (p₁ :: SPGT.interior R)) = Q.length + (R.length - 1) := by
    simp only [holeLength, List.length_append, List.length_cons, PathBasics.interior_length]
    omega
  rw [hlenhole, Nat.even_iff] at heven
  rcases Nat.even_or_odd (pathLength Q) with hq | hq
  · rw [Nat.even_iff] at hq
    refine Or.inr ⟨?_, ?_⟩
    · rw [Nat.odd_iff]; omega
    · rw [Nat.not_odd_iff_even, Nat.even_iff]; omega
  · rw [Nat.odd_iff] at hq
    refine Or.inl ⟨?_, ?_⟩
    · rw [Nat.odd_iff]; omega
    · rw [Nat.not_odd_iff_even, Nat.even_iff]; omega

end Len2



section BergeBranch

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"Let `P'` be the path `p₁-⋯-pₙ-y` of `G₀`.  Then `P'` has odd length `≥ 5`.  If `G₀` is
Berge then by 2.1 there is a leap for `P'` in `X`, and the result follows."* -/
theorem branch_berge {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    (hXa : AnticonnectedSet G X) {p : List V} {p₁ pn : V}
    (hp : IsPathList G p) (hpX : ∀ w ∈ p, w ∉ X) (hn5 : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (heven : Even (pathLength p))
    (hBerge : Berge (cG0 G p X pn)) :
    ∃ x₁ ∈ X, ∃ x₂ ∈ X, ¬ G.Adj x₁ x₂ ∧ IsPathList G (x₁ :: (p.tail ++ [x₂])) := by
  classical
  have hpos : 0 < p.length := by omega
  have hplen : p.length = pathLength p + 1 := PathBasics.length_eq_pathLength_add_one hp
  have hp0 : (p[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
  have hplast : (p[p.length - 1]'(by omega)) = pn :=
    PathBasics.getElem_last_of_getLast? hlast (by omega)
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hPF : IsPathFrom G p p₁ pn := ⟨hp, hhead, hlast⟩
  have hne1n : p₁ ≠ pn := PathBasics.isPathFrom_ends_ne hPF (by omega)
  have hXW : X ⊆ cW p X := fun z hz => Or.inr hz
  have hpW : ∀ z ∈ p, z ∈ cW p X := fun z hz => Or.inl hz
  -- `p = p₁ :: p.tail`, and the tail is a path from `p₂` to `pₙ`
  have hpcons : p = p₁ :: p.tail := by
    cases hpe : p with
    | nil => rw [hpe] at hhead; simp at hhead
    | cons z t =>
      rw [hpe] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead]
  have hp₁tail : p₁ ∉ p.tail := by
    have h := hp.2.1
    rw [hpcons] at h
    exact (List.nodup_cons.mp h).1
  have htailsub : ∀ w ∈ p.tail, w ∈ p := fun w hw => List.tail_subset p hw
  have htailidx : ∀ w ∈ p.tail, ∃ (k : ℕ) (hk : k < p.length), 1 ≤ k ∧ (p[k]'hk) = w := by
    intro w hw
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem (htailsub w hw)
    refine ⟨k, hk, ?_, hkeq⟩
    by_contra hcon
    have hk0 : k = 0 := by omega
    subst hk0
    rw [hp0] at hkeq
    exact hp₁tail (hkeq ▸ hw)
  have hmemtail : ∀ (k : ℕ) (hk : k < p.length), 1 ≤ k → (p[k]'hk) ∈ p.tail := by
    intro k hk hk1
    rw [← List.drop_one]
    have hlt : k - 1 < (p.drop 1).length := by simp only [List.length_drop]; omega
    have h1 : ((p.drop 1)[k - 1]'hlt)
        = (p[1 + (k - 1)]'(by simp only [List.length_drop] at hlt; omega)) :=
      List.getElem_drop ..
    have heq : ((p.drop 1)[k - 1]'hlt) = (p[k]'hk) := by
      rw [h1]
      exact hp.2.1.getElem_inj_iff.mpr (by omega)
    rw [← heq]
    exact List.getElem_mem hlt
  have htailpath : IsPathFrom G p.tail (p[1]'(by omega)) pn := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← List.drop_one]
      exact PathBasics.isPathList_drop hp (by omega)
    · rw [← List.drop_one, List.head?_drop, List.getElem?_eq_getElem (by omega)]
    · rw [← List.drop_one, List.getLast?_drop, if_neg (by omega)]
      exact hlast
  -- the path `P' = p₁-⋯-pₙ-y` of `G₀`
  have hp' : IsPathFrom (cG G p X) p p₁ pn :=
    (RestrictGraph.isPathFrom_iff_of_subset hpW).mpr hPF
  have hpmap : IsPathFrom (cG0 G p X pn) (p.map Sum.inl) (Sum.inl p₁) (Sum.inl pn) :=
    (isPathFrom_map_inl (cG G p X) (cS X pn) p p₁ pn).mp hp'
  have hylen : (p.map (Sum.inl : V → V ⊕ Unit)).length = p.length := List.length_map ..
  have hyadj : (cG0 G p X pn).Adj (Sum.inr ()) (Sum.inl pn) :=
    (cG0_adj_inr' pn ()).mpr (Or.inr rfl)
  have hynotmem : (Sum.inr () : V ⊕ Unit) ∉ p.map Sum.inl := by
    intro h
    obtain ⟨z, -, hz⟩ := List.mem_map.mp h
    exact absurd hz (by simp)
  have hyother : ∀ z ∈ p.map (Sum.inl : V → V ⊕ Unit), z ≠ Sum.inl pn →
      ¬ (cG0 G p X pn).Adj (Sum.inr ()) z := by
    intro z hz hzne
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rw [cG0_adj_inr']
    rintro (hcc | hcc)
    · exact hpX w hw hcc
    · exact hzne (by rw [hcc])
  have hP' : IsPathFrom (cG0 G p X pn) (p.map Sum.inl ++ [Sum.inr ()]) (Sum.inl p₁)
      (Sum.inr ()) := PathAttach.isPathFrom_concat hpmap hyadj hynotmem hyother
  have hP'len : (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]).length = p.length + 1 := by
    simp
  have hP'get : ∀ (k : ℕ) (hk : k < p.length)
      (hk' : k < (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]).length),
      ((p.map Sum.inl ++ [Sum.inr ()])[k]'hk') = Sum.inl (p[k]'hk) := by
    intro k hk hk'
    have hklt : k < (p.map (Sum.inl : V → V ⊕ Unit)).length := by simpa using hk
    rw [List.getElem_append_left hklt, List.getElem_map]
  -- the hypotheses of 2.1
  have hX' : AnticonnectedSet (cG0 G p X pn) (Sum.inl '' X) :=
    PendantTransport.anticonnectedSet_pendant_restrict hXW hXa
  have hP'X : ∀ z ∈ (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]), z ∉ Sum.inl '' X := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
      rintro ⟨x, hx, hxe⟩
      exact hpX w hw (Sum.inl_injective hxe ▸ hx)
    · have : z = Sum.inr () := by simpa using h
      rw [this]
      exact PendantTransport.inr_notMem_image_inl
  have hodd : Odd (pathLength (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()])) := by
    rw [Nat.odd_iff]
    simp only [pathLength, hP'len]
    rw [Nat.even_iff] at heven
    omega
  have hcy : VertexComplete (cG0 G p X pn) (Sum.inr ()) (Sum.inl '' X) := by
    rintro z ⟨x, hx, rfl⟩
    exact (cG0_adj_inr' x ()).mpr (Or.inl hx)
  have hcp₁ : VertexComplete (cG0 G p X pn) (Sum.inl p₁) (Sum.inl '' X) := by
    rintro z ⟨x, hx, rfl⟩
    exact (cG0_adj_inl p₁ x).mpr
      ⟨(hXuniq p₁ hp₁mem).mpr rfl x hx, Or.inl hp₁mem, Or.inr hx⟩
  have hnoedge : ¬ ∃ w ∈ (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]),
      ∃ w' ∈ (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]),
      EdgeComplete (cG0 G p X pn) (Sum.inl '' X) w w' := by
    rintro ⟨w, hw, w', hw', hadj, hwc, hw'c⟩
    have hclass : ∀ z ∈ (p.map (Sum.inl : V → V ⊕ Unit) ++ [Sum.inr ()]),
        VertexComplete (cG0 G p X pn) z (Sum.inl '' X) → z = Sum.inl p₁ ∨ z = Sum.inr () := by
      intro z hz hzc
      rcases List.mem_append.mp hz with h | h
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
        refine Or.inl ?_
        have : VertexComplete G u X := by
          intro x hx
          exact ((cG0_adj_inl u x).mp (hzc (Sum.inl x) ⟨x, hx, rfl⟩)).1
        rw [(hXuniq u hu).mp this]
      · exact Or.inr (by simpa using h)
    have hnadj : ¬ (cG0 G p X pn).Adj (Sum.inl p₁) (Sum.inr ()) := by
      rw [cG0_adj_inr]
      rintro (hcc | hcc)
      · exact hpX p₁ hp₁mem hcc
      · exact hne1n hcc
    rcases hclass w hw hwc with hw1 | hw1 <;> rcases hclass w' hw' hw'c with hw2 | hw2
    · exact (cG0 G p X pn).ne_of_adj hadj (hw1.trans hw2.symm)
    · exact hnadj (by rw [← hw1, ← hw2]; exact hadj)
    · exact hnadj (by rw [← hw2, ← hw1]; exact hadj.symm)
    · exact (cG0 G p X pn).ne_of_adj hadj (hw1.trans hw2.symm)
  rcases thm_2_1 (cG0 G p X pn) hBerge (Sum.inl '' X) hX'
      (p.map Sum.inl ++ [Sum.inr ()]) (Sum.inl p₁) (Sum.inr ()) hP' hP'X hodd hcp₁ hcy with
    hc1 | ⟨-, a, haX, b, hbX, hleap⟩ | ⟨hc3, -⟩
  · exact absurd hc1 hnoedge
  · obtain ⟨a₀, ha₀X, rfl⟩ := haX
    obtain ⟨b₀, hb₀X, rfl⟩ := hbX
    obtain ⟨-, -, hab, hnab, hAd, hBd⟩ := hleap
    have htr : ∀ (x : V), x ∈ X → ∀ (k : ℕ) (hk : k < p.length),
        ((cG0 G p X pn).Adj (Sum.inl x) ((p.map Sum.inl ++ [Sum.inr ()])[k]'(by omega)))
          ↔ G.Adj x (p[k]'hk) := by
      intro x hx k hk
      rw [hP'get k hk (by omega), cG0_adj_inl]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, Or.inr hx, Or.inl (List.getElem_mem hk)⟩
    have hA : ∀ w ∈ p.tail, (G.Adj a₀ w ↔ w = (p[1]'(by omega))) := by
      intro w hw
      obtain ⟨k, hk, hk1, rfl⟩ := htailidx w hw
      rw [← htr a₀ ha₀X k hk, hAd k (by omega)]
      constructor
      · intro h
        have hk1' : k = 1 := by omega
        subst hk1'
        rfl
      · intro h
        have hkk : k = 1 := hp.2.1.getElem_inj_iff.mp h
        omega
    have hB : ∀ w ∈ p.tail, (G.Adj b₀ w ↔ w = pn) := by
      intro w hw
      obtain ⟨k, hk, hk1, rfl⟩ := htailidx w hw
      rw [← htr b₀ hb₀X k hk, hBd k (by omega)]
      constructor
      · intro h
        have hk2 : k = p.length - 1 := by omega
        subst hk2
        exact hplast
      · intro h
        rw [← hplast] at h
        have hkk : k = p.length - 1 := hp.2.1.getElem_inj_iff.mp h
        omega
    have hnadj : ¬ G.Adj a₀ b₀ := by
      intro hadj
      refine hnab ?_
      rw [cG0_adj_inl]
      exact ⟨hadj, Or.inr ha₀X, Or.inr hb₀X⟩
    refine ⟨a₀, ha₀X, b₀, hb₀X, hnadj, ?_⟩
    have ha₀tail : a₀ ∉ p.tail := fun h => hpX a₀ (htailsub a₀ h) ha₀X
    have hb₀tail : b₀ ∉ p.tail := fun h => hpX b₀ (htailsub b₀ h) hb₀X
    refine (PathAttach.isPathFrom_cons_concat htailpath ?_ ?_ hnadj ?_ ha₀tail hb₀tail
      ?_ ?_).1
    · exact (hA _ (hmemtail 1 (by omega) (by omega))).mpr rfl
    · refine (hB pn ?_).mpr rfl
      rw [← hplast]
      exact hmemtail (p.length - 1) (by omega) (by omega)
    · intro hc
      exact hab (by rw [hc])
    · intro z hz hzne hadj
      exact hzne ((hA z hz).mp hadj)
    · intro z hz hzne hadj
      exact hzne ((hB z hz).mp hadj)
  · exfalso
    simp only [pathLength, hP'len] at hc3
    omega

end BergeBranch



end Workspace.ProofLemmas.Thm29Aux
