import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm85RungChoice
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EnlargeStripBySet

/-!
# 8.5, claim (6): two choices of rungs have different traversals

PAPER (printed p. 44):

*"(6) There are two choices of rungs with different traversals.*

*Take a choice of rungs, and let `ij` be its traversal; and suppose that all other choices of
rungs have the same traversal.  Let `A₁ = N_i \ S_ij`, and `A₂ = N_j \ S_ij`.  From (4),(5), and
the uniqueness of `ij` it follows that `X ∩ (V(S,N) \ S_ij) = A₁ ∪ A₂`.  Hence `n ≥ 2`, for if
`n = 1` then we can add `f₁` to `N_i`, `N_j` and `S_ij`, contrary to the maximality of the strip
system.  Choose `x₁ ∈ A₁` and `x₂ ∈ A₂` in disjoint strips.  From (4), `x₁` is adjacent to
exactly one of `f₁, f_n`, say `f₁`.  For any other vertex `x₃ ∈ A₂`, let `R_uv` be a choice of
rungs forming `L(H)` say, such that `x₁, x₃ ∈ V(H)`.  From (4) and (5) it follows that `f_n` is
adjacent to `x₃`; and so `f_n` is complete to `A₂`, and similarly `f₁` is complete to `A₁`.
From the minimality of `F`, there are no other edges between `F` and `A₁ ∪ A₂`; but then we can
add `f₁` to `N_i`, `f_n` to `N_j`, and `F` to `S_ij`, contrary to the maximality of the strip
system.  This proves (6)."*

## How the printed argument is organised here

The printed proof splits off the case `n = 1` ("add `f₁` to `N_i`, `N_j` and `S_ij`") from the
case `n ≥ 2` ("add `f₁` to `N_i`, `f_n` to `N_j`, and `F` to `S_ij`").  Both are the same
enlargement `Thm85EnlargeStripBySet.thm85EnlargeStripBySet`, with the promoted sets `A_u` and
`A_v` taken to be `{f₁}` and `{f_n}`; when `n = 1` these two singletons coincide, which is
exactly the printed case `n = 1`.  So no case distinction on `n` is needed below.

The two facts that feed the enlargement are

* `attachment_dichotomy` — the printed sentence *"`X ∩ (V(S,N) \ S_ij) = A₁ ∪ A₂`"* together
  with *"there are no other edges between `F` and `A₁ ∪ A₂`"*, and
* `rung_end_adj` — the printed sentence *"`f_n` is complete to `A₂`, and similarly `f₁` is
  complete to `A₁`"*.

Both are obtained by choosing, through the vertex under consideration, a family of rungs
(`Thm85RungChoice.exists_rung_family_meeting`), which is broad by (5) and therefore has the
traversal `ij` by (4) and by the assumption that all traversals agree.

The printed proof reads *"`x₁` is adjacent to exactly one of `f₁, f_n`, say `f₁`"*, i.e. it
fixes the orientation of the traversal.  Here the orientation is fixed by
`orientation`: a choice whose traversal is the *reversed* pair `(j,i)` forces `f₁ = f_n`, and
then the two orientations say the same thing.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgameClaim6

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-! ## Two small combinatorial facts -/

/-- In a 3-connected graph every vertex has a neighbour different from any prescribed vertex. -/
theorem exists_adj_ne [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3) (a b : U) :
    ∃ w : U, J.Adj a w ∧ w ≠ b := by
  classical
  have h3 : 3 ≤ (J.neighborSet a).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  by_contra hc
  push_neg at hc
  have hsub : J.neighborSet a ⊆ ({b} : Set U) := by
    intro w hw
    exact Set.mem_singleton_iff.mpr (hc w hw)
  have hle : (J.neighborSet a).ncard ≤ ({b} : Set U).ncard :=
    Set.ncard_le_ncard hsub (Set.finite_singleton b)
  rw [Set.ncard_singleton] at hle
  omega

/-- `[a,b,p,q]` has no repeated entry as soon as the four pairwise distinctions that are not
already forced by `a ≠ b` and `p ≠ q` hold. -/
theorem nodup_four {a b p q : U} (hab : a ≠ b) (hpq : p ≠ q)
    (h1 : a ≠ p) (h2 : a ≠ q) (h3 : b ≠ p) (h4 : b ≠ q) : [a, b, p, q].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, and_true,
    not_or]
  tauto

/-! ## Reading off the traversal at one rung -/

section Traversal

variable {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
  {F : Set V} {f₁ fn : V} {R : U → U → List V} {p q : U}

/-- **The printed bullets of (4), read at a single rung.**

If the traversal of the choice `R` is `pq` and the edge `ab` is different from `pq`, then any
vertex of the rung `R_ab` that has a neighbour in `F` is the end of that rung in `N_p` (and its
only neighbour in `F` is `f₁`) or the end in `N_q` (and its only neighbour in `F` is `f_n`). -/
theorem attachment_of_traversal
    (hR : RungChoice G J S N R) (htrav : IsTraversal G J N F f₁ fn R p q)
    {a b : U} (hab : J.Adj a b) (hne : s(a, b) ≠ s(p, q))
    {x f : V} (hx : x ∈ R a b) (hf : f ∈ F) (hadj : G.Adj x f) :
    (x ∈ N p ∧ f = f₁) ∨ (x ∈ N q ∧ f = fn) := by
  classical
  obtain ⟨hpq, hbullet1, hbullet2, hbullet3⟩ := htrav
  -- The rung of the reversed pair has the same vertex set.
  have hrev : ∀ c d : U, J.Adj c d → ∀ z : V, z ∈ R c d → z ∈ R d c := by
    intro c d hcd z hz
    rw [hR.2 c d hcd, List.mem_reverse]
    exact hz
  -- The first bullet, applied at a neighbour `w ≠ q` of `p`.
  have hcase1 : ∀ w : U, w ≠ q → J.Adj p w → x ∈ R p w → (x ∈ N p ∧ f = f₁) := by
    intro w hwq hpw hxw
    obtain ⟨r, hrR, hrN, -, -, -, huniq⟩ := hbullet1 w hwq hpw
    obtain ⟨hxr, hfr⟩ := huniq x hxw f hf hadj
    exact ⟨hxr ▸ hrN, hfr⟩
  have hcase2 : ∀ w : U, w ≠ p → J.Adj q w → x ∈ R q w → (x ∈ N q ∧ f = fn) := by
    intro w hwp hqw hxw
    obtain ⟨r, hrR, hrN, -, -, -, huniq⟩ := hbullet2 w hwp hqw
    obtain ⟨hxr, hfr⟩ := huniq x hxw f hf hadj
    exact ⟨hxr ▸ hrN, hfr⟩
  by_cases hap : a = p
  · subst hap
    have hbq : b ≠ q := by
      intro h; exact hne (by rw [h])
    exact Or.inl (hcase1 b hbq hab hx)
  · by_cases haq : a = q
    · subst haq
      have hbp : b ≠ p := by
        intro h; exact hne (by rw [h, Sym2.eq_swap])
      exact Or.inr (hcase2 b hbp hab hx)
    · by_cases hbp : b = p
      · subst hbp
        have haq' : a ≠ q := haq
        exact Or.inl (hcase1 a haq' hab.symm (hrev a b hab x hx))
      · by_cases hbq : b = q
        · subst hbq
          exact Or.inr (hcase2 a hap hab.symm (hrev a b hab x hx))
        · -- the two edges are disjoint: the third bullet forbids the edge `xf`
          exfalso
          have hnd : [a, b, p, q].Nodup := nodup_four hab.ne hpq.ne hap haq hbp hbq
          exact hbullet3 a b hab hnd x hx f hf hadj

end Traversal

/-! ## The two consequences of (4)+(5) used by the enlargement -/

section Main

variable [Fintype V] [DecidableEq V] [Fintype U]
variable {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}

/-- A rung meets `N_u` in exactly one vertex. -/
theorem rung_N_unique {u v : U} {Q : List V} (hQ : IsUVRung G J S N u v Q)
    {x y : V} (hx : x ∈ Q) (hxN : x ∈ N u) (hy : y ∈ Q) (hyN : y ∈ N u) : x = y := by
  obtain ⟨s, -, -, -, huniq⟩ := StripSystemBasics.exists_rung_head hQ
  rw [huniq x hx hxN, huniq y hy hyN]

/-- **"Make a choice of rungs such that `x ∈ V(R_ab)`"**: a family of rungs through one
prescribed vertex. -/
theorem exists_choice_through (hSN : IsJStripSystem G J S N)
    {a b : U} (hab : J.Adj a b) {x : V} (hx : x ∈ S a b) :
    ∃ R : U → U → List V, RungChoice G J S N R ∧ x ∈ R a b := by
  classical
  obtain ⟨R, hR, hRsymm, hmeet⟩ :=
    Workspace.ProofLemmas.Thm85RungChoice.exists_rung_family_meeting hSN ({x} : Set V)
  obtain ⟨z, hzD, hzR⟩ := hmeet a b hab ⟨x, rfl, hx⟩
  rw [Set.mem_singleton_iff] at hzD
  exact ⟨R, ⟨hR, hRsymm⟩, hzD ▸ hzR⟩

/-- The same with two prescribed vertices on two different edges. -/
theorem exists_choice_through_two (hSN : IsJStripSystem G J S N)
    {a b c d : U} (hab : J.Adj a b) (hcd : J.Adj c d) (hne : s(a, b) ≠ s(c, d))
    {x y : V} (hx : x ∈ S a b) (hy : y ∈ S c d) :
    ∃ R : U → U → List V, RungChoice G J S N R ∧ x ∈ R a b ∧ y ∈ R c d := by
  classical
  obtain ⟨R, hR, hRsymm, hmeet⟩ :=
    Workspace.ProofLemmas.Thm85RungChoice.exists_rung_family_meeting hSN ({x, y} : Set V)
  refine ⟨R, ⟨hR, hRsymm⟩, ?_, ?_⟩
  · obtain ⟨z, hzD, hzR⟩ := hmeet a b hab ⟨x, by simp, hx⟩
    have hzS : z ∈ S a b := StripSystemBasics.rung_subset_strip (hR a b hab) z hzR
    rcases hzD with hz | hz
    · exact hz ▸ hzR
    · exact absurd (StripSystemBasics.edge_eq_of_mem_strips hSN hab hcd (hz ▸ hzS) hy) hne
  · obtain ⟨z, hzD, hzR⟩ := hmeet c d hcd ⟨y, by simp, hy⟩
    have hzS : z ∈ S c d := StripSystemBasics.rung_subset_strip (hR c d hcd) z hzR
    rcases hzD with hz | hz
    · exact absurd (StripSystemBasics.edge_eq_of_mem_strips hSN hab hcd hx (hz ▸ hzS)) hne
    · exact hz ▸ hzR

variable {F : Set V} {f₁ fn : V} {i j : U}

/-- **The orientation of the traversal.**

The printed proof says *"`x₁` is adjacent to exactly one of `f₁, f_n`, say `f₁`"*, thereby
fixing which end of the path `f₁ … f_n` is the `N_i`-end.  Under the hypothesis of (6) — all
choices have the same traversal *edge* — a choice whose traversal is the reversed pair `(j,i)`
forces `f₁ = f_n`, in which case the two orientations say the same thing. -/
theorem orientation (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R)
    (hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    {R₀ : U → U → List V} (hR₀ : RungChoice G J S N R₀)
    (htrav₀ : IsTraversal G J N F f₁ fn R₀ i j)
    (hsame : ∀ (R : U → U → List V) (p q : U), RungChoice G J S N R →
      IsTraversal G J N F f₁ fn R p q → s(p, q) = s(i, j))
    {R : U → U → List V} {p q : U} (hR : RungChoice G J S N R)
    (htrav : IsTraversal G J N F f₁ fn R p q) :
    (p = i ∧ q = j) ∨ (p = j ∧ q = i ∧ f₁ = fn) := by
  classical
  have hij : J.Adj i j := htrav₀.1
  rcases Sym2.eq_iff.mp (hsame R p q hR htrav) with ⟨hpi, hqj⟩ | ⟨hpj, hqi⟩
  · exact Or.inl ⟨hpi, hqj⟩
  · refine Or.inr ⟨hpj, hqi, ?_⟩
    rw [hpj, hqi] at htrav
    -- `p = j`, `q = i`: we produce a choice of rungs sharing one rung with `R₀` at `i` and one
    -- rung with `R` at `j`, and read (4) off it twice.
    obtain ⟨w, hiw, hwj⟩ := exists_adj_ne hJ i j
    obtain ⟨w', hjw', hw'i⟩ := exists_adj_ne hJ j i
    obtain ⟨y, hyR₀, hyS, hyN, -⟩ :=
      StripSystemBasics.exists_rung_head (hR₀.1 i w hiw)
    obtain ⟨y', hy'R, hy'S, hy'N, -⟩ :=
      StripSystemBasics.exists_rung_head (hR.1 j w' hjw')
    have hedgene : s(i, w) ≠ s(j, w') := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hij.ne h1
      · exact hw'i h1.symm
    obtain ⟨R₃, hR₃, hyR₃, hy'R₃⟩ :=
      exists_choice_through_two hSN hiw hjw' hedgene hyS hy'S
    obtain ⟨p₃, q₃, htrav₃, -⟩ := hclaim4 R₃ (hclaim5 R₃ hR₃)
    rcases Sym2.eq_iff.mp (hsame R₃ p₃ q₃ hR₃ htrav₃) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] at htrav₃
    · -- the traversal of `R₃` is `(i,j)`: compare its second bullet at `w'` with the first
      -- bullet of `R` at `w'`
      obtain ⟨r, hrR₃, hrN, -, -, hadjr, -⟩ := htrav₃.2.2.1 w' hw'i hjw'
      have hry : r = y' := rung_N_unique (hR₃.1 j w' hjw') hrR₃ hrN hy'R₃ hy'N
      subst hry
      obtain ⟨r', hr'R, hr'N, -, -, -, huniq⟩ := htrav.2.1 w' hw'i hjw'
      exact ((huniq r hy'R fn hfn hadjr).2).symm
    · -- the traversal of `R₃` is `(j,i)`: compare its second bullet at `w` with the first
      -- bullet of `R₀` at `w`
      obtain ⟨r, hrR₃, hrN, -, -, hadjr, -⟩ := htrav₃.2.2.1 w hwj hiw
      have hry : r = y := rung_N_unique (hR₃.1 i w hiw) hrR₃ hrN hyR₃ hyN
      subst hry
      obtain ⟨r', hr'R, hr'N, -, -, -, huniq⟩ := htrav₀.2.1 w hwj hiw
      exact ((huniq r hyR₀ fn hfn hadjr).2).symm


/-- **"`X ∩ (V(S,N) \ S_ij) = A₁ ∪ A₂`, and there are no other edges between `F` and
`A₁ ∪ A₂`"** (printed p. 44).

Every attachment of `F` outside the strip `S_ij` is an end in `N_i` of a rung whose only
neighbour in `F` is `f₁`, or an end in `N_j` of a rung whose only neighbour in `F` is `f_n`. -/
theorem attachment_dichotomy (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R)
    (hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    {R₀ : U → U → List V} (hR₀ : RungChoice G J S N R₀)
    (htrav₀ : IsTraversal G J N F f₁ fn R₀ i j)
    (hsame : ∀ (R : U → U → List V) (p q : U), RungChoice G J S N R →
      IsTraversal G J N F f₁ fn R p q → s(p, q) = s(i, j))
    {x : V} (hxV : x ∈ stripSystemVertices J S) (hxS : x ∉ S i j)
    {f : V} (hf : f ∈ F) (hadj : G.Adj x f) :
    (x ∈ N i ∧ f = f₁) ∨ (x ∈ N j ∧ f = fn) := by
  classical
  have hij : J.Adj i j := htrav₀.1
  obtain ⟨a, b, hab, hxab⟩ : ∃ a b : U, J.Adj a b ∧ x ∈ S a b := by
    simp only [stripSystemVertices, Set.mem_iUnion] at hxV
    obtain ⟨a, b, hab, hx⟩ := hxV
    exact ⟨a, b, hab, hx⟩
  have hedgene : s(a, b) ≠ s(i, j) := by
    intro h
    refine hxS ?_
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxab
    · rw [StripSystemBasics.strip_symm hSN hab] at hxab
      exact hxab
  obtain ⟨R, hR, hxR⟩ := exists_choice_through hSN hab hxab
  obtain ⟨p, q, htrav, -⟩ := hclaim4 R (hclaim5 R hR)
  have hpq := orientation hSN hJ hf₁ hfn hclaim4 hclaim5 hR₀ htrav₀ hsame hR htrav
  have hedgene' : s(a, b) ≠ s(p, q) := by
    rw [hsame R p q hR htrav]; exact hedgene
  have hkey := attachment_of_traversal hR htrav hab hedgene' hxR hf hadj
  rcases hpq with ⟨hpi, hqj⟩ | ⟨hpj, hqi, heq⟩
  · rw [hpi, hqj] at hkey
    exact hkey
  · rw [hpj, hqi] at hkey
    rcases hkey with ⟨hxN, hfe⟩ | ⟨hxN, hfe⟩
    · exact Or.inr ⟨hxN, hfe.trans heq⟩
    · exact Or.inl ⟨hxN, hfe.trans heq.symm⟩

/-- **"`f₁` is complete to `A₁`"** (printed p. 44): every vertex of `N_i ∩ S_iw`, for a
neighbour `w ≠ j` of `i`, is adjacent to `f₁`. -/
theorem rung_end_adj_left (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R)
    (hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    {R₀ : U → U → List V} (hR₀ : RungChoice G J S N R₀)
    (htrav₀ : IsTraversal G J N F f₁ fn R₀ i j)
    (hsame : ∀ (R : U → U → List V) (p q : U), RungChoice G J S N R →
      IsTraversal G J N F f₁ fn R p q → s(p, q) = s(i, j))
    {w : U} (hiw : J.Adj i w) (hwj : w ≠ j) {y : V} (hyN : y ∈ N i) (hyS : y ∈ S i w) :
    G.Adj y f₁ := by
  classical
  obtain ⟨R, hR, hyR⟩ := exists_choice_through hSN hiw hyS
  obtain ⟨p, q, htrav, -⟩ := hclaim4 R (hclaim5 R hR)
  rcases orientation hSN hJ hf₁ hfn hclaim4 hclaim5 hR₀ htrav₀ hsame hR htrav with
    ⟨hpi, hqj⟩ | ⟨hpj, hqi, heq⟩
  · rw [hpi, hqj] at htrav
    obtain ⟨r, hrR, hrN, -, -, hadjr, -⟩ := htrav.2.1 w hwj hiw
    have : r = y := rung_N_unique (hR.1 i w hiw) hrR hrN hyR hyN
    exact this ▸ hadjr
  · rw [hpj, hqi] at htrav
    obtain ⟨r, hrR, hrN, -, -, hadjr, -⟩ := htrav.2.2.1 w hwj hiw
    have : r = y := rung_N_unique (hR.1 i w hiw) hrR hrN hyR hyN
    rw [← this, heq]
    exact hadjr

/-- **"`f_n` is complete to `A₂`"** (printed p. 44). -/
theorem rung_end_adj_right (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R)
    (hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    {R₀ : U → U → List V} (hR₀ : RungChoice G J S N R₀)
    (htrav₀ : IsTraversal G J N F f₁ fn R₀ i j)
    (hsame : ∀ (R : U → U → List V) (p q : U), RungChoice G J S N R →
      IsTraversal G J N F f₁ fn R p q → s(p, q) = s(i, j))
    {w : U} (hjw : J.Adj j w) (hwi : w ≠ i) {y : V} (hyN : y ∈ N j) (hyS : y ∈ S j w) :
    G.Adj y fn := by
  classical
  obtain ⟨R, hR, hyR⟩ := exists_choice_through hSN hjw hyS
  obtain ⟨p, q, htrav, -⟩ := hclaim4 R (hclaim5 R hR)
  rcases orientation hSN hJ hf₁ hfn hclaim4 hclaim5 hR₀ htrav₀ hsame hR htrav with
    ⟨hpi, hqj⟩ | ⟨hpj, hqi, heq⟩
  · rw [hpi, hqj] at htrav
    obtain ⟨r, hrR, hrN, -, -, hadjr, -⟩ := htrav.2.2.1 w hwi hjw
    have : r = y := rung_N_unique (hR.1 j w hjw) hrR hrN hyR hyN
    exact this ▸ hadjr
  · rw [hpj, hqi] at htrav
    obtain ⟨r, hrR, hrN, -, -, hadjr, -⟩ := htrav.2.1 w hwi hjw
    have : r = y := rung_N_unique (hR.1 j w hjw) hrR hrN hyR hyN
    rw [← this, ← heq]
    exact hadjr


/-- **Claim (6) of the proof of 8.5** (printed p. 44):
*"There are two choices of rungs with different traversals."* -/
theorem claim6 (hJ : IsKConnected J 3) (hSN : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hclaim3 : ∃ u v u' v' : U, J.Adj u v ∧ J.Adj u' v' ∧ [u, v, u', v'].Nodup ∧
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty ∧
      (attachments G F (stripSystemVertices J S) ∩ S u' v').Nonempty)
    (P : List V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P})
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R)
    (hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R) :
    HasDifferentTraversals G J S N F f₁ fn := by
  classical
  by_contra hno
  -- A broad choice exists by (3), and by (4) it has a traversal `ij`.
  obtain ⟨R₀, hR₀broad⟩ :=
    Workspace.ProofLemmas.Thm85EndgameNotions.exists_broad_choice hSN
      (attachments G F (stripSystemVertices J S)) hclaim3
  have hR₀ : RungChoice G J S N R₀ := hR₀broad.1
  obtain ⟨i, j, htrav₀, -⟩ := hclaim4 R₀ hR₀broad
  -- the assumption of (6): all choices have the same traversal edge
  have hsame : ∀ (R : U → U → List V) (p q : U), RungChoice G J S N R →
      IsTraversal G J N F f₁ fn R p q → s(p, q) = s(i, j) := by
    intro R p q hR htrav
    by_contra hne
    exact hno ⟨R, R₀, p, q, i, j, hR, hR₀, htrav, htrav₀, hne⟩
  have hij : J.Adj i j := htrav₀.1
  have hf₁F : f₁ ∈ F := by rw [hPF]; exact List.mem_of_mem_head? hP.2.1
  have hfnF : fn ∈ F := by rw [hPF]; exact List.mem_of_getLast? hP.2.2
  -- `F` is disjoint from the strip system
  have hFdisj : Disjoint F (stripSystemVertices J S) :=
    Set.disjoint_left.mpr fun z hz hz' => (hFcompl hz) hz'
  have hFV : ∀ z ∈ F, z ∉ stripSystemVertices J S := fun z hz => hFcompl hz
  have hFN : ∀ (u : U), ∀ z ∈ F, z ∉ N u := fun u z hz hzN =>
    hFV z hz (StripSystemBasics.N_subset_vertices hSN u hzN)
  have hFS : ∀ (a b : U), J.Adj a b → ∀ z ∈ F, z ∉ S a b := fun a b hab z hz hzS =>
    hFV z hz (StripSystemBasics.strip_subset_vertices hab hzS)
  -- the enlarged families
  set S' : U → U → Set V := fun a b => if s(a, b) = s(i, j) then S i j ∪ F else S a b with hS'def
  set N' : U → Set V :=
    fun w => if w = i then N i ∪ {f₁} else if w = j then N j ∪ {fn} else N w with hN'def
  have hS'uv : S' i j = S i j ∪ F := if_pos rfl
  have hS'vu : S' j i = S i j ∪ F := if_pos (Sym2.eq_swap)
  have hS'other : ∀ a b : U, J.Adj a b → s(a, b) ≠ s(i, j) → S' a b = S a b :=
    fun a b _ h => if_neg h
  have hN'u : N' i = N i ∪ {f₁} := if_pos rfl
  have hN'v : N' j = N j ∪ {fn} := by
    simp only [hN'def]
    rw [if_neg hij.ne']
    simp
  have hN'other : ∀ w : U, w ≠ i → w ≠ j → N' w = N w := by
    intro w h1 h2
    simp only [hN'def]
    rw [if_neg h1, if_neg h2]
  -- "there are no other edges between `F` and `A₁ ∪ A₂`"
  have hattach : ∀ f ∈ F, ∀ a b : U, J.Adj a b → s(a, b) ≠ s(i, j) → ∀ y ∈ S a b, G.Adj f y →
      (f ∈ ({f₁} : Set V) ∧ y ∈ N i) ∨ (f ∈ ({fn} : Set V) ∧ y ∈ N j) := by
    intro f hf a b hab hne y hy hadj
    have hyV : y ∈ stripSystemVertices J S :=
      StripSystemBasics.strip_subset_vertices hab hy
    have hyS : y ∉ S i j := by
      intro hc
      exact hne (StripSystemBasics.edge_eq_of_mem_strips hSN hab hij hy hc)
    rcases attachment_dichotomy hSN hJ hf₁F hfnF hclaim4 hclaim5 hR₀ htrav₀ hsame
        hyV hyS hf hadj.symm with ⟨hyN, hfe⟩ | ⟨hyN, hfe⟩
    · exact Or.inl ⟨Set.mem_singleton_iff.mpr hfe, hyN⟩
    · exact Or.inr ⟨Set.mem_singleton_iff.mpr hfe, hyN⟩
  have hAucomplete : ∀ w : U, J.Adj i w → w ≠ j → ∀ p ∈ ({f₁} : Set V),
      ∀ y ∈ N i ∩ S i w, G.Adj p y := by
    intro w hiw hwj p hp y hy
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact (rung_end_adj_left hSN hJ hf₁F hfnF hclaim4 hclaim5 hR₀ htrav₀ hsame
      hiw hwj hy.1 hy.2).symm
  have hAvcomplete : ∀ w : U, J.Adj j w → w ≠ i → ∀ p ∈ ({fn} : Set V),
      ∀ y ∈ N j ∩ S j w, G.Adj p y := by
    intro w hjw hwi p hp y hy
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact (rung_end_adj_right hSN hJ hf₁F hfnF hclaim4 hclaim5 hR₀ htrav₀ hsame
      hjw hwi hy.1 hy.2).symm
  -- every vertex of the enlarged strip lies on a rung of the enlarged system
  have hcover : ∀ x ∈ S i j ∪ F, ∃ Q : List V, IsUVRung G J S' N' i j Q ∧ x ∈ Q := by
    rintro x (hx | hx)
    · obtain ⟨Q, hQ, hxQ⟩ := StripSystemBasics.exists_rung hSN hij hx
      obtain ⟨-, s, t, hpath, hsub, hNi, hNj⟩ := hQ
      refine ⟨Q, ⟨hij, s, t, hpath, ?_, ?_, ?_⟩, hxQ⟩
      · intro z hz
        rw [hS'uv]
        exact Or.inl (hsub z hz)
      · intro z hz
        have hzF : z ∉ F := fun hc => hFS i j hij z hc (hsub z hz)
        rw [hN'u]
        constructor
        · rintro (h | h)
          · exact (hNi z hz).mp h
          · exact absurd (Set.mem_singleton_iff.mp h ▸ hf₁F) hzF
        · intro h
          exact Or.inl ((hNi z hz).mpr h)
      · intro z hz
        have hzF : z ∉ F := fun hc => hFS i j hij z hc (hsub z hz)
        rw [hN'v]
        constructor
        · rintro (h | h)
          · exact (hNj z hz).mp h
          · exact absurd (Set.mem_singleton_iff.mp h ▸ hfnF) hzF
        · intro h
          exact Or.inl ((hNj z hz).mpr h)
    · refine ⟨P, ⟨hij, f₁, fn, hP, ?_, ?_, ?_⟩, ?_⟩
      · intro z hz
        rw [hS'uv]
        exact Or.inr (by rw [hPF]; exact hz)
      · intro z hz
        have hzF : z ∈ F := by rw [hPF]; exact hz
        rw [hN'u]
        constructor
        · rintro (h | h)
          · exact absurd h (hFN i z hzF)
          · exact Set.mem_singleton_iff.mp h
        · intro h
          exact Or.inr (Set.mem_singleton_iff.mpr h)
      · intro z hz
        have hzF : z ∈ F := by rw [hPF]; exact hz
        rw [hN'v]
        constructor
        · rintro (h | h)
          · exact absurd h (hFN j z hzF)
          · exact Set.mem_singleton_iff.mp h
        · intro h
          exact Or.inr (Set.mem_singleton_iff.mpr h)
      · rw [hPF] at hx; exact hx
  exact Workspace.ProofLemmas.Thm85EnlargeStripBySet.thm85EnlargeStripBySet
    G J S N hSN hmax i j hij F hFne hFdisj ({f₁} : Set V) ({fn} : Set V)
    (by rintro z hz; rw [Set.mem_singleton_iff] at hz; exact hz ▸ hf₁F)
    (by rintro z hz; rw [Set.mem_singleton_iff] at hz; exact hz ▸ hfnF)
    S' N' hS'uv hS'vu hS'other hN'u hN'v hN'other hattach hAucomplete hAvcomplete hcover

end Main

end Workspace.ProofLemmas.Thm85EndgameClaim6
