import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.MinimalConnectedIsPath

/-!
# 8.5: the minimal `F` is the vertex set of a path

PAPER (printed p. 42, proof of 8.5, the sentence immediately after (3)):

*"From (3) it follows that there exists a 2-element subset of `X` that is not local, and so from
the minimality of `F` it follows that `F` is the vertex set of a path, say `f₁, …, f_n`."*

Claim (3) produces two *disjoint* edges `uv`, `u'v'` of `J` with `X ∩ S_uv ≠ ∅ ≠ X ∩ S_{u'v'}`;
picking one attachment from each gives a two-element subset of `X` which lies in no single strip
(the strips are disjoint) and in no single `N_w` (a vertex of `S_uv ∩ N_w` forces `w ∈ {u,v}`,
and likewise for `u',v'`, and the four ends are distinct) — i.e. a two-element non-local subset
of `X`.  Every connected subset of `F` whose attachment set still contains that pair is
therefore non-local, so minimality of `F` forces `F` to be *minimal connected containing two
prescribed attachments*, and such a set is the vertex set of a path.

A *path* of the paper is `Core.IsPathList` — induced, non-null, connected, not a cycle, all
degrees `≤ 2` — presented as the list of its vertices in order, with named ends by
`Core.IsPathFrom`; the paper's `f₁, …, f_n` is that list, so `f₁` is its first and `f_n` its
last entry.

**Status: this module is a work item — the theorem below is stated but not yet proved.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85PathStructure

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- **"`F` is the vertex set of a path, say `f₁, …, f_n`"** (proof of 8.5, printed p. 42). -/
theorem thm85PathStructure {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim3 : ∃ u v u' v' : U, J.Adj u v ∧ J.Adj u' v' ∧ [u, v, u', v'].Nodup ∧
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty ∧
      (attachments G F (stripSystemVertices J S) ∩ S u' v').Nonempty) :
    ∃ (P : List V) (f₁ fn : V), IsPathFrom G P f₁ fn ∧ F = {x : V | x ∈ P} := by
  classical
  obtain ⟨u, v, u', v', huv, hu'v', hnd, hx, hx'⟩ := hclaim3
  obtain ⟨x, hxa, hxS⟩ := hx
  obtain ⟨x', hx'a, hx'S⟩ := hx'
  -- The two chosen attachments lie outside `F` and each has a neighbour in `F`.
  have hxV : x ∈ stripSystemVertices J S := hxa.1
  have hx'V : x' ∈ stripSystemVertices J S := hx'a.1
  have hxF : x ∉ F := fun h => (hFcompl h) hxV
  have hx'F : x' ∉ F := fun h => (hFcompl h) hx'V
  -- The two edges are disjoint, so the two strips are distinct and anticomplete.
  have hedge : s(u, v) ≠ s(u', v') := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp at hnd
  have hne : x ≠ x' := by
    intro h
    subst h
    exact hedge (StripSystemBasics.edge_eq_of_mem_strips hSN huv hu'v' hxS hx'S)
  have hnadj : ¬ G.Adj x x' :=
    StripSystemBasics.not_adj_of_disjoint_edges hSN huv hu'v' hnd hxS hx'S
  -- A path from `x` to `x'` whose interior is a connected subset of `F` attached to both.
  obtain ⟨p, hp, h3, hint, hconn, ⟨d, hd, hxd⟩, ⟨d', hd', hx'd'⟩⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hFconn hne hnadj hxF hx'F hxa.2 hx'a.2
  set F₁ : Set V := {z : V | z ∈ SPGT.interior p} with hF₁
  have hxF₁ : x ∈ attachments G F₁ (stripSystemVertices J S) := ⟨hxV, d, hd, hxd⟩
  have hx'F₁ : x' ∈ attachments G F₁ (stripSystemVertices J S) := ⟨hx'V, d', hd', hx'd'⟩
  -- `{x, x'}` is not local, hence neither is the whole attachment set of `F₁`.
  have hnotlocal :
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) := by
    rintro (⟨w, hw⟩ | ⟨a, b, hab, hsub⟩)
    · have hxNw : x ∈ N w := hw hxF₁
      have hx'Nw : x' ∈ N w := hw hx'F₁
      have hwuv : w = u ∨ w = v := by
        by_contra hc
        push_neg at hc
        have h0 : x ∈ S u v ∩ N w := ⟨hxS, hxNw⟩
        rw [StripSystemBasics.strip_inter_N_eq_empty hSN huv hc.1 hc.2] at h0
        exact h0
      have hwu'v' : w = u' ∨ w = v' := by
        by_contra hc
        push_neg at hc
        have h0 : x' ∈ S u' v' ∩ N w := ⟨hx'S, hx'Nw⟩
        rw [StripSystemBasics.strip_inter_N_eq_empty hSN hu'v' hc.1 hc.2] at h0
        exact h0
      rcases hwuv with rfl | rfl <;> rcases hwu'v' with h | h <;> subst h <;> simp at hnd
    · have h1 : s(a, b) = s(u, v) :=
        StripSystemBasics.edge_eq_of_mem_strips hSN hab huv (hsub hxF₁) hxS
      have h2 : s(a, b) = s(u', v') :=
        StripSystemBasics.edge_eq_of_mem_strips hSN hab hu'v' (hsub hx'F₁) hx'S
      exact hedge (h1.symm.trans h2)
  -- Minimality of `F` forces `F` to be that interior.
  have hFeq : F₁ = F := hFmin F₁ hint hconn hnotlocal
  refine ⟨SPGT.interior p, p[1]'(by omega), p[p.length - 2]'(by omega),
    PathGlue.isPathFrom_interior hp.1 h3, ?_⟩
  rw [← hFeq]

end Workspace.ProofLemmas.Thm85PathStructure
