import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.NoMajorVerticesGraphShape
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameK4Shape
import Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapMeets
import Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapCross

/-!
# 8.5: the closing paragraph in the case `n = 1`

PAPER (printed pp. 44–45, the last paragraph of the proof of 8.5), verbatim:

*"Now for any optimal choice of rungs, if `hi` is its traversal, then by (4) and the optimality
of the choice, it follows that `K` consists precisely of the edges of `J` with exactly one end
in common with `hi`, together possibly with `hi` itself.  In particular `hi` meets all edges in
`K`.  We may assume that some other edge `jk` is the traversal for some other optimal choice;
and hence (since `J` is 3-connected) it follows that `J = K₄` and `jk` is disjoint from `hi`,
and neither edge is in `K`.  Hence `V(J) = {h,i,j,k}`.  Now since the strip system is not
degenerate, there is one of the four edges `hj, hk, ij, ik` whose strip contains a rung of
nonzero length; some `hj`-rung `R` has length `> 0` say.  From (4) it follows that exactly one
vertex of `R` is in `X`, one of its ends; say the end in `N_h`.  Let `R_uv` (`uv ∈ E(J)`) be any
choice of rungs such that `R_hj = R`.  Since the end of `R` in `N_j` does not belong to `X`, it
follows from (4) that for each of `R_hk, R_ij, R_ik`, its unique vertex in `X` is its end in
`N_h ∪ N_i`.  Since the choice of these rungs was arbitrary, it follows that `X ∩ S_hk = N_hk`,
`X ∩ S_ij = N_ij`, and `X ∩ S_ik = N_ik`.  If also `X ∩ S_hj = N_hj` then `hi` is the traversal
for every choice of rungs, contrary to (6), so `X ∩ S_hj ≠ N_hj`.  It follows that every
`ij`-rung has length 0; for if one, `R'` say, has length `> 0`, then its unique vertex in `X` is
its end in `N_i`, and by exchanging `h` and `i` it follows that `X ∩ S_hj = N_hj`, a
contradiction.  Similarly all `hk`- and `ik`-rungs have length 0, and therefore all `hj`-rungs
have even length, since `G` is Berge.  From (1), we may assume that `f₁` is adjacent to `r_hj`
and complete to `S_hk`, and `f_n` is complete to `S_ij ∪ S_ik`, and there are no other edges
between `F` and `S_hk ∪ S_ij ∪ S_ik ∪ {r_hj}`.  Let `R'` be an `hj`-rung such that its vertex in
`N_h` (`r'_hj`, say) is not its unique vertex in `X`.  Consequently, its other end (`r'_jh`) is
its unique vertex in `X`.  By the same argument with `hi` and `jk` exchanged, it follows that
one of `f₁, f_n` is complete to `S_ij ∪ {r'_jh}` and the other to `S_hk ∪ S_ik`; and hence
`n = 1`.  But then the path `f₁-r_hj-R_hj-r_jh-r_ji-f₁` is an odd hole, a contradiction.  This
proves 8.5."*

**Why this is a separate work item.**  `Thm85EndgameClosing.closing` already carries this
paragraph, but it takes claim (4) in the form `HasUniqueTraversal`, an *ordered* uniqueness, and
it discharges the paragraph by deriving `f₁ = f_n` and then contradicting that ordered
uniqueness — `IsTraversal … R i j` and `IsTraversal … R j i` are the same statement once
`f₁ = f_n`.  That shortcut is unavailable exactly when `f₁ = f_n`, which is the case the `n = 1`
step of 8.5 has to rule out.  The version below is the same paragraph with `f₁ = f_n` assumed
and claim (4) weakened to the existence of a traversal; it is the printed odd-hole argument,
which stops at *"But then the path `f₁-r_hj-R_hj-r_jh-r_ji-f₁` is an odd hole"* and is not
formalized anywhere else in this development.

## How the proof goes

The two choices of rungs with different traversals put us in the `K₄` of the paragraph:
`Thm85EndgamePathTwoVerticesGapMeets.k4_neighbourhoods` names its four vertices `h, i, j, k`,
with `hi` the traversal of the first choice `R` and `jk` the traversal of the second choice
`R'`.

The rest of the paragraph is carried by
`Thm85EndgamePathTwoVerticesGapCross.cross_rung_end`, which says that on each of the four
edges meeting `hi` in one vertex, *every* rung has its end on `hi` as its unique vertex
adjacent to `f₁` — that is the printed *"From (4) it follows that exactly one vertex of `R` is
in `X`, one of its ends"*, and its proof is where the printed odd hole
`f₁-r_hj-R_hj-r_jh-r_ji-f₁` is used.  Applying it to the four rungs `R' h j`, `R' h k`,
`R' i j`, `R' i k` of the *second* choice says that `R'` satisfies the two `f₁`/`f_n` bullets
of claim (4) at the edge `hi`, while `jk` is a full traversal of `R'` disjoint from `hi`.  That
is exactly the hypothesis of `Thm85EndgameK4Shape.disjoint_traversals_absurd`, the paper's
*"`J = K₄`, the four rungs have length `0`, and so `L(H)` is degenerate, contrary to (1)"*.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions
open Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapMeets
open Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapCross

/-- **Gap: the closing paragraph of the proof of 8.5, for `n = 1`** (printed pp. 44–45).

Two choices of rungs with different traversals force `J = K₄`, and then the printed argument
ends with the odd hole `f₁-r_hj-R_hj-r_jh-r_ji-f₁`.  See the module docstring for the full
paper text and for why the already-formalized `Thm85EndgameClosing.closing` cannot be used when
`f₁ = f_n`. -/
theorem n1_different_traversals_absurd {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
          (phi : H.lineGraph ≃g G.induce K'),
        IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' phi)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ Rc u v} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P})
    (hfeq : f₁ = fn)
    (hclaim4 : ∀ Rc : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc →
      ∃ p q : U, IsTraversal G J N F f₁ fn Rc p q)
    (hclaim5 : ∀ Rc : U → U → List V, RungChoice G J S N Rc →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc)
    (hclaim6 : HasDifferentTraversals G J S N F f₁ fn) :
    False := by
  classical
  subst hfeq
  -- `n = 1`: the vertex set of the path is the single vertex `f₁`
  have hf₁F : f₁ ∈ F := by
    rw [hPF]; exact List.mem_of_mem_head? hP.2.1
  have hf₁out : f₁ ∉ stripSystemVertices J S := hFcompl hf₁F
  -- the `K₄` of the closing paragraph
  obtain ⟨R, R', h, i, j, k, hR, hR', htrav, htrav', hdiff⟩ := hclaim6
  obtain ⟨hnd, hNh, hNi, hNj, hNk⟩ :=
    k4_neighbourhoods G hG J hJ S N hSN F f₁ f₁ hf₁F hf₁F hclaim1 hclaim4 hclaim5
      hR hR' htrav htrav' hdiff
  have hd : h ≠ i ∧ h ≠ j ∧ h ≠ k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd
    tauto
  obtain ⟨ehi, ehj, ehk, eij, eik, ejk⟩ := hd
  have hhi : J.Adj h i := (hNh i).mpr (Or.inl rfl)
  have hcover : ∀ c : U, c = h ∨ c = i ∨ c = j ∨ c = k :=
    Thm85EndgameK4Shape.cover_of_hub_neighbourhoods hJ ehj ehk eij eik
      (fun w hw => (hNh w).mp hw) (fun w hw => (hNi w).mp hw)
  have hall : ∀ u v : U, u ≠ v → (u = h ∨ u = i ∨ u = j ∨ u = k) →
      (v = h ∨ v = i ∨ v = j ∨ v = k) → J.Adj u v := by
    intro u v huv hu hv
    rcases hu with rfl | rfl | rfl | rfl
    · rcases hv with hc | hc | hc | hc
      · exact absurd hc.symm huv
      · exact (hNh v).mpr (Or.inl hc)
      · exact (hNh v).mpr (Or.inr (Or.inl hc))
      · exact (hNh v).mpr (Or.inr (Or.inr hc))
    · rcases hv with hc | hc | hc | hc
      · exact (hNi v).mpr (Or.inl hc)
      · exact absurd hc.symm huv
      · exact (hNi v).mpr (Or.inr (Or.inl hc))
      · exact (hNi v).mpr (Or.inr (Or.inr hc))
    · rcases hv with hc | hc | hc | hc
      · exact (hNj v).mpr (Or.inl hc)
      · exact (hNj v).mpr (Or.inr (Or.inl hc))
      · exact absurd hc.symm huv
      · exact (hNj v).mpr (Or.inr (Or.inr hc))
    · rcases hv with hc | hc | hc | hc
      · exact (hNk v).mpr (Or.inl hc)
      · exact (hNk v).mpr (Or.inr (Or.inl hc))
      · exact (hNk v).mpr (Or.inr (Or.inr hc))
      · exact absurd hc.symm huv
  -- "`J = K₄`"
  have hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := by
    refine NoMajorVerticesGraphShape.k4_of_two_hubs J hJ h i hhi ?_ ?_
    · intro w hwh hwi
      rcases hcover w with hc | hc | hc | hc
      · exact absurd hc hwh
      · exact absurd hc hwi
      · subst hc
        exact ⟨((hNh w).mpr (Or.inr (Or.inl rfl))).symm,
          ((hNi w).mpr (Or.inr (Or.inl rfl))).symm⟩
      · subst hc
        exact ⟨((hNh w).mpr (Or.inr (Or.inr rfl))).symm,
          ((hNi w).mpr (Or.inr (Or.inr rfl))).symm⟩
    · intro w hwh hwi x hx y hy
      have hxv : x = j ∨ x = k := by
        rcases hcover x with hc | hc | hc | hc
        · exact absurd hc hx.2.1
        · exact absurd hc hx.2.2
        · exact Or.inl hc
        · exact Or.inr hc
      have hyv : y = j ∨ y = k := by
        rcases hcover y with hc | hc | hc | hc
        · exact absurd hc hy.2.1
        · exact absurd hc hy.2.2
        · exact Or.inl hc
        · exact Or.inr hc
      rcases hcover w with hc | hc | hc | hc
      · exact absurd hc hwh
      · exact absurd hc hwi
      · subst hc
        rcases hxv with hx1 | hx1
        · exact absurd (hx1 ▸ hx.1) (SimpleGraph.irrefl J)
        · rcases hyv with hy1 | hy1
          · exact absurd (hy1 ▸ hy.1) (SimpleGraph.irrefl J)
          · rw [hx1, hy1]
      · subst hc
        rcases hxv with hx1 | hx1
        · rcases hyv with hy1 | hy1
          · rw [hx1, hy1]
          · exact absurd (hy1 ▸ hy.1) (SimpleGraph.irrefl J)
        · exact absurd (hx1 ▸ hx.1) (SimpleGraph.irrefl J)
  -- the four cross edges: every rung meets `f₁` only at its end on `hi`
  have hcross : ∀ u v : U, (u = h ∨ u = i) → (v = j ∨ v = k) →
      ∃ r : V, r ∈ R' u v ∧ r ∈ N u ∧
        UniqueEdgeBetween G {x : V | x ∈ R' u v} F r f₁ := by
    have hperm : ∀ u v w x : U, [u, v, w, x].Nodup →
        (∀ c : U, c = u ∨ c = v ∨ c = w ∨ c = x) →
        IsTraversal G J N F f₁ f₁ R u v →
        ∃ r : V, r ∈ R' u w ∧ r ∈ N u ∧
          UniqueEdgeBetween G {y : V | y ∈ R' u w} F r f₁ := by
      intro u v w x hnd' hcover' htrav''
      have huw : J.Adj u w := by
        refine hall u w ?_ (hcover u) (hcover w)
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          and_true, not_or] at hnd'
        tauto
      exact cross_rung_end G hG J hJ S N hSN hK4 F f₁ hf₁F hf₁out hclaim1 hclaim4 hclaim5
        u v w x hnd' hcover' (fun p q hpq _ _ => hall p q hpq (hcover p) (hcover q))
        R hR htrav'' (R' u w) (hR'.1 u w huw)
    have hswapt : IsTraversal G J N F f₁ f₁ R i h := traversal_swap htrav
    intro u v hu hv
    rcases hu with rfl | rfl
    · rcases hv with rfl | rfl
      · exact hperm u i v k hnd hcover htrav
      · refine hperm u i v j ?_ ?_ htrav
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or] at hnd ⊢
          tauto
        · intro c
          rcases hcover c with hc | hc | hc | hc
          · exact Or.inl hc
          · exact Or.inr (Or.inl hc)
          · exact Or.inr (Or.inr (Or.inr hc))
          · exact Or.inr (Or.inr (Or.inl hc))
    · rcases hv with rfl | rfl
      · refine hperm u h v k ?_ ?_ hswapt
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or] at hnd ⊢
          tauto
        · intro c
          rcases hcover c with hc | hc | hc | hc
          · exact Or.inr (Or.inl hc)
          · exact Or.inl hc
          · exact Or.inr (Or.inr (Or.inl hc))
          · exact Or.inr (Or.inr (Or.inr hc))
      · refine hperm u h v j ?_ ?_ hswapt
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or] at hnd ⊢
          tauto
        · intro c
          rcases hcover c with hc | hc | hc | hc
          · exact Or.inr (Or.inl hc)
          · exact Or.inl hc
          · exact Or.inr (Or.inr (Or.inr hc))
          · exact Or.inr (Or.inr (Or.inl hc))
  -- `R'` has a full traversal `jk` disjoint from `hi`, and it obeys the two bullets at `hi`
  have hb1 : ∀ w : U, w ≠ i → J.Adj h w →
      ∃ r : V, r ∈ R' h w ∧ r ∈ N h ∧ UniqueEdgeBetween G {x : V | x ∈ R' h w} F r f₁ := by
    intro w hw hhw
    rcases hcover w with hc | hc | hc | hc
    · exact absurd (hc ▸ hhw) (SimpleGraph.irrefl J)
    · exact absurd hc hw
    · exact hcross h w (Or.inl rfl) (Or.inl hc)
    · exact hcross h w (Or.inl rfl) (Or.inr hc)
  have hb2 : ∀ w : U, w ≠ h → J.Adj i w →
      ∃ r : V, r ∈ R' i w ∧ r ∈ N i ∧ UniqueEdgeBetween G {x : V | x ∈ R' i w} F r f₁ := by
    intro w hw hiw
    rcases hcover w with hc | hc | hc | hc
    · exact absurd hc hw
    · exact absurd (hc ▸ hiw) (SimpleGraph.irrefl J)
    · exact hcross i w (Or.inr rfl) (Or.inl hc)
    · exact hcross i w (Or.inr rfl) (Or.inr hc)
  exact Thm85EndgameK4Shape.disjoint_traversals_absurd G hG J hJ S N hSN F f₁ f₁
    hclaim1 R' hR' h i j k hnd hhi hb1 hb2 htrav'

end Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGap
