import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Infrastructure: a non-cut vertex outside a connected proper subset -/

private theorem reach_mono {W : Type*} {G : SimpleGraph W} {S T : Set W} (hST : S ⊆ T)
    {u v : W} (hu : u ∈ S) (hv : v ∈ S)
    (hr : (G.induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    (G.induce T).Reachable ⟨u, hST hu⟩ ⟨v, hST hv⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun w => ⟨w.1, hST w.2⟩, fun {_ _} h => h⟩ : (G.induce S) →g (G.induce T)) p⟩

/-- *"Since `F ≠ A`, there exists `f ∈ A \ F` such that `A \ {f}` is connected."*

Take a vertex `f` of `S \ F` at maximum distance (inside `S`) from a root `r ∈ F`.  A
vertex of `F` reaches `r` inside `F`, which avoids `f`; a vertex of `S \ F` reaches `r`
by descending the distance function, and every vertex on that descent is strictly closer
to `r` than `f` is, hence different from `f`. -/
private theorem exists_noncut_outside {W : Type*} [Finite W] {G : SimpleGraph W}
    {S F : Set W} (hS : ConnectedSet G S) (hF : ConnectedSet G F) (hFS : F ⊆ S)
    {r : W} (hrF : r ∈ F) (hne : F ≠ S) :
    ∃ f ∈ S, f ∉ F ∧ ConnectedSet G (S \ {f}) := by
  have hrS : r ∈ S := hFS hrF
  set rr : ↥S := ⟨r, hrS⟩ with hrr
  set T : Set ↥S := {v : ↥S | (v : W) ∉ F} with hTdef
  have hTne : T.Nonempty := by
    rcases Set.eq_or_ssubset_of_subset hFS with h | h
    · exact absurd h hne
    · obtain ⟨v, hvS, hvF⟩ := Set.exists_of_ssubset h
      exact ⟨⟨v, hvS⟩, hvF⟩
  obtain ⟨a, haT, hamax⟩ :=
    Set.exists_max_image T (fun v => (G.induce S).dist rr v) (Set.toFinite T) hTne
  have haF : (a : W) ∉ F := haT
  have hrT : r ∈ S \ {(a : W)} := ⟨hrS, by
    simp only [Set.mem_singleton_iff]
    intro h
    exact haF (h ▸ hrF)⟩
  have hFsub : F ⊆ S \ {(a : W)} := by
    intro v hv
    refine ⟨hFS hv, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    exact haF (h ▸ hv)
  have hFreach : ∀ (x : W) (hx : x ∈ F),
      (G.induce (S \ {(a : W)})).Reachable ⟨r, hrT⟩ ⟨x, hFsub hx⟩ := by
    intro x hx
    exact reach_mono hFsub hrF hx (hF ⟨r, hrF⟩ ⟨x, hx⟩)
  refine ⟨(a : W), a.2, haF, ?_⟩
  have key : ∀ (n : ℕ) (x : W) (hxS : x ∈ S) (hxa : x ≠ (a : W)),
      (G.induce S).dist rr ⟨x, hxS⟩ ≤ n →
      (G.induce (S \ {(a : W)})).Reachable ⟨r, hrT⟩ ⟨x, ⟨hxS, hxa⟩⟩ := by
    intro n
    induction n with
    | zero =>
        intro x hxS hxa hd
        have h0 : (G.induce S).dist rr ⟨x, hxS⟩ = 0 := by omega
        have hxr : (rr : ↥S) = ⟨x, hxS⟩ := ((hS rr ⟨x, hxS⟩).dist_eq_zero_iff).mp h0
        have hval : r = x := congrArg Subtype.val hxr
        have he : (⟨r, hrT⟩ : ↥(S \ {(a : W)})) = ⟨x, ⟨hxS, hxa⟩⟩ := Subtype.ext hval
        rw [he]
    | succ m ih =>
        intro x hxS hxa hd
        by_cases hxF : x ∈ F
        · exact hFreach x hxF
        by_cases h0 : (G.induce S).dist rr ⟨x, hxS⟩ = 0
        · have hxr : (rr : ↥S) = ⟨x, hxS⟩ := ((hS rr ⟨x, hxS⟩).dist_eq_zero_iff).mp h0
          have hval : r = x := congrArg Subtype.val hxr
          have he : (⟨r, hrT⟩ : ↥(S \ {(a : W)})) = ⟨x, ⟨hxS, hxa⟩⟩ := Subtype.ext hval
          rw [he]
        · have hxT : (⟨x, hxS⟩ : ↥S) ∈ T := hxF
          have hdle : (G.induce S).dist rr ⟨x, hxS⟩ ≤ (G.induce S).dist rr a :=
            hamax _ hxT
          obtain ⟨w, hw⟩ := (hS rr ⟨x, hxS⟩).exists_walk_length_eq_dist
          set d := (G.induce S).dist rr ⟨x, hxS⟩ with hdef
          have hd1 : 1 ≤ d := by omega
          have hklt : d - 1 < w.length := by omega
          have hadj := w.adj_getVert_succ hklt
          have hk1 : (d - 1) + 1 = w.length := by omega
          have hend : w.getVert ((d - 1) + 1) = ⟨x, hxS⟩ := by
            rw [hk1]; exact w.getVert_length
          have hdy : (G.induce S).dist rr (w.getVert (d - 1)) ≤ d - 1 := by
            have h := SimpleGraph.dist_le (w.take (d - 1))
            rw [SimpleGraph.Walk.take_length] at h
            omega
          have hya : ((w.getVert (d - 1) : ↥S) : W) ≠ (a : W) := by
            intro he
            have hee : (w.getVert (d - 1) : ↥S) = a := Subtype.ext he
            rw [hee] at hdy
            omega
          have hreach := ih ((w.getVert (d - 1) : ↥S) : W) (w.getVert (d - 1)).2 hya
            (le_trans hdy (by omega))
          refine hreach.trans (SimpleGraph.Adj.reachable ?_)
          show G.Adj ((w.getVert (d - 1) : ↥S) : W) x
          have hgg : G.Adj ((w.getVert (d - 1) : ↥S) : W)
              ((w.getVert ((d - 1) + 1) : ↥S) : W) := hadj
          rw [hend] at hgg
          exact hgg
  intro p q
  have hp : (G.induce (S \ {(a : W)})).Reachable ⟨r, hrT⟩ p := by
    have h := key ((G.induce S).dist rr ⟨(p : W), p.2.1⟩) (p : W) p.2.1 p.2.2 le_rfl
    convert h using 2
  have hq : (G.induce (S \ {(a : W)})).Reachable ⟨r, hrT⟩ q := by
    have h := key ((G.induce S).dist rr ⟨(q : W), q.2.1⟩) (q : W) q.2.1 q.2.2 le_rfl
    convert h using 2
  exact hp.symm.trans hq

/-! ### Claim (3) -/

/-- Claim **(3)** of the printed proof: *"There is no connected `F ⊆ A` containing
neighbours of all of `x₀, x₁, x₂, y` except `A` itself."* -/
theorem claim3 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard) :
    ∀ F : Set V, F ⊆ A → ConnectedSet G F →
      (∃ a ∈ F, G.Adj (x 0) a) → (∃ a ∈ F, G.Adj (x 1) a) → (∃ a ∈ F, G.Adj (x 2) a) →
      (∃ a ∈ F, G.Adj y a) → F = A := by
  intro F hFA hFconn hF0 hF1 hF2 hFy
  by_contra hFneA
  -- *"From the minimality of `A`, some member of `Y` has no neighbour in `F` and is
  -- nonadjacent to `x₂`."*
  have hlt : F.ncard < A.ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hFA, hFneA⟩) (Set.toFinite A)
  have hbad : ∃ w ∈ Y, ¬ G.Adj w (x 2) ∧ ∀ a ∈ F, ¬ G.Adj w a := by
    by_contra hcon
    push_neg at hcon
    have hFgood : GoodA G z A₀ x Y y F :=
      ⟨hFA.trans hA.1, hFconn, hF0, hF1, hF2,
        (fun w hw hw2 => hcon w hw hw2), hFy⟩
    have := hAmin F hFgood
    omega
  obtain ⟨w₀, hw₀Y, hw₀2, hw₀F⟩ := hbad
  -- `w₀ ≠ y`, because `y` has a neighbour in `F`
  obtain ⟨by₀, hby₀F, hby₀⟩ := hFy
  have hw₀y : w₀ ≠ y := by
    rintro rfl
    exact hw₀F by₀ hby₀F hby₀
  have hw₀Y0 : w₀ ∈ Y \ {y} := ⟨hw₀Y, by simpa using hw₀y⟩
  -- *"In particular, `x₂` is not `Y₀`-complete"*
  have hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}) := by
    intro hcon
    exact hw₀2 (hcon w₀ hw₀Y0).symm
  -- *"and by (2), at least two vertices of `A` are `Y₀`-complete"*
  rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
    hL | ⟨-, P, hP, hPint, hcard⟩
  · exact hx2nc hL.1
  -- *"since `A` contains two `Y₀`-complete vertices"*: the edge count in claim (2)'s right
  -- disjunct yields two distinct `Y₀`-complete vertices in the interior of `P`, and the
  -- interior of `P` lies in `A`.  See `Thm192Infra.two_complete_in_interior`.
  obtain ⟨c, hcI, d, hdI, hcd, hcY, hdY⟩ :=
    Thm192Infra.two_complete_in_interior hws hA.1 hP hPint hcard
  have hcA : c ∈ A := hPint c hcI
  have hdA : d ∈ A := hPint d hdI
  -- *"Since `F ≠ A`, there exists `f ∈ A \ F` such that `A \ {f}` is connected."*
  obtain ⟨f, hfA, hfF, hfconn⟩ :=
    exists_noncut_outside hA.2.1 hFconn hFA hby₀F (fun h => hFneA h)
  have hFsub' : F ⊆ A \ {f} := by
    intro v hv
    refine ⟨hFA hv, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    exact hfF (h ▸ hv)
  -- *"But every vertex in `Y ∪ {x₀,x₁,x₂}` has a neighbour in `A \ {f}`"*
  have hgood : GoodA G z A₀ x Y y (A \ {f}) := by
    refine ⟨(Set.diff_subset).trans hA.1, hfconn, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨a, haF, ha⟩ := hF0; exact ⟨a, hFsub' haF, ha⟩
    · obtain ⟨a, haF, ha⟩ := hF1; exact ⟨a, hFsub' haF, ha⟩
    · obtain ⟨a, haF, ha⟩ := hF2; exact ⟨a, hFsub' haF, ha⟩
    · intro v hvY hv2
      by_cases hvy : v = y
      · exact ⟨by₀, hFsub' hby₀F, by rw [hvy]; exact hby₀⟩
      · have hvY0 : v ∈ Y \ {y} := ⟨hvY, by simpa using hvy⟩
        by_cases hcf : c = f
        · refine ⟨d, ⟨hdA, ?_⟩, (hdY v hvY0).symm⟩
          simp only [Set.mem_singleton_iff]
          intro h
          exact hcd (hcf.trans h.symm)
        · exact ⟨c, ⟨hcA, by simpa using hcf⟩, (hcY v hvY0).symm⟩
    · exact ⟨by₀, hFsub' hby₀F, hby₀⟩
  -- *"This contradicts the minimality of `A`"*
  have hle := hAmin _ hgood
  have hdc : (A \ {f}).ncard = A.ncard - 1 := Set.ncard_diff_singleton_of_mem hfA
  have hpos : 0 < A.ncard := (Set.ncard_pos (Set.toFinite A)).mpr ⟨f, hfA⟩
  omega

end Workspace.ProofLemmas.Thm192Claim3
