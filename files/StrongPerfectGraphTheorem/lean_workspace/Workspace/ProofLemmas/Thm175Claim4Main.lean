import Workspace.ProofLemmas.Thm175Claim4Parity
import Workspace.ProofLemmas.Thm175Claim4Bridge
import Workspace.ProofLemmas.Thm175Claim4FirstMiss
import Workspace.ProofLemmas.Thm175Claim4Selection
import Workspace.ProofLemmas.Thm175Claim4Closing

/-! Assembly of the printed proof of claim (4) of 17.5. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Main

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- PAPER: "For every subpath `P'` of `P`, if the ends of `P'` are adjacent
to `x₁`, then there are an even number of `W`-complete edges in `P'`." -/
theorem main (hG : InF7 G) (s : Setup c) (hopt : IsOptimal c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁)) :
    ∀ a d (had : a < d) (hd : d < c.core.p.length),
      G.Adj s.x₁ (c.core.p[a]'(lt_trans had hd)) →
      G.Adj s.x₁ (c.core.p[d]'hd) →
      Even (edges G (wSet s) ((c.core.p.drop a).take (d - a + 1))).ncard := by
  apply Thm175Claim4Parity.parity_of_intervals_without_internal_neighbor
    G (wSet s) c.core.p c.core.hp.1 s.x₁
  intro a d had hd hxa hxd hno
  by_contra hneven
  have ho := Nat.not_even_iff_odd.mp hneven
  obtain ⟨heven, i, hi, hai, hijd, hiW, hjW, hlocal⟩ :=
    Thm175Claim4Exceptional.two_consecutive hG s hfirst a d had hd hxa hxd hno ho
  obtain ⟨h1, hp₂W, hbound⟩ := Thm175Claim4Bridge.restricted_complete_vertices
    hG s hfirst a d had hd hxa hxd hno heven i hi hai hijd hiW hjW hlocal
  have ht0 := Thm175Claim4FirstMiss.first_miss_zero hG s hfirst
  obtain ⟨u, v, huP, hvP, hune, hvne, huv, huW, hvV⟩ :=
    Thm175Claim4Selection.adjacent_completions hG s hopt hfirst ht0 h1 hp₂W hbound
  exact Thm175Claim4Closing.adjacent_complete_contradiction hG s hfirst ht0 h1 hp₂W
    u v huP hvP hune hvne huv huW hvV

end Workspace.ProofLemmas.Thm175Claim4Main
