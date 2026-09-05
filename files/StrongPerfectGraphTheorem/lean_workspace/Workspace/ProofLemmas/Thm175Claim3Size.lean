import Workspace.ProofLemmas.Thm175Optimal
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.AnticompleteUnionComponents
import Workspace.Statements.S13.Thm_13_6

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim3Size

open Workspace.Types.Core.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas Workspace.ProofLemmas.Thm175Optimal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "For if `|X| = 1`, `X = {x}` say, then
`z-x-p₁-⋯-pₙ` is an odd path of length at least 5 between `Y`-complete
vertices, and none of its internal vertices are `Y`-complete, contrary to
13.6. So `|X| ≥ 2`." The empty case is excluded by claim (1). -/
theorem not_subsingleton (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z)
    (hfirst : ∀ w ∈ c.core.p, (VertexComplete G w c.X ↔ w = c.core.p₁)) :
    ¬ c.X.Subsingleton := by
  classical
  have hp₁ := PathBasics.head_mem c.core.hp.2.1
  have hpₙ := PathBasics.getLast_mem c.core.hp.2.2
  have hends : c.core.p₁ ≠ c.core.pₙ :=
    PathBasics.isPathFrom_ends_ne c.core.hp (Nat.le_of_lt c.core.hlong)
  have hpₙY : VertexComplete G c.core.pₙ c.Y := (c.core.hYuniq _ hpₙ).mpr rfl
  have hXne : c.X.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hcX : VertexComplete G c.core.pₙ c.X := by simp [he, VertexComplete]
    exact hends ((hfirst _ hpₙ).mp hcX).symm
  have hYne : c.Y.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hcY : VertexComplete G c.core.p₁ c.Y := by simp [he, VertexComplete]
    exact hends ((c.core.hYuniq _ hp₁).mp hcY)
  intro hsmall
  obtain ⟨x, hxX⟩ := hXne
  have hXeq : c.X = {x} := Set.eq_singleton_iff_unique_mem.mpr
    ⟨hxX, fun v hv => hsmall hv hxX⟩
  have hxY : x ∉ c.Y := by
    intro hx
    have hpₙX : VertexComplete G c.core.pₙ c.X := by
      intro v hv
      have hvx := hsmall hv hxX
      simpa [hvx] using hpₙY x hx
    exact hends ((hfirst _ hpₙ).mp hpₙX).symm
  have hd : Disjoint c.X c.Y := by
    rw [hXeq, Set.disjoint_singleton_left]
    exact hxY
  have hxnot : ¬ VertexComplete G x c.Y := by
    intro hxcomp
    have hanti : Anticomplete Gᶜ c.X c.Y := by
      intro v hv w hw hadj
      have hvx := hsmall hv hxX
      have hn := ((SimpleGraph.compl_adj G v w).mp hadj).2
      apply hn
      simpa [hvx] using hxcomp w hw
    exact (Workspace.Types.AnticompleteUnionComponents.anticompleteUnionComponents
      Gᶜ c.X c.Y hd ⟨x, hxX⟩ hYne hanti).1 c.hXYa
  have hxp : x ∉ c.core.p := fun h => c.core.houtX x h hxX
  have hxp₁ : G.Adj x c.core.p₁ := (c.core.hp₁X x hxX).symm
  have hother : ∀ w ∈ c.core.p, w ≠ c.core.p₁ → ¬ G.Adj x w := by
    intro w hw hne hadj
    apply hne
    apply (hfirst w hw).mp
    intro v hv
    have hvx := hsmall hv hxX
    simpa [hvx] using hadj.symm
  have hxpPath := PathAttach.isPathFrom_cons c.core.hp hxp₁ hxp hother
  have hzx : G.Adj z x := c.hzXY x (Or.inl hxX)
  have hzp : z ∉ x :: c.core.p := by
    simp only [List.mem_cons, not_or]
    exact ⟨hzx.ne, c.core.hzP⟩
  have hzother : ∀ w ∈ x :: c.core.p, w ≠ x → ¬ G.Adj z w := by
    intro w hw hne
    rcases List.mem_cons.mp hw with he | hw
    · exact (hne he).elim
    · exact c.core.hzanti w hw
  have hpath := PathAttach.isPathFrom_cons hxpPath hzx hzp hzother
  have hlen : pathLength (z :: x :: c.core.p) = pathLength c.core.p + 2 := by
    have hpos := PathBasics.path_length_pos c.core.hp.1
    simp only [pathLength, List.length_cons]
    omega
  have hodd : Odd (pathLength (z :: x :: c.core.p)) := by
    rw [hlen]
    exact c.core.hodd.add_even (by decide)
  have hout : c.Y ⊆ {w | w ∈ z :: x :: c.core.p}ᶜ := by
    intro w hw hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact c.hz (Or.inr hw)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hxY hw
    · exact c.core.houtY w hmem hw
  have hcomplete : ∀ w ∈ z :: x :: c.core.p,
      VertexComplete G w c.Y → w = z ∨ w = c.core.pₙ := by
    intro w hw hc
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl rfl
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (hxnot hc).elim
    · exact Or.inr ((c.core.hYuniq w hw).mp hc)
  rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1
      (z :: x :: c.core.p) z c.core.pₙ hpath hodd c.Y hout c.hYa
      (fun w hw => c.hzXY w (Or.inr hw)) hpₙY with he | he
  · obtain ⟨u, hu, v, hv, hadj, huc, hvc⟩ := he
    rcases hcomplete u hu huc with rfl | rfl <;>
      rcases hcomplete v hv hvc with rfl | rfl
    · exact G.irrefl hadj
    · exact c.core.hzanti _ hpₙ hadj
    · exact c.core.hzanti _ hpₙ hadj.symm
    · exact G.irrefl hadj
  · have hlong := c.core.hlong
    omega

end Workspace.ProofLemmas.Thm175Claim3Size
