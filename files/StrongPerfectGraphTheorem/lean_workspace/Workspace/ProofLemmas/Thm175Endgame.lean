import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm175Claims
import Workspace.Statements.S17.Thm_17_3
import Workspace.ProofLemmas.Thm175FinalMiss
import Workspace.ProofLemmas.Thm175FinalConfiguration

/-!
# The closing application of 17.3 in the proof of 17.5

The last paragraph of the paper constructs a connected set `F` and an
anticonnected set `T`, then applies 17.3 to the path
`x₂-z-x₁-p_h`.  The small structure below records exactly the hypotheses of
that application and the neighbour property that contradicts its conclusion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm175Minimal
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claims

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The data used in the final invocation of 17.3.  The letters match the
statement of 17.3.  The last field says that every vertex in `T` does have a
neighbour in `F \ {a}`, which will contradict the vertex returned by 17.3. -/
structure FinalSetup (G : SimpleGraph V) where
  F : Set V
  T : Set V
  a₀ : V
  b₀ : V
  a : V
  b : V
  hFT : Disjoint F T
  hF : ConnectedSet G F
  hT : AnticonnectedSet G T
  ha₀ : a₀ ∉ F ∪ T
  hb₀ : b₀ ∉ F ∪ T
  ha : a ∈ F
  hb : b ∈ F
  hpath : IsPathList G [a, a₀, b₀, b]
  ha₀T : VertexComplete G a₀ T
  hb₀T : VertexComplete G b₀ T
  haT : ¬ VertexComplete G a T
  hbT : ¬ VertexComplete G b T
  ha₀F : {f ∈ F | G.Adj a₀ f} = {a}
  hb₀F : {f ∈ F | G.Adj b₀ f} = {b}
  hFa : ConnectedSet G (F \ {a})
  hhit : ∀ y ∈ T, ∃ f ∈ F \ {a}, G.Adj y f

/-- The final paragraph after claim (5), packaged up to the application of
17.3.

PAPER: *"The set `F={x₂,p_h,…,p_n}` is connected; the only neighbour of
`x₁` in `F` is `p_h`; the only neighbour of `z` in `F` is `x₂`. Since
`x₁,z` are `(X\{x₁,x₂})∪Y`-complete, and `p_h,x₂` are not, it follows from
17.2 that there is a vertex in `(X\{x₁,x₂})∪Y` with no neighbour in `F`
except possibly `x₂`. But every vertex in `(X\{x₁,x₂})∪Y` is adjacent to
either `p_j` or to `p_n`, a contradiction."*

The formal closing below uses 17.3, whose asymmetric conclusion is exactly
the "except possibly `x₂`" form needed here. -/
theorem final_setup
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁))
    (hclaim2 : Claim2Conclusion c)
    (blocks : AntipathBlocks G c.X c.Y)
    (firstMiss : FirstMissContext c.core.p₁ blocks)
    (h4 : Claim4Conclusion c blocks firstMiss)
    (last : LastNeighborContext c blocks)
    (h5 : 0 < last.h) :
    Nonempty (FinalSetup G) := by
  classical
  obtain ⟨j, hj, hjh, hjW⟩ := Thm175FinalParity.later_complete
    c hopt hfirst blocks firstMiss h4 last h5
  have hjX : VertexComplete G (c.core.p[j]'hj) (c.X \ {blocks.x₁}) :=
    fun v hv => hjW v (Or.inl hv)
  have hmiss := Thm175FinalMiss.second_missed hG c hfirst blocks last h5 j hj hjh hjX
  obtain ⟨x₂, r, hx⟩ := Thm175FinalBlocks.two_first blocks
  have hx₂idx : blocks.qX[1]'blocks.hXlong = x₂ := by simp only [hx, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [hx₂idx] at hmiss
  let ph := c.core.p[last.h]'last.hlt
  let pj := c.core.p[j]'hj
  let T : Set V := {v | v ∈ r ++ blocks.qY}
  let tail : Set V := {v | v ∈ c.core.p.drop last.h}
  let F : Set V := tail ∪ {x₂}
  have hRne : r ++ blocks.qY ≠ [] := by
    intro he
    have hY := blocks.hYlong
    rw [(List.append_eq_nil_iff.mp he).2] at hY
    simp at hY
  obtain ⟨hT, hx₁x₂, hx₁T, hx₂T, hx₁x₂no, hx₁comp, hx₂not⟩ :=
    Thm175FinalConfiguration.head_pair_facts
      (by simpa only [hx, List.cons_append] using blocks.hanti.1) hRne
  have hx₁X : blocks.x₁ ∈ c.X :=
    (blocks.hXverts _).mp (PathBasics.head_mem blocks.hxhead)
  have hx₂X : x₂ ∈ c.X := (blocks.hXverts _).mp (by simp [hx])
  have hTsub : T ⊆ c.X ∪ c.Y := by
    intro v hv
    rcases List.mem_append.mp hv with hvr | hvY
    · exact Or.inl ((blocks.hXverts _).mp (by simp [hx, hvr]))
    · exact Or.inr ((blocks.hYverts _).mp hvY)
  have hYsub : c.Y ⊆ T := fun v hv =>
    List.mem_append_right _ ((blocks.hYverts v).mpr hv)
  have htailP : ∀ v ∈ tail, v ∈ c.core.p := fun v hv => List.drop_subset _ _ hv
  have hx₁P : blocks.x₁ ∉ c.core.p := fun hv => c.core.houtX _ hv hx₁X
  have hx₂P : x₂ ∉ c.core.p := fun hv => c.core.houtX _ hv hx₂X
  have hphP : ph ∈ c.core.p := List.getElem_mem _
  have hpjP : pj ∈ c.core.p := List.getElem_mem _
  have hphTail : ph ∈ tail :=
    (Thm175FinalBlocks.mem_drop_iff _ _ _).mpr ⟨last.h, last.hlt, le_rfl, rfl⟩
  have hpjTail : pj ∈ tail :=
    (Thm175FinalBlocks.mem_drop_iff _ _ _).mpr ⟨j, hj, by omega, rfl⟩
  have hpnP : c.core.pₙ ∈ c.core.p := PathBasics.getLast_mem c.core.hp.2.2
  have hpLast := PathBasics.getElem_last_of_getLast? c.core.hp.2.2
    (PathBasics.path_length_pos c.core.hp.1)
  have hpnTail : c.core.pₙ ∈ tail :=
    (Thm175FinalBlocks.mem_drop_iff _ _ _).mpr
      ⟨c.core.p.length - 1, by omega, by omega, hpLast⟩
  have hphnepn : ph ≠ c.core.pₙ := by
    intro he
    have hidx := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hpLast.symm)
    omega
  have hphnot : ¬ VertexComplete G ph T := by
    intro hc
    exact hphnepn ((c.core.hYuniq ph hphP).mp (fun v hv => hc v (hYsub hv)))
  have htailconn : ConnectedSet G tail :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isChain
      ((InducedPathExtraction.isChain_of_isPathList c.core.hp.1).drop _)
  have hx₂pj : G.Adj x₂ pj := (hjX x₂ ⟨hx₂X, hx₁x₂.symm⟩).symm
  have hFconn : ConnectedSet G F :=
    ConnectedSetUnionAttach.connectedSet_union_singleton htailconn ⟨pj, hpjTail, hx₂pj⟩
  have hdiff : F \ {x₂} = tail := by
    ext v
    constructor
    · rintro ⟨hv | hv, hne⟩
      · exact hv
      · exact (hne hv).elim
    · intro hv
      exact ⟨Or.inl hv, fun he => hx₂P (he ▸ htailP v hv)⟩
  have hFT : Disjoint F T := by
    apply Set.disjoint_left.mpr
    rintro v (hv | hv) hvT
    · rcases hTsub hvT with hvX | hvY
      · exact c.core.houtX v (htailP v hv) hvX
      · exact c.core.houtY v (htailP v hv) hvY
    · exact hx₂T (hv ▸ hvT)
  have hznotF : z ∉ F := by
    rintro (hz | hz)
    · exact c.core.hzP (htailP z hz)
    · exact c.hz (Or.inl (hz ▸ hx₂X))
  have hznotT : z ∉ T := fun hz => c.hz (hTsub hz)
  have hx₁notF : blocks.x₁ ∉ F := by
    rintro (hv | hv)
    · exact hx₁P (htailP _ hv)
    · exact hx₁x₂ hv
  have hzx₁ : G.Adj z blocks.x₁ := c.hzXY _ (Or.inl hx₁X)
  have hzx₂ : G.Adj z x₂ := c.hzXY _ (Or.inl hx₂X)
  have hzph : ¬ G.Adj z ph := c.core.hzanti ph hphP
  have hphx₂ : ph ≠ x₂ := fun he => hx₂P (he ▸ hphP)
  have hpath : IsPathList G [x₂, z, blocks.x₁, ph] := by
    apply PathGlue.isPathList_four
    · have hzneph : z ≠ ph := fun he => c.core.hzP
        (List.mem_iff_getElem.mpr ⟨last.h, last.hlt, he.symm⟩)
      have hxph : blocks.x₁ ≠ ph := last.hadj.ne
      simp [hzx₂.ne.symm, hx₁x₂.symm, hphx₂.symm, hzx₁.ne, hzneph, hxph]
    · exact hzx₂.symm
    · exact hzx₁
    · exact last.hadj
    · exact fun ha => hx₁x₂no ha.symm
    · exact fun ha => hmiss ha.symm
    · exact hzph
  have hzF : {f ∈ F | G.Adj z f} = {x₂} := by
    ext f
    constructor
    · rintro ⟨hf | hf, ha⟩
      · exact (c.core.hzanti f (htailP f hf) ha).elim
      · exact hf
    · intro hf
      have he : f = x₂ := hf
      subst f
      exact ⟨Or.inr rfl, hzx₂⟩
  have hx₁F : {f ∈ F | G.Adj blocks.x₁ f} = {ph} := by
    ext f
    constructor
    · rintro ⟨hf | hf, ha⟩
      · obtain ⟨i, hi, hhi, he⟩ := (Thm175FinalBlocks.mem_drop_iff _ _ _).mp hf
        have hle := last.hmax i hi (he ▸ ha)
        have hie : i = last.h := by omega
        subst i
        exact he.symm
      · have he : f = x₂ := hf
        exact (hx₁x₂no (he ▸ ha)).elim
    · intro hf
      have he : f = ph := hf
      subst f
      exact ⟨Or.inl hphTail, last.hadj⟩
  have hhit : ∀ y ∈ T, ∃ f ∈ F \ {x₂}, G.Adj y f := by
    intro y hy
    rw [hdiff]
    rcases List.mem_append.mp hy with hyr | hyY
    · have hyX : y ∈ c.X := (blocks.hXverts _).mp (by simp [hx, hyr])
      have hynex : y ≠ blocks.x₁ := fun he => hx₁T (he ▸ List.mem_append_left blocks.qY hyr)
      exact ⟨pj, hpjTail, (hjX y ⟨hyX, hynex⟩).symm⟩
    · have hyY' := (blocks.hYverts y).mp hyY
      exact ⟨c.core.pₙ, hpnTail, ((c.core.hYuniq _ hpnP).mpr rfl y hyY').symm⟩
  exact ⟨{
    F := F
    T := T
    a₀ := z
    b₀ := blocks.x₁
    a := x₂
    b := ph
    hFT := hFT
    hF := hFconn
    hT := hT
    ha₀ := fun h => h.elim hznotF hznotT
    hb₀ := fun h => h.elim hx₁notF hx₁T
    ha := Or.inr rfl
    hb := Or.inl hphTail
    hpath := hpath
    ha₀T := fun v hv => c.hzXY v (hTsub hv)
    hb₀T := hx₁comp
    haT := hx₂not
    hbT := hphnot
    ha₀F := hzF
    hb₀F := hx₁F
    hFa := hdiff.symm ▸ htailconn
    hhit := hhit }⟩

/-- Once the last paragraph has supplied `FinalSetup`, 17.3 gives the desired
contradiction. -/
theorem finalSetup_absurd
    (G : SimpleGraph V) (hG : InF7 G) (s : FinalSetup G) : False := by
  obtain ⟨y, hyT, hyanti⟩ :=
    _root_.Workspace.Statements.S17.SPGT.thm_17_3
      G hG s.F s.T s.hFT s.hF s.hT
      s.a₀ s.b₀ s.a s.b s.ha₀ s.hb₀ s.ha s.hb s.hpath
      s.ha₀T s.hb₀T s.haT s.hbT s.ha₀F s.hb₀F s.hFa
  obtain ⟨f, hf, hyf⟩ := s.hhit y hyT
  exact (hyanti f hf) hyf

/-- An optimal counterexample is impossible.  This follows by invoking the
numbered claims in their printed order and then applying 17.3. -/
theorem optimal_counterexample_absurd
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c) : False := by
  have hfirst := first_unique_of_optimal G hG z c hopt
  have h2 := claim2 G hG z c hopt hfirst
  obtain ⟨blocks⟩ := claim3 G hG z c hopt hfirst h2
  obtain ⟨firstMiss⟩ := exists_first_miss G c blocks
  have h4 := claim4 G hG z c hopt hfirst blocks firstMiss
  obtain ⟨last⟩ := exists_last_neighbor G c blocks
  have h5 := claim5 G hG z c hopt hfirst blocks firstMiss h4 last
  obtain ⟨s⟩ := final_setup G hG z c hopt hfirst h2 blocks firstMiss h4 last h5
  exact finalSetup_absurd G hG s

end Workspace.ProofLemmas.Thm175Endgame
