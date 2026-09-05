import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.Thm58NoEvenTrackThroughAttachments
import Workspace.ProofLemmas.Thm84AdjacentChoices
import Workspace.ProofLemmas.Thm84ForkCountForcesK4
import Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath
import Workspace.ProofLemmas.Thm84K4CaseShortAttachment
import Workspace.ProofLemmas.Thm84K4CaseDegenerate
import Workspace.Statements.S05.Thm_5_7
import Workspace.Statements.S08.Thm_8_3

/-!
# 8.4: reduction of the `K₄` case to alternative 5 of 5.7

The printed proof applies 5.7 a second time after it has labelled the four vertices of `J`.
The only fact needed for that application is that the two unchanged vertices still fork.  This
file proves that reduction without choosing labels for the four vertices.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84K4CaseReduction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two outcomes retained by the `K₄` branch of 8.4. -/
def Outcome {U : Type*} [Fintype U] (G : SimpleGraph V) (J : SimpleGraph U) : Prop :=
  (∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
    ∃ (k : ℕ) (H'' : SimpleGraph (Fin k)) (K'' : Set V),
      IsAppearance G J' H'' K'' ∧ NondegenerateAppearance J' H'') ∨
  (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧
    ∃ (k : ℕ) (H'' : SimpleGraph (Fin k)) (K'' : Set V)
      (ψ : H''.lineGraph ≃g G.induce K''),
      IsAppearance G J H'' K'' ∧ IsOvershadowedAppearance G H'' K'' ψ)

/-- Every vertex forks when the chosen line graph is saturated. -/
theorem all_fork_of_saturates {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (X : Set V)
    (hSat : SaturatesLineGraph H
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(phi ⟨e, he⟩) : V) ∈ X}) :
    ∀ u : U, Thm84ForkCountForcesK4.ForkAt J R X u := by
  classical
  have hfam :=
    (Thm84AdjacentChoices.saturates_iff G J hJ S N hSN H R hForms phi X).mp hSat
  intro u
  obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ :=
    Thm84ForkCountForcesK4.exists_three_neighbours J hJ u
  have bad_eq : ∀ v v' : U, J.Adj u v → J.Adj u v' →
      ¬ (∃ s : V, (R u v).head? = some s ∧ s ∈ X) →
      ¬ (∃ s : V, (R u v').head? = some s ∧ s ∈ X) → v = v' := by
    intro v v' huv huv' hv hv'
    refine hfam u v v' huv huv' ?_ ?_
    · intro s hs hsX
      exact hv ⟨s, hs, hsX⟩
    · intro s hs hsX
      exact hv' ⟨s, hs, hsX⟩
  by_cases g₁ : ∃ s : V, (R u v₁).head? = some s ∧ s ∈ X
  · by_cases g₂ : ∃ s : V, (R u v₂).head? = some s ∧ s ∈ X
    · exact ⟨v₁, v₂, h₁, h₂, h₁₂, g₁, g₂⟩
    · by_cases g₃ : ∃ s : V, (R u v₃).head? = some s ∧ s ∈ X
      · exact ⟨v₁, v₃, h₁, h₃, h₁₃, g₁, g₃⟩
      · exact absurd (bad_eq v₂ v₃ h₂ h₃ g₂ g₃) h₂₃
  · by_cases g₂ : ∃ s : V, (R u v₂).head? = some s ∧ s ∈ X
    · by_cases g₃ : ∃ s : V, (R u v₃).head? = some s ∧ s ∈ X
      · exact ⟨v₂, v₃, h₂, h₃, h₂₃, g₂, g₃⟩
      · exact absurd (bad_eq v₁ v₃ h₁ h₃ g₁ g₃) h₁₃
    · exact absurd (bad_eq v₁ v₂ h₁ h₂ g₁ g₂) h₁₂

/-- Forking is unchanged at a vertex not incident with the replaced edge. -/
theorem fork_iff_of_agree_off_edge {U : Type*}
    (J : SimpleGraph U) (R R' : U → U → List V) (X : Set V)
    (a b u : U) (hua : u ≠ a) (hub : u ≠ b)
    (hdiff : ∀ x z : U, J.Adj x z → s(x, z) ≠ s(a, b) → R x z = R' x z) :
    Thm84ForkCountForcesK4.ForkAt J R X u ↔
      Thm84ForkCountForcesK4.ForkAt J R' X u := by
  have hRR : ∀ v : U, J.Adj u v → R u v = R' u v := by
    intro v huv
    refine hdiff u v huv ?_
    intro hcon
    rcases Sym2.eq_iff.mp hcon with ⟨h, -⟩ | ⟨h, -⟩
    · exact hua h
    · exact hub h
  constructor
  · rintro ⟨v, v', hv, hv', hvv', hg, hg'⟩
    exact ⟨v, v', hv, hv', hvv', by rwa [← hRR v hv], by rwa [← hRR v' hv']⟩
  · rintro ⟨v, v', hv, hv', hvv', hg, hg'⟩
    exact ⟨v, v', hv, hv', hvv', by rwa [hRR v hv], by rwa [hRR v' hv']⟩

/-- In a four-element type, the complement of two distinct vertices has two elements. -/
theorem ncard_compl_pair_eq_two {U : Type*} [Fintype U] [DecidableEq U]
    (hcard : Fintype.card U = 4) {a b : U} (hab : a ≠ b) :
    (({a, b} : Set U)ᶜ).ncard = 2 := by
  rw [Set.ncard_compl]
  have hp : ({a, b} : Set U).ncard = 2 := Set.ncard_pair hab
  rw [hp, Nat.card_eq_fintype_card, hcard]

/-- Alternative 6 of 5.7 already gives one of the two required outcomes. -/
theorem outcome_of_five_seven_six {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnd : NondegenerateStripSystem G J S N)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (phi' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms' : FormsLineGraph G J S N R' H')
    (h576 : ∃ c₁ c₂ : Fin n', DifferentBiparity H' c₁ c₂ ∧
      (¬ ∃ q : List (Fin n'), IsBranch H' q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
      {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
        (↑(phi' ⟨e, he⟩) : V) ∈ X} = incidentEdges H' c₁ ∪ incidentEdges H' c₂) :
    Outcome G J := by
  classical
  let K' : Set V :=
    ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}
  by_cases hnondeg : NondegenerateAppearance J H'
  · left
    obtain ⟨c₁, c₂, -, hnb, hXeq⟩ := h576
    refine EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath
      G hG J hJ n' H' K' hForms'.2 phi'
      (fun c => {x : V | ∃ (e : Sym2 (Fin n')) (he : e ∈ H'.edgeSet),
        e ∈ incidentEdges H' c ∧ x = (↑(phi' ⟨e, he⟩) : V)})
      (fun _ => rfl) [y] y y ?_ ?_ c₁ c₂ hnb ?_ ?_ ?_ (fun _ => hnondeg)
    · refine ⟨⟨by simp, by simp, ?_⟩, rfl, rfl⟩
      intro i j hi hj
      simp only [List.length_singleton] at hi hj
      have hii : i = 0 := by omega
      have hjj : j = 0 := by omega
      subst hii
      subst hjj
      exact iff_of_false G.irrefl (by omega)
    · intro z hz hzK
      have hzy : z = y := by simpa only [List.mem_singleton] using hz
      subst z
      apply hy
      simp only [stripSystemVertices, Set.mem_iUnion]
      simp only [K', Set.mem_iUnion, Set.mem_setOf_eq] at hzK
      obtain ⟨u, v, huv, hyR⟩ := hzK
      obtain ⟨-, -, -, -, hsub, -, -⟩ := hForms'.1 u v huv
      exact ⟨u, v, huv, hsub y hyR⟩
    · rintro z ⟨e, he, hec, rfl⟩
      have hemem : e ∈ {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
          (↑(phi' ⟨e, he⟩) : V) ∈ X} := by
        rw [hXeq]
        exact Or.inl hec
      obtain ⟨he', hzX⟩ := hemem
      rw [hX] at hzX
      exact hzX
    · rintro z ⟨e, he, hec, rfl⟩
      have hemem : e ∈ {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
          (↑(phi' ⟨e, he⟩) : V) ∈ X} := by
        rw [hXeq]
        exact Or.inr hec
      obtain ⟨he', hzX⟩ := hemem
      rw [hX] at hzX
      exact hzX
    · intro z hz w hw hzw
      simp only [List.mem_singleton] at hz
      subst hz
      have hwX : (↑(phi' (phi'.symm ⟨w, hw⟩)) : V) ∈ X := by
        rw [phi'.apply_symm_apply, hX]
        exact hzw
      have heX : ((phi'.symm ⟨w, hw⟩ : H'.edgeSet) : Sym2 (Fin n')) ∈
          {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
            (↑(phi' ⟨e, he⟩) : V) ∈ X} :=
        ⟨(phi'.symm ⟨w, hw⟩).2, hwX⟩
      rw [hXeq] at heX
      have hval : (↑(phi' (phi'.symm ⟨w, hw⟩)) : V) = w := by
        rw [phi'.apply_symm_apply]
      rcases heX with heX | heX
      · exact Or.inl ⟨rfl, ⟨_, (phi'.symm ⟨w, hw⟩).2, heX, hval.symm⟩⟩
      · exact Or.inr ⟨rfl, ⟨_, (phi'.symm ⟨w, hw⟩).2, heX, hval.symm⟩⟩
  · right
    refine ⟨hK4, ?_⟩
    by_contra hno
    exact hnondeg
      (_root_.Workspace.Statements.S08.SPGT.thm_8_3 G hG J hJ S N hSN hnd hno
        n' H' R' hForms')

/-- An edge of a track that contains its first end is its first edge.  In particular, the
track edges incident with that end form a subsingleton set. -/
theorem incident_trackEdges_subsingleton_at_head {W : Type*} {H : SimpleGraph W}
    {q : List W} {b₁ b₂ : W} (hq : IsTrackFrom H q b₁ b₂) (hqlen : 2 ≤ q.length) :
    (incidentEdges H b₁ ∩ trackEdges q).Subsingleton := by
  intro e he f hf
  have eeq := ThreeTracksLineGraphPrism.edge_eq_firstTrackEdge hq hqlen he.2 he.1.2
  have feq := ThreeTracksLineGraphPrism.edge_eq_firstTrackEdge hq hqlen hf.2 hf.1.2
  exact eeq.trans feq.symm

/-- The analogous fact at the last end of a track. -/
theorem incident_trackEdges_subsingleton_at_last {W : Type*} {H : SimpleGraph W}
    {q : List W} {b₁ b₂ : W} (hq : IsTrackFrom H q b₁ b₂) (hqlen : 2 ≤ q.length) :
    (incidentEdges H b₂ ∩ trackEdges q).Subsingleton := by
  intro e he f hf
  have eeq := ThreeTracksLineGraphPrism.edge_eq_lastTrackEdge hq hqlen he.2 he.1.2
  have feq := ThreeTracksLineGraphPrism.edge_eq_lastTrackEdge hq hqlen hf.2 hf.1.2
  exact eeq.trans feq.symm

/-- The alternative-5 branch itself is an overshadowing branch as soon as it has length at
least three.  The equality in 5.7.5 says that every incident edge outside the branch belongs
to `X`; hence at either end only the single end-edge of the branch may miss `X`. -/
theorem outcome_of_long_five_seven_five {U : Type*} [Fintype U]
    {S : U → U → Set V} {N : U → Set V} {y : V}
    (G : SimpleGraph V) (J : SimpleGraph U)
    (X : Set V) (hX : X = G.neighborSet y)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (phi' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms' : FormsLineGraph G J S N R' H')
    (q : List (Fin n')) (b₁ b₂ : Fin n')
    (hq : IsBranch H' q) (hqends : IsTrackFrom H' q b₁ b₂)
    (hqodd : Odd (trackLength q)) (hqlong : 3 ≤ trackLength q)
    (hEq : {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
        (↑(phi' ⟨e, he⟩) : V) ∈ X} \ trackEdges q =
      (incidentEdges H' b₁ ∪ incidentEdges H' b₂) \ trackEdges q) :
    Outcome G J := by
  classical
  right
  refine ⟨hK4, n', H', _, phi', hForms'.2, q, b₁, b₂, hq, hqends, hqodd, hqlong,
    y, ?_, ?_⟩
  · refine Set.Subsingleton.anti (incident_trackEdges_subsingleton_at_head hqends ?_) ?_
    · simp only [trackLength] at hqlong
      omega
    · rintro e ⟨heinc, heno⟩
      refine ⟨heinc, ?_⟩
      by_contra hnotrack
      have hrhs : e ∈ (incidentEdges H' b₁ ∪ incidentEdges H' b₂) \ trackEdges q :=
        ⟨Or.inl heinc, hnotrack⟩
      have hlhs : e ∈ {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
          (↑(phi' ⟨e, he⟩) : V) ∈ X} \ trackEdges q := by
        rw [hEq]
        exact hrhs
      obtain ⟨he, heX⟩ := hlhs.1
      apply heno
      refine ⟨he, ?_⟩
      rw [hX] at heX
      exact heX
  · refine Set.Subsingleton.anti (incident_trackEdges_subsingleton_at_last hqends ?_) ?_
    · simp only [trackLength] at hqlong
      omega
    · rintro e ⟨heinc, heno⟩
      refine ⟨heinc, ?_⟩
      by_contra hnotrack
      have hrhs : e ∈ (incidentEdges H' b₁ ∪ incidentEdges H' b₂) \ trackEdges q :=
        ⟨Or.inr heinc, hnotrack⟩
      have hlhs : e ∈ {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
          (↑(phi' ⟨e, he⟩) : V) ∈ X} \ trackEdges q := by
        rw [hEq]
        exact hrhs
      obtain ⟨he, heX⟩ := hlhs.1
      apply heno
      refine ⟨he, ?_⟩
      rw [hX] at heX
      exact heX

/--
PAPER (printed pp. 41--42), the graph-theoretic core of the zero-rung subcase.  After the
alternative-5 branch has one edge, the displayed odd-hole and triangle-linking arguments show
that either the changed strip has a zero rung and a positive rung, or the original `K₄`
subdivision contains a four-cycle through all four branch vertices.  These are exactly the two
alternatives below.
-/
theorem short_branch_forces_mixed_or_degenerate {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (a b : U) (hab : J.Adj a b)
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (phi' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms : FormsLineGraph G J S N R H)
    (hsym : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (hForms' : FormsLineGraph G J S N R' H')
    (hsym' : ∀ u v : U, J.Adj u v → R' v u = (R' u v).reverse)
    (hSat : SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(phi ⟨e, he⟩) : V) ∈ X})
    (hdiff : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v)
    (q : List (Fin n')) (b₁ b₂ : Fin n')
    (hq : IsBranch H' q) (hqends : IsTrackFrom H' q b₁ b₂)
    (hqlen : trackLength q = 1)
    (hEq : {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
        (↑(phi' ⟨e, he⟩) : V) ∈ X} \ trackEdges q =
      (incidentEdges H' b₁ ∪ incidentEdges H' b₂) \ trackEdges q) :
    (∃ u v : U, J.Adj u v ∧ pathLength (R' u v) = 0 ∧ 1 ≤ pathLength (R u v)) ∨
      DegenerateAppearance J H := by
  classical
  have hcard : Fintype.card U = 4 := by
    obtain ⟨e⟩ := hK4
    simpa using Fintype.card_congr e.toEquiv
  have hcomplete : ∀ u v : U, u ≠ v → J.Adj u v := by
    obtain ⟨e⟩ := hK4
    intro u v huv
    apply e.map_rel_iff.mp
    exact fun he => huv (e.injective he)
  obtain ⟨c, d, hcdne, hcomp⟩ :=
    Set.ncard_eq_two.mp (ncard_compl_pair_eq_two hcard hab.ne)
  have hc : c ≠ a ∧ c ≠ b := by
    have hc : c ∈ ({a, b} : Set U)ᶜ := by rw [hcomp]; simp
    simpa using hc
  have hd : d ≠ a ∧ d ≠ b := by
    have hd : d ∈ ({a, b} : Set U)ᶜ := by rw [hcomp]; simp
    simpa using hd
  have hac := hcomplete a c hc.1.symm
  have had := hcomplete a d hd.1.symm
  have hbc := hcomplete b c hc.2.symm
  have hbd := hcomplete b d hd.2.symm
  have hcd := hcomplete c d hcdne
  have hcover : ∀ u : U, u = a ∨ u = b ∨ u = c ∨ u = d := by
    intro u
    by_cases hua : u = a
    · exact Or.inl hua
    by_cases hub : u = b
    · exact Or.inr (Or.inl hub)
    have hu : u ∈ ({a, b} : Set U)ᶜ := by simp [hua, hub]
    rw [hcomp] at hu
    exact Or.inr (Or.inr hu)
  obtain ⟨r, hr⟩ := Thm84K4CaseRungs.exists_ends y hForms.1 hsym
  obtain ⟨r', hr'⟩ := Thm84K4CaseRungs.exists_ends y hForms'.1 hsym'
  have hall := all_fork_of_saturates G J hJ S N hSN H R hForms phi X hSat
  have hfc := (fork_iff_of_agree_off_edge J R R' X a b c hc.1 hc.2 hdiff).mp (hall c)
  have hfd := (fork_iff_of_agree_off_edge J R R' X a b d hd.1 hd.2 hdiff).mp (hall d)
  obtain ⟨hzero, hnone, hclean⟩ := Thm84K4CaseShortAttachment.short_attachment_data
    hJ hSN hForms' hr' hsym' phi' hab hac had hbc hbd hcd hX hfc hfd hqends hqlen hEq
  have hsat : ∀ u v w : U, J.Adj u v → J.Adj u w →
      ¬ G.Adj y (r u v) → ¬ G.Adj y (r u w) → v = w := by
    have hfam := (Thm84AdjacentChoices.saturates_iff G J hJ S N hSN H R hForms phi X).mp hSat
    intro u v w huv huw hv hw
    apply hfam u v w huv huw
    · intro s hs hsX
      have he : s = r u v :=
        Option.some_injective _ (hs.symm.trans (hr.path u v huv).2.1)
      apply hv
      rwa [hX, he] at hsX
    · intro s hs hsX
      have he : s = r u w :=
        Option.some_injective _ (hs.symm.trans (hr.path u w huw).2.1)
      apply hw
      rwa [hX, he] at hsX
  exact Or.inr (Thm84K4CaseDegenerate.degenerate_of_short_attachment hG hJ hSN hForms
    hForms'.1 hsym hsym' hr hr' hK4 hab hac had hbc hbd hcd hcover hdiff hy hsat
    hnone hclean hzero)

/-- The short alternative-5 branch finishes with 8.2 in the mixed-rung case and with 8.3 in
the degenerate case. -/
theorem fiveSevenFive_short_endgame {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateStripSystem G J S N)
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (a b : U) (hab : J.Adj a b)
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (phi' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms : FormsLineGraph G J S N R H)
    (hsym : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (hForms' : FormsLineGraph G J S N R' H')
    (hsym' : ∀ u v : U, J.Adj u v → R' v u = (R' u v).reverse)
    (hSat : SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(phi ⟨e, he⟩) : V) ∈ X})
    (hdiff : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v)
    (q : List (Fin n')) (b₁ b₂ : Fin n')
    (hq : IsBranch H' q) (hqends : IsTrackFrom H' q b₁ b₂)
    (hqlen : trackLength q = 1)
    (hEq : {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
        (↑(phi' ⟨e, he⟩) : V) ∈ X} \ trackEdges q =
      (incidentEdges H' b₁ ∪ incidentEdges H' b₂) \ trackEdges q) :
    Outcome G J := by
  obtain hmixed | hdeg := short_branch_forces_mixed_or_degenerate G hG J hJ S N hSN
    y hy X hX hK4 a b hab n H R phi n' H' R' phi' hForms hsym hForms' hsym'
    hSat hdiff q b₁ b₂ hq hqends hqlen hEq
  · right
    refine ⟨hK4, ?_⟩
    obtain ⟨u, v, huv, hzero, hpos⟩ := hmixed
    exact _root_.Workspace.Statements.S08.SPGT.thm_8_2 G hG J hJ S N hSN
      ⟨u, v, huv, R' u v, R u v, hForms'.1 u v huv, hzero,
        hForms.1 u v huv, hpos⟩
  · right
    refine ⟨hK4, ?_⟩
    by_contra hno
    exact (_root_.Workspace.Statements.S08.SPGT.thm_8_3 G hG J hJ S N hSN
      (hnd hK4) hno n H R hForms) hdeg

/--
PAPER (printed pp. 41--42), from the conclusion of the second 5.7 application:
*"and so there is an edge `ij` of `J` such that `R'_ij` is even and
`(X ∩ V(L(H'))) \ V(R'_ij) = (T'_i ∪ T'_j) \ V(R'_ij)`"*, through
*"Since the strip system is nondegenerate, it follows from 8.3 that there is an overshadowed
appearance of `K₄` in `G`."*

The long-branch case is immediate from the definition of overshadowing.  The one-edge case is
passed to `short_branch_forces_mixed_or_degenerate`.
-/
theorem fiveSevenFive_endgame {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateStripSystem G J S N)
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (a b : U) (hab : J.Adj a b)
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (phi' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms : FormsLineGraph G J S N R H)
    (hsym : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (hForms' : FormsLineGraph G J S N R' H')
    (hsym' : ∀ u v : U, J.Adj u v → R' v u = (R' u v).reverse)
    (hSat : SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(phi ⟨e, he⟩) : V) ∈ X})
    (hdiff : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v)
    (h575 : ∃ (q : List (Fin n')) (b₁ b₂ : Fin n'), IsBranch H' q ∧
      IsTrackFrom H' q b₁ b₂ ∧ Odd (trackLength q) ∧
      {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
        (↑(phi' ⟨e, he⟩) : V) ∈ X} \ trackEdges q =
        (incidentEdges H' b₁ ∪ incidentEdges H' b₂) \ trackEdges q) :
    Outcome G J := by
  obtain ⟨q, b₁, b₂, hq, hqends, hqodd, hEq⟩ := h575
  by_cases hqlong : 3 ≤ trackLength q
  · exact outcome_of_long_five_seven_five G J X hX hK4 n' H' R' phi' hForms'
      q b₁ b₂ hq hqends hqodd hqlong hEq
  · have hqlen : trackLength q = 1 := by
      obtain ⟨k, hk⟩ := hqodd
      omega
    exact fiveSevenFive_short_endgame G hG J hJ S N hSN hnd y hy X hX hK4 a b hab
      n H R phi n' H' R' phi' hForms hsym hForms' hsym' hSat hdiff
      q b₁ b₂ hq hqends hqlen hEq

/-- The `K₄` case is reduced to the geometric tail following alternative 5 of 5.7. -/
theorem reduction {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateStripSystem G J S N)
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (a b : U) (hab : J.Adj a b)
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (phi' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms : FormsLineGraph G J S N R H)
    (hsym : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (hForms' : FormsLineGraph G J S N R' H')
    (hsym' : ∀ u v : U, J.Adj u v → R' v u = (R' u v).reverse)
    (hSat : SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(phi ⟨e, he⟩) : V) ∈ X})
    (hUnsat : ¬ SaturatesLineGraph H'
      {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(phi' ⟨e, he⟩) : V) ∈ X})
    (hdiff : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v) :
    Outcome G J := by
  classical
  let K' : Set V :=
    ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}
  let X' : Set (Sym2 (Fin n')) :=
    {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(phi' ⟨e, he⟩) : V) ∈ X}
  have hyK' : y ∉ K' := by
    intro hyK
    simp only [K', Set.mem_iUnion, Set.mem_setOf_eq] at hyK
    obtain ⟨u, v, huv, hyR⟩ := hyK
    obtain ⟨-, -, -, -, hsub, -, -⟩ := hForms'.1 u v huv
    apply hy
    simp only [stripSystemVertices, Set.mem_iUnion]
    exact ⟨u, v, huv, hsub y hyR⟩
  have hXattach : X' =
      {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet,
        (↑(phi' ⟨e, he⟩) : V) ∈ attachments G {y} K'} := by
    ext e
    simp only [X', Set.mem_setOf_eq]
    constructor
    · rintro ⟨he, heX⟩
      refine ⟨he, ⟨(phi' ⟨e, he⟩).2, y, rfl, ?_⟩⟩
      rw [hX] at heX
      exact heX.symm
    · rintro ⟨he, -, z, hz, hadj⟩
      have hzy : z = y := hz
      subst z
      exact ⟨he, by rw [hX]; exact hadj.symm⟩
  have hnotrack : ¬ ∃ (q : List (Fin n')) (_hq : 5 ≤ q.length),
      IsTrackList H' q ∧ Even (trackLength q) ∧
      s(q[0], q[1]) ∈ X' ∧ s(q[q.length - 2], q[q.length - 1]) ∈ X' ∧
      ∀ e ∈ trackEdges q, e ≠ s(q[0], q[1]) →
        e ≠ s(q[q.length - 2], q[q.length - 1]) → e ∉ X' := by
    rw [hXattach]
    exact Thm58NoEvenTrackThroughAttachments.thm58NoEvenTrackThroughAttachments
      G hG n' H' K' phi' y hyK'
  obtain ⟨J₀, ⟨eJ⟩⟩ := IsoTransport.exists_iso_fin J
  have hc3 : CyclicallyThreeConnected H' :=
    ⟨Fintype.card U, J₀, SubdivisionCounting.isKConnected_of_iso eJ hJ,
      Thm85Five8Transported.isSubdivision_of_iso eJ hForms'.2.1.1⟩
  have hXE : X' ⊆ H'.edgeSet := by
    rintro e ⟨he, -⟩
    exact he
  have h57 := _root_.Workspace.Statements.S05.SPGT.thm_5_7
    H' hForms'.2.1.2 hc3 X' hXE hnotrack
  have hcard : Fintype.card U = 4 := by
    obtain ⟨e⟩ := hK4
    calc
      Fintype.card U = Fintype.card (Fin 4) := Fintype.card_congr e.toEquiv
      _ = 4 := by simp
  have hall := all_fork_of_saturates G J hJ S N hSN H R hForms phi X hSat
  have hsubfork : ({a, b} : Set U)ᶜ ⊆
      {u : U | Thm84ForkCountForcesK4.ForkAt J R' X u} := by
    intro u hu
    have hua : u ≠ a := by
      intro h
      exact hu (by rw [h]; exact Set.mem_insert _ _)
    have hub : u ≠ b := by
      intro h
      exact hu (by rw [h]; exact Set.mem_insert_of_mem _ rfl)
    exact (fork_iff_of_agree_off_edge J R R' X a b u hua hub hdiff).mp (hall u)
  have hforkTwo : 2 ≤
      {u : U | Thm84ForkCountForcesK4.ForkAt J R' X u}.ncard := by
    have hle := Set.ncard_le_ncard hsubfork (Set.toFinite _)
    rw [ncard_compl_pair_eq_two hcard hab.ne] at hle
    exact hle
  have hbigTwo : 2 ≤
      {z ∈ branchVertices H' | (incidentEdges H' z ∩ X').Nontrivial}.ncard := by
    rw [Thm84ForkCountForcesK4.forkcount_eq_ncard
      G J hJ S N hSN H' R' hForms' phi' X]
    exact hforkTwo
  rcases h57.2 with (hSat' | h576) | ⟨hbigLe, hEq⟩
  · exact absurd hSat' hUnsat
  · exact outcome_of_five_seven_six G hG J hJ S N hSN (hnd hK4) hK4
      y hy X hX n' H' R' phi' hForms' h576
  · have hbigEq :
        {z ∈ branchVertices H' | (incidentEdges H' z ∩ X').Nontrivial}.ncard = 2 := by
      omega
    have h575 := hEq hbigEq
    exact fiveSevenFive_endgame G hG J hJ S N hSN hnd y hy X hX hK4 a b hab
      n H R phi n' H' R' phi' hForms hsym hForms' hsym' hSat hdiff h575

end Workspace.ProofLemmas.Thm84K4CaseReduction
