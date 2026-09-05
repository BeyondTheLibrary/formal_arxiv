import Workspace.ProofLemmas.Thm93CaseTwoCommon
import Workspace.Statements.S09.Thm_9_1

/-! The saturation branch of the last paragraph of 9.3, through the first leap. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoSaturated

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure Workspace.ProofLemmas.Thm93CaseTwoCommon

variable {V : Type*}

/-- PAPER (9.3, p. 49): "`a₁-y₁-Q₁-x₁-b₁` is an odd antipath in `G`."
We use its reverse, so the given list `Q₁` keeps its orientation. -/
theorem extend_antipath {G : SimpleGraph V} {Q : List V} {a b x y : V}
    (hQ : IsAntipathFrom G Q x y) (hab : G.Adj a b)
    (haQ : a ∉ Q) (hbQ : b ∉ Q)
    (hN : ∀ u ∈ Q, ∀ w ∈ ({a, b} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = y) ∨ (w = b ∧ u = x)))) :
    IsPathFrom Gᶜ (b :: (Q ++ [a])) b a := by
  have hx := (PathBasics.isPathFrom_ends_mem hQ).1
  have hy := (PathBasics.isPathFrom_ends_mem hQ).2
  have hb : ∀ u ∈ Q, Gᶜ.Adj b u ↔ u = x := by
    intro u hu
    have hne : b ≠ u := fun h => hbQ (h ▸ hu)
    rw [G.compl_adj, and_iff_right hne, G.adj_comm, hN u hu b (by simp)]
    simp [hab.ne.symm]
  have ha : ∀ u ∈ Q, Gᶜ.Adj a u ↔ u = y := by
    intro u hu
    have hne : a ≠ u := fun h => haQ (h ▸ hu)
    rw [G.compl_adj, and_iff_right hne, G.adj_comm, hN u hu a (by simp)]
    simp [hab.ne]
  exact PathAttach.isPathFrom_cons_concat hQ ((hb x hx).mpr rfl) ((ha y hy).mpr rfl)
    (fun h => h.2 hab.symm) hab.ne.symm hbQ haQ
    (fun u hu hne h => hne ((hb u hu).mp h))
    (fun u hu hne h => hne ((ha u hu).mp h))

/-- Missing one vertex of a saturating triangle puts each of the other vertices in `X`. -/
theorem mem_of_missed_triangle {X T : Set V} (h : (T \ X).Subsingleton)
    {x v : V} (hx : x ∈ T) (hxX : x ∉ X) (hv : v ∈ T) (hne : v ≠ x) : v ∈ X := by
  by_contra hvX
  exact hne (h ⟨hv, hvX⟩ ⟨hx, hxX⟩)

variable [Fintype V] [DecidableEq V]

/-- PAPER (9.3, p. 49): "every vertex in `X` has a non-neighbour in `V(Q₁)`; and hence
no vertex of `Q₂` belongs to `X`." This is precisely the use of 2.2 in the complement. -/
theorem other_antipath_missed {G : SimpleGraph V} (hG : Berge G)
    {K F : Set V} (hF : F ⊆ Kᶜ) (hconn : ConnectedSet G F)
    {Q Q' : List V} {a b : V}
    (hp : IsPathFrom Gᶜ (b :: (Q ++ [a])) b a)
    (hodd : Odd (pathLength Q))
    (hQK : ∀ w ∈ Q, w ∈ K) (hQ'K : ∀ w ∈ Q', w ∈ K)
    (ha : a ∈ common G K F) (hb : b ∈ common G K F)
    (hmiss : Disjoint (common G K F) {v | v ∈ Q})
    (hcomp : Complete G {v | v ∈ Q} {v | v ∈ Q'}) :
    Disjoint (common G K F) {v | v ∈ Q'} := by
  have hanti : AnticonnectedSet Gᶜ F := by
    change ConnectedSet Gᶜᶜ F
    rwa [compl_compl]
  have hlen : pathLength (b :: (Q ++ [a])) = pathLength Q + 2 := by
    have hQne : Q ≠ [] := by
      intro h
      simp [h, pathLength] at hodd
    have hpos : 0 < Q.length := List.length_pos_iff.mpr hQne
    rw [PathAttach.pathLength_cons_append_singleton]
    unfold pathLength
    omega
  have hpodd : Odd (pathLength (b :: (Q ++ [a]))) := by
    rw [hlen]
    exact hodd.add_even (by decide)
  have hpF : ∀ w ∈ b :: (Q ++ [a]), w ∉ F := by
    intro w hw hwF
    have hwK : w ∈ K := by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | hw | rfl
      · exact hb.1
      · exact hQK w hw
      · exact ha.1
    exact hF hwF hwK
  have hnoedge : ¬ ∃ u ∈ b :: (Q ++ [a]), ∃ v ∈ b :: (Q ++ [a]),
      EdgeComplete Gᶜ F u v := by
    apply no_complete_edge hp (by omega)
    intro w hw hcomplete
    have hwQ : w ∈ Q := by simpa [SPGT.interior] using hw
    exact Set.disjoint_left.mp hmiss ⟨hQK w hwQ, hcomplete⟩ hwQ
  apply Set.disjoint_left.mpr
  intro v hv hvQ'
  obtain ⟨w, hw, hadj⟩ := Workspace.Statements.S02.SPGT.thm_2_2 Gᶜ
    (HoleBasics.berge_compl.mpr hG) F hanti (b :: (Q ++ [a])) b a hp hpF hpodd
    hb.2 ha.2 hnoedge v hv.2
  have hwQ : w ∈ Q := by simpa [SPGT.interior] using hw
  exact hadj.2 (hcomp w hwQ v hvQ').symm

/-- PAPER (9.3, p. 49): "This restores the symmetry between `Q₁,Q₂`."
Both antipaths miss the common neighbours, while all four ends of the short paths are
common neighbours. -/
theorem saturated_common_sets (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K))
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary Gᶜ H K phi Q₁ Q₂ x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂
      c₁ c₂ c₃ c₄ N)
    (hsat : SaturatesLineGraph H {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F}) :
    ({v | v ∈ P₁} ∪ {v | v ∈ P₂} : Set V) ⊆ common G K F ∧
    Disjoint (common G K F) {v | v ∈ Q₁} ∧
    Disjoint (common G K F) {v | v ∈ Q₂} := by
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq, l1, l2, lq1, lq2, hanti, hcomp,
    e11, e12, e21, e22, n11, n12, n21, n22⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  obtain ⟨hN, _, _, _, _, _, hbvs, _, _, _, _, hN1, hN2, hN3, hN4, _, _⟩ := hdict
  have ha1 := (PathBasics.isPathFrom_ends_mem hP₁).1
  have hb1 := (PathBasics.isPathFrom_ends_mem hP₁).2
  have ha2 := (PathBasics.isPathFrom_ends_mem hP₂).1
  have hb2 := (PathBasics.isPathFrom_ends_mem hP₂).2
  have hx1 := (PathBasics.isPathFrom_ends_mem hQ₁).1
  have hy1 := (PathBasics.isPathFrom_ends_mem hQ₁).2
  have hx2 := (PathBasics.isPathFrom_ends_mem hQ₂).1
  have hy2 := (PathBasics.isPathFrom_ends_mem hQ₂).2
  have ht1 := common_triangle phi N hN hsat (c := c₁) (by rw [hbvs]; simp)
  have ht2 := common_triangle phi N hN hsat (c := c₂) (by rw [hbvs]; simp)
  have ht3 := common_triangle phi N hN hsat (c := c₃) (by rw [hbvs]; simp)
  have ht4 := common_triangle phi N hN hsat (c := c₄) (by rw [hbvs]; simp)
  rw [hN1] at ht1
  rw [hN2] at ht2
  rw [hN3] at ht3
  rw [hN4] at ht4
  have hQ1K : ∀ w ∈ Q₁, w ∈ K := by rw [hK]; exact fun _ hw => Or.inl (Or.inr hw)
  have hQ2K : ∀ w ∈ Q₂, w ∈ K := by rw [hK]; exact fun _ hw => Or.inr hw
  have hpair1 := KnotLabels.eq_pair_of_length_one hP₁ hP₁len
  have hpair2 := KnotLabels.eq_pair_of_length_one hP₂ hP₂len
  have hab := PathBasics.isPathFrom_ends_adj_of_length_one hP₁ hP₁len
  have hp1 := extend_antipath hQ₁ hab (d1q1 _ ha1) (d1q1 _ hb1) n11
  have hp2 := extend_antipath hQ₂ hab (d1q2 _ ha1) (d1q2 _ hb1) n12
  obtain ⟨⟨_, _, odd1, odd2⟩, _⟩ := Workspace.Statements.S09.SPGT.thm_9_1 G hG _ _ _ _ hknot
  have hends : Disjoint (common G K F) {v | v ∈ Q₁} ∨
      Disjoint (common G K F) {v | v ∈ Q₂} :=
    common_misses_one hknot hK hFsub hP₁len hP₂len hFattach phi happ hsat
  have hfour : a₁ ∈ common G K F ∧ b₁ ∈ common G K F ∧
      a₂ ∈ common G K F ∧ b₂ ∈ common G K F := by
    rcases hends with hm | hm
    · have hxX : x₁ ∉ common G K F := fun h => Set.disjoint_left.mp hm h hx1
      have hyX : y₁ ∉ common G K F := fun h => Set.disjoint_left.mp hm h hy1
      exact ⟨mem_of_missed_triangle ht3 (by simp) hyX (by simp) (fun h => d1q1 _ ha1 (h ▸ hy1)),
        mem_of_missed_triangle ht1 (by simp) hxX (by simp) (fun h => d1q1 _ hb1 (h ▸ hx1)),
        mem_of_missed_triangle ht3 (by simp) hyX (by simp) (fun h => d2q1 _ ha2 (h ▸ hy1)),
        mem_of_missed_triangle ht1 (by simp) hxX (by simp) (fun h => d2q1 _ hb2 (h ▸ hx1))⟩
    · have hxX : x₂ ∉ common G K F := fun h => Set.disjoint_left.mp hm h hx2
      have hyX : y₂ ∉ common G K F := fun h => Set.disjoint_left.mp hm h hy2
      exact ⟨mem_of_missed_triangle ht4 (by simp) hyX (by simp) (fun h => d1q2 _ ha1 (h ▸ hy2)),
        mem_of_missed_triangle ht2 (by simp) hxX (by simp) (fun h => d1q2 _ hb1 (h ▸ hx2)),
        mem_of_missed_triangle ht2 (by simp) hxX (by simp) (fun h => d2q2 _ ha2 (h ▸ hx2)),
        mem_of_missed_triangle ht4 (by simp) hyX (by simp) (fun h => d2q2 _ hb2 (h ▸ hy2))⟩
  refine ⟨?_, ?_⟩
  · intro v hv
    simp only [hpair1, hpair2, Set.mem_union, Set.mem_setOf_eq, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | (rfl | rfl)
    exacts [hfour.1, hfour.2.1, hfour.2.2.1, hfour.2.2.2]
  · rcases hends with hm | hm
    · exact ⟨hm, other_antipath_missed hG hFsub hFconn hp1 odd1 hQ1K hQ2K
        hfour.1 hfour.2.1 hm hcomp⟩
    · exact ⟨other_antipath_missed hG hFsub hFconn hp2 odd2 hQ2K hQ1K
        hfour.1 hfour.2.1 hm (fun u hu v hv => (hcomp v hv u hu).symm), hm⟩

/-- PAPER (9.3, p. 49): "its ends are complete to `F`, and its internal vertices are not.
By 2.1, `F` contains a leap." -/
theorem leap_on_long_antipath {G : SimpleGraph V} (hG : Berge G)
    {K F : Set V} (hF : F ⊆ Kᶜ) (hconn : ConnectedSet G F)
    {Q : List V} {a b : V} (hp : IsPathFrom Gᶜ (b :: (Q ++ [a])) b a)
    (hodd : Odd (pathLength Q)) (hlong : 3 ≤ pathLength Q)
    (hQK : ∀ w ∈ Q, w ∈ K) (ha : a ∈ common G K F) (hb : b ∈ common G K F)
    (hmiss : Disjoint (common G K F) {v | v ∈ Q}) :
    ∃ f₁ ∈ F, ∃ f₂ ∈ F, IsLeapForPath Gᶜ (b :: (Q ++ [a])) f₁ f₂ := by
  have hanti : AnticonnectedSet Gᶜ F := by
    change ConnectedSet Gᶜᶜ F
    rwa [compl_compl]
  have hlen : pathLength (b :: (Q ++ [a])) = pathLength Q + 2 := by
    rw [PathAttach.pathLength_cons_append_singleton]
    unfold pathLength at *
    omega
  have hpodd : Odd (pathLength (b :: (Q ++ [a]))) := by
    rw [hlen]
    exact hodd.add_even (by decide)
  have hpF : ∀ w ∈ b :: (Q ++ [a]), w ∉ F := by
    intro w hw hwF
    have hwK : w ∈ K := by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | hw | rfl
      · exact hb.1
      · exact hQK w hw
      · exact ha.1
    exact hF hwF hwK
  have hnoedge : ¬ ∃ u ∈ b :: (Q ++ [a]), ∃ v ∈ b :: (Q ++ [a]),
      EdgeComplete Gᶜ F u v := by
    apply no_complete_edge hp (by omega)
    intro w hw hcomplete
    have hwQ : w ∈ Q := by simpa [SPGT.interior] using hw
    exact Set.disjoint_left.mp hmiss ⟨hQK w hwQ, hcomplete⟩ hwQ
  rcases Workspace.Statements.S02.SPGT.thm_2_1 Gᶜ (HoleBasics.berge_compl.mpr hG)
    F hanti (b :: (Q ++ [a])) b a hp hpF hpodd hb.2 ha.2 with he | hl | ⟨h3, _⟩
  · exact (hnoedge he).elim
  · exact hl.2
  · omega

end Workspace.ProofLemmas.Thm93CaseTwoSaturated
