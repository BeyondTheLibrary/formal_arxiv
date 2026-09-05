import Workspace.ProofLemmas.Thm93CaseTwoSixOnePairs
import Workspace.ProofLemmas.Thm93CaseTwoSixOneDict
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.Statements.S06.Thm_6_1
import Workspace.Statements.S09.Thm_9_1

/-!
# The nonsaturating branch of the final paragraph of 9.3
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93CaseTwoSixOne

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure
open Workspace.ProofLemmas.Thm93CaseTwoPairs
open Workspace.ProofLemmas.Thm93CaseTwoSixOnePairs
open Workspace.ProofLemmas.Thm93CaseTwoSixOneDict

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (proof of 9.3, printed p. 49):** *"If `X` does not saturate `L(H)` in `G̅`, then
by (2) we may apply 6.1.  Since `Q₁` has length `> 1` it follows that the last outcome of 6.1
holds, and hence statement 3 of the theorem holds."*

The first two outcomes of 6.1 are overshadowed appearances of `K₄` in `G̅` and in `G`, both
excluded by hypothesis; the third needs `J = K₃,₃`; the fourth says `|V(H)| = 6`, and then each
of the two long branches of `H` has only one internal vertex, so `Q₁` and `Q₂` would both have
length `1`.  The last outcome gives two `G`-adjacent vertices of `F` whose neighbours in `K`
are exactly those of the two ends of one of `P₁, P₂`. -/
theorem nonsaturating_pair
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (hQlong : ¬ (pathLength Q₁ = 1 ∧ pathLength Q₂ = 1))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoover : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi)
    (hnoovercompl : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' psi)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary Gᶜ H K phi Q₁ Q₂ x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂
      c₁ c₂ c₃ c₄ N)
    (hallmajor : ∀ f ∈ F, MajorForLineGraph Gᶜ H K phi f)
    (hnotsat : ¬ SaturatesLineGraph H {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F}) :
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  have hGc : Berge Gᶜ := Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG
  have hYanti : AnticonnectedSet Gᶜ F := by
    show ConnectedSet Gᶜᶜ F
    rw [compl_compl]
    exact hFconn
  have h61 := Workspace.Statements.S06.SPGT.thm_6_1 Gᶜ hGc 4 (⊤ : SimpleGraph (Fin 4))
    Workspace.ProofLemmas.SubdivisionCounting.k4_three_connected n H K happ.1 phi F hYanti
    hallmajor hnotsat
  obtain ⟨hN, hnd, h12, h23, h34, h41, hbv, hex₁, hex₂, hex₃, hex₄,
    hNc₁, hNc₂, hNc₃, hNc₄, hbr₁, hbr₂⟩ := hdict
  obtain ⟨he12, hi12⟩ := hex₁
  obtain ⟨he23, hi23⟩ := hex₂
  obtain ⟨he34, hi34⟩ := hex₃
  obtain ⟨he41, hi41⟩ := hex₄
  have hL := labels_of_knot hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len hK
  obtain ⟨⟨d1, d2, d3, d4, d5, d6, d7⟩, ⟨d8, d9, d10, d11, d12, d13⟩,
    ⟨d14, d15, d16, d17, d18⟩, ⟨d19, d20, d21, d22⟩,
    ⟨d23, d24, d25, d26, d27, d28⟩⟩ := all_ne hL
  have hthird1 : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ incidentEdges H c₁ →
      e ≠ s(c₁, c₂) → e ≠ s(c₄, c₁) → (↑(phi ⟨e, he⟩) : V) = x₁ := by
    intro e he hinc hne1 hne2
    have hm : (↑(phi ⟨e, he⟩) : V) ∈ N c₁ := img_mem_N phi N hN c₁ he hinc
    rw [hNc₁] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact absurd (img_inj phi he he12 (h.trans hi12.symm)) hne1
    · exact absurd (img_inj phi he he41 (h.trans hi41.symm)) hne2
    · exact h
  have hthird2 : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ incidentEdges H c₂ →
      e ≠ s(c₁, c₂) → e ≠ s(c₂, c₃) → (↑(phi ⟨e, he⟩) : V) = x₂ := by
    intro e he hinc hne1 hne2
    have hm : (↑(phi ⟨e, he⟩) : V) ∈ N c₂ := img_mem_N phi N hN c₂ he hinc
    rw [hNc₂] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact absurd (img_inj phi he he12 (h.trans hi12.symm)) hne1
    · exact absurd (img_inj phi he he23 (h.trans hi23.symm)) hne2
    · exact h
  have hthird3 : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ incidentEdges H c₃ →
      e ≠ s(c₂, c₃) → e ≠ s(c₃, c₄) → (↑(phi ⟨e, he⟩) : V) = y₁ := by
    intro e he hinc hne1 hne2
    have hm : (↑(phi ⟨e, he⟩) : V) ∈ N c₃ := img_mem_N phi N hN c₃ he hinc
    rw [hNc₃] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact absurd (img_inj phi he he34 (h.trans hi34.symm)) hne2
    · exact absurd (img_inj phi he he23 (h.trans hi23.symm)) hne1
    · exact h
  have hthird4 : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ incidentEdges H c₄ →
      e ≠ s(c₃, c₄) → e ≠ s(c₄, c₁) → (↑(phi ⟨e, he⟩) : V) = y₂ := by
    intro e he hinc hne1 hne2
    have hm : (↑(phi ⟨e, he⟩) : V) ∈ N c₄ := img_mem_N phi N hN c₄ he hinc
    rw [hNc₄] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact absurd (img_inj phi he he34 (h.trans hi34.symm)) hne1
    · exact absurd (img_inj phi he he41 (h.trans hi41.symm)) hne2
    · exact h
  have hn13 : ¬ H.Adj c₁ c₃ := by
    refine not_adj_of_N_disjoint phi N hN ?_
    intro v hv hv'
    rw [hNc₁] at hv
    rw [hNc₃] at hv'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
    rcases hv with rfl | rfl | rfl <;> rcases hv' with h | h | h
    exacts [d1 h.symm, d8 h, d11 h, d3 h.symm, d14 h.symm, d20 h,
      d4 h.symm, d15 h.symm, d23 h]
  have hn24 : ¬ H.Adj c₂ c₄ := by
    refine not_adj_of_N_disjoint phi N hN ?_
    intro v hv hv'
    rw [hNc₂] at hv
    rw [hNc₄] at hv'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
    rcases hv with rfl | rfl | rfl <;> rcases hv' with h | h | h
    exacts [d1 h.symm, d9 h, d13 h, d2 h.symm, d14 h, d18 h,
      d6 h.symm, d21 h.symm, d28 h]
  have hk33 : ¬ Nonempty ((⊤ : SimpleGraph (Fin 4)) ≃g
      completeBipartiteGraph (Fin 3) (Fin 3)) := by
    rintro ⟨e⟩
    have := Fintype.card_congr e.toEquiv
    simp at this
  rcases h61 with ⟨-, hover⟩ | ⟨-, -, hover⟩ | ⟨h33, -, -⟩ | ⟨-, hsix⟩ | ⟨-, -, hlast⟩
  · exact (hnoovercompl hover).elim
  · rw [compl_compl] at hover
    exact (hnoover hover).elim
  · exact (hk33 h33).elim
  · exfalso
    obtain ⟨⟨-, -, hoQ₁, hoQ₂⟩, -⟩ :=
      Workspace.Statements.S09.SPGT.thm_9_1 G hG P₁ P₂ Q₁ Q₂ hknot
    obtain ⟨q₁, hq₁, -, hset₁⟩ := hbr₁
    obtain ⟨q₂, hq₂, -, hset₂⟩ := hbr₂
    have hlen₁ : Q₁.length ≤ 3 := le_trans
      (length_le_trackLength phi hQ₁.1.2.1 hq₁.1.2.1 hset₁)
      (trackLength_le_three hq₁ hnd hbv hsix)
    have hlen₂ : Q₂.length ≤ 3 := le_trans
      (length_le_trackLength phi hQ₂.1.2.1 hq₂.1.2.1 hset₂)
      (trackLength_le_three hq₂ hnd hbv hsix)
    obtain ⟨k₁, hk₁⟩ := hoQ₁
    obtain ⟨k₂, hk₂⟩ := hoQ₂
    simp only [pathLength] at hk₁ hk₂
    exact hQlong ⟨by simp only [pathLength]; omega, by simp only [pathLength]; omega⟩
  · obtain ⟨y, hyF, y', hy'F, hnadjyy', v₁, v₂, v₃, v₄, ea, eb, ec, ed, edp, edq, edr, eds,
      hvnd, hbv', ha12, ha23, ha34, ha41, hea, heb, hec, hed,
      hpi, hpa, hpb, hqi, hqb, hqc, hri, hrc, hrd, hsi, hsd, hsa,
      hysup, hysub, hy'sup, hy'sub⟩ := hlast
    have hsets : ({v₁, v₂, v₃, v₄} : Set (Fin n)) = {c₁, c₂, c₃, c₄} := by
      rw [← hbv']; exact hbv
    have hmem : ∀ v : Fin n, v ∈ ({v₁, v₂, v₃, v₄} : Set (Fin n)) →
        v ∈ ({c₁, c₂, c₃, c₄} : Set (Fin n)) := fun v hv => hsets ▸ hv
    rcases cycle_labels hvnd hmem hn13 hn24 ha12 ha23 ha34 ha41 with
      (hcase | hcase) | (hcase | hcase) | (hcase | hcase) | (hcase | hcase)
    · -- (v₁, v₂, v₃, v₄) = (c₁, c₂, c₃, c₄)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₁, v₂) := by rw [hea]
      subst hea'
      have heb' : eb = s(v₂, v₃) := by rw [heb]
      subst heb'
      have hec' : ec = s(v₃, v₄) := by rw [hec]
      subst hec'
      have hed' : ed = s(v₄, v₁) := by rw [hed]
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = x₂ :=
        hthird2 edp hedpe hpi hpa hpb
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = y₁ :=
        hthird3 edq hedqe hqi hqb hqc
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = y₂ :=
        hthird4 edr hedre hri hrc hrd
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = x₁ :=
        hthird1 eds hedse hsi hsa hsd
      refine pair_first_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y') (f₂ := y) hy'F hyF (hFsub hy'F) (hFsub hyF)
        (fun h => hnadjyy' h.symm) ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hy'sup he34 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hy'sup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hy'sup he41 (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi12]; simp
        · rw [hi23]; simp
        · rw [hi34]; simp
        · rw [hi41]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi12]
          exact adj_of_edge_mem phi hysup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hysup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hysup he41 (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi12]; simp
        · rw [hi23]; simp
        · rw [hi34]; simp
        · rw [hi41]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
    · -- (v₁, v₂, v₃, v₄) = (c₂, c₃, c₄, c₁)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₁, v₂) := by rw [hea]
      subst hea'
      have heb' : eb = s(v₂, v₃) := by rw [heb]
      subst heb'
      have hec' : ec = s(v₃, v₄) := by rw [hec]
      subst hec'
      have hed' : ed = s(v₄, v₁) := by rw [hed]
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = y₁ :=
        hthird3 edp hedpe hpi hpa hpb
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = y₂ :=
        hthird4 edq hedqe hqi hqb hqc
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = x₁ :=
        hthird1 edr hedre hri hrd hrc
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = x₂ :=
        hthird2 eds hedse hsi hsd hsa
      refine pair_second_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y) (f₂ := y') hyF hy'F (hFsub hyF) (hFsub hy'F)
        hnadjyy' ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hysup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hysup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hysup he23 (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi23]; simp
        · rw [hi34]; simp
        · rw [hi41]; simp
        · rw [hi12]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hy'sup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hy'sup he12 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hy'sup he41 (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi23]; simp
        · rw [hi34]; simp
        · rw [hi41]; simp
        · rw [hi12]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp
    · -- (v₁, v₂, v₃, v₄) = (c₃, c₄, c₁, c₂)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₁, v₂) := by rw [hea]
      subst hea'
      have heb' : eb = s(v₂, v₃) := by rw [heb]
      subst heb'
      have hec' : ec = s(v₃, v₄) := by rw [hec]
      subst hec'
      have hed' : ed = s(v₄, v₁) := by rw [hed]
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = y₂ :=
        hthird4 edp hedpe hpi hpa hpb
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = x₁ :=
        hthird1 edq hedqe hqi hqc hqb
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = x₂ :=
        hthird2 edr hedre hri hrc hrd
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = y₁ :=
        hthird3 eds hedse hsi hsd hsa
      refine pair_first_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y) (f₂ := y') hyF hy'F (hFsub hyF) (hFsub hy'F)
        hnadjyy' ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hysup he34 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hysup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hysup he41 (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi34]; simp
        · rw [hi41]; simp
        · rw [hi12]; simp
        · rw [hi23]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi12]
          exact adj_of_edge_mem phi hy'sup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hy'sup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hy'sup he41 (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi34]; simp
        · rw [hi41]; simp
        · rw [hi12]; simp
        · rw [hi23]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp
    · -- (v₁, v₂, v₃, v₄) = (c₄, c₁, c₂, c₃)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₁, v₂) := by rw [hea]
      subst hea'
      have heb' : eb = s(v₂, v₃) := by rw [heb]
      subst heb'
      have hec' : ec = s(v₃, v₄) := by rw [hec]
      subst hec'
      have hed' : ed = s(v₄, v₁) := by rw [hed]
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = x₁ :=
        hthird1 edp hedpe hpi hpb hpa
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = x₂ :=
        hthird2 edq hedqe hqi hqb hqc
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = y₁ :=
        hthird3 edr hedre hri hrc hrd
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = y₂ :=
        hthird4 eds hedse hsi hsd hsa
      refine pair_second_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y') (f₂ := y) hy'F hyF (hFsub hy'F) (hFsub hyF)
        (fun h => hnadjyy' h.symm) ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hy'sup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hy'sup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hy'sup he23 (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi41]; simp
        · rw [hi12]; simp
        · rw [hi23]; simp
        · rw [hi34]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hysup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hysup he12 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hysup he41 (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi41]; simp
        · rw [hi12]; simp
        · rw [hi23]; simp
        · rw [hi34]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
    · -- (v₁, v₂, v₃, v₄) = (c₂, c₁, c₄, c₃)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₂, v₁) := by rw [hea]; exact Sym2.eq_swap
      subst hea'
      have heb' : eb = s(v₃, v₂) := by rw [heb]; exact Sym2.eq_swap
      subst heb'
      have hec' : ec = s(v₄, v₃) := by rw [hec]; exact Sym2.eq_swap
      subst hec'
      have hed' : ed = s(v₁, v₄) := by rw [hed]; exact Sym2.eq_swap
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = x₁ :=
        hthird1 edp hedpe hpi hpa hpb
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = y₂ :=
        hthird4 edq hedqe hqi hqc hqb
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = y₁ :=
        hthird3 edr hedre hri hrd hrc
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = x₂ :=
        hthird2 eds hedse hsi hsa hsd
      refine pair_first_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y') (f₂ := y) hy'F hyF (hFsub hy'F) (hFsub hyF)
        (fun h => hnadjyy' h.symm) ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hy'sup he34 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hy'sup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hy'sup he41 (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi12]; simp
        · rw [hi41]; simp
        · rw [hi34]; simp
        · rw [hi23]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi12]
          exact adj_of_edge_mem phi hysup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hysup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hysup he41 (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi12]; simp
        · rw [hi41]; simp
        · rw [hi34]; simp
        · rw [hi23]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
    · -- (v₁, v₂, v₃, v₄) = (c₁, c₄, c₃, c₂)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₂, v₁) := by rw [hea]; exact Sym2.eq_swap
      subst hea'
      have heb' : eb = s(v₃, v₂) := by rw [heb]; exact Sym2.eq_swap
      subst heb'
      have hec' : ec = s(v₄, v₃) := by rw [hec]; exact Sym2.eq_swap
      subst hec'
      have hed' : ed = s(v₁, v₄) := by rw [hed]; exact Sym2.eq_swap
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = y₂ :=
        hthird4 edp hedpe hpi hpb hpa
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = y₁ :=
        hthird3 edq hedqe hqi hqc hqb
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = x₂ :=
        hthird2 edr hedre hri hrd hrc
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = x₁ :=
        hthird1 eds hedse hsi hsd hsa
      refine pair_second_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y') (f₂ := y) hy'F hyF (hFsub hy'F) (hFsub hyF)
        (fun h => hnadjyy' h.symm) ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hy'sup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hy'sup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hy'sup he23 (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi41]; simp
        · rw [hi34]; simp
        · rw [hi23]; simp
        · rw [hi12]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hysup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hysup he12 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hysup he41 (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi41]; simp
        · rw [hi34]; simp
        · rw [hi23]; simp
        · rw [hi12]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
    · -- (v₁, v₂, v₃, v₄) = (c₄, c₃, c₂, c₁)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₂, v₁) := by rw [hea]; exact Sym2.eq_swap
      subst hea'
      have heb' : eb = s(v₃, v₂) := by rw [heb]; exact Sym2.eq_swap
      subst heb'
      have hec' : ec = s(v₄, v₃) := by rw [hec]; exact Sym2.eq_swap
      subst hec'
      have hed' : ed = s(v₁, v₄) := by rw [hed]; exact Sym2.eq_swap
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = y₁ :=
        hthird3 edp hedpe hpi hpb hpa
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = x₂ :=
        hthird2 edq hedqe hqi hqc hqb
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = x₁ :=
        hthird1 edr hedre hri hrc hrd
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = y₂ :=
        hthird4 eds hedse hsi hsa hsd
      refine pair_first_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y) (f₂ := y') hyF hy'F (hFsub hyF) (hFsub hy'F)
        hnadjyy' ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hysup he34 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hysup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hysup he41 (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi34]; simp
        · rw [hi23]; simp
        · rw [hi12]; simp
        · rw [hi41]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi12]
          exact adj_of_edge_mem phi hy'sup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hy'sup he23 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hy'sup he41 (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi34]; simp
        · rw [hi23]; simp
        · rw [hi12]; simp
        · rw [hi41]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp
    · -- (v₁, v₂, v₃, v₄) = (c₃, c₂, c₁, c₄)
      simp only [Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      have hea' : ea = s(v₂, v₁) := by rw [hea]; exact Sym2.eq_swap
      subst hea'
      have heb' : eb = s(v₃, v₂) := by rw [heb]; exact Sym2.eq_swap
      subst heb'
      have hec' : ec = s(v₄, v₃) := by rw [hec]; exact Sym2.eq_swap
      subst hec'
      have hed' : ed = s(v₁, v₄) := by rw [hed]; exact Sym2.eq_swap
      subst hed'
      have hedpe : edp ∈ H.edgeSet := hpi.1
      have hedpv : (↑(phi ⟨edp, hedpe⟩) : V) = x₂ :=
        hthird2 edp hedpe hpi hpb hpa
      have hedqe : edq ∈ H.edgeSet := hqi.1
      have hedqv : (↑(phi ⟨edq, hedqe⟩) : V) = x₁ :=
        hthird1 edq hedqe hqi hqb hqc
      have hedre : edr ∈ H.edgeSet := hri.1
      have hedrv : (↑(phi ⟨edr, hedre⟩) : V) = y₂ :=
        hthird4 edr hedre hri hrd hrc
      have hedse : eds ∈ H.edgeSet := hsi.1
      have hedsv : (↑(phi ⟨eds, hedse⟩) : V) = y₁ :=
        hthird3 eds hedse hsi hsa hsd
      refine pair_second_of_sets G hknot hP₁ hP₂ hQ₁ hQ₂ hL
        (f₁ := y) (f₂ := y') hyF hy'F (hFsub hyF) (hFsub hy'F)
        hnadjyy' ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hysup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hysup he12 (by simp)
        · rw [← hi23]
          exact adj_of_edge_mem phi hysup he23 (by simp)
        · rw [← hedqv]
          exact adj_of_edge_mem phi hysup hedqe (by simp)
        · rw [← hedrv]
          exact adj_of_edge_mem phi hysup hedre (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hysub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi23]; simp
        · rw [hi12]; simp
        · rw [hi41]; simp
        · rw [hi34]; simp
        · rw [hedqv]; simp
        · rw [hedrv]; simp
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · rw [← hi34]
          exact adj_of_edge_mem phi hy'sup he34 (by simp)
        · rw [← hi12]
          exact adj_of_edge_mem phi hy'sup he12 (by simp)
        · rw [← hi41]
          exact adj_of_edge_mem phi hy'sup he41 (by simp)
        · rw [← hedsv]
          exact adj_of_edge_mem phi hy'sup hedse (by simp)
        · rw [← hedpv]
          exact adj_of_edge_mem phi hy'sup hedpe (by simp)
      · intro w hw hadjw
        obtain ⟨e, he, hmem, rfl⟩ := mem_image_of_adj phi hy'sub hw hadjw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hi23]; simp
        · rw [hi12]; simp
        · rw [hi41]; simp
        · rw [hi34]; simp
        · rw [hedpv]; simp
        · rw [hedsv]; simp


end Workspace.ProofLemmas.Thm93CaseTwoSixOne
