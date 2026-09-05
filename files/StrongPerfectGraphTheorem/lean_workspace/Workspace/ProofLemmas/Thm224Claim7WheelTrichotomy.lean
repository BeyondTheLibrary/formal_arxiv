import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm224Claim7Reduction
import Workspace.Statements.S16.Thm_16_1

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim7WheelTrichotomy

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.KiteTailBasics

private theorem third_vertex_adjacent_in_three_path
    {V : Type*} {G : SimpleGraph V} {p₁ p₂ p₃ a b c : V}
    (hP : IsPathList G [p₁, p₂, p₃])
    (ha : a ∈ [p₁, p₂, p₃]) (hb : b ∈ [p₁, p₂, p₃]) (hc : c ∈ [p₁, p₂, p₃])
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.Adj c a ∨ G.Adj c b := by
  have h12 : G.Adj p₁ p₂ := by
    simpa using Workspace.ProofLemmas.PathBasics.path_adj_succ hP (i := 0) (by simp)
  have h23 : G.Adj p₂ p₃ := by
    simpa using Workspace.ProofLemmas.PathBasics.path_adj_succ hP (i := 1) (by simp)
  simp at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    simp_all [SimpleGraph.adj_comm]

/-- The three alternatives of theorem 16.1 are impossible for the rim neighbours
`a`, `b`, and `z` supplied at the end of the claim-(7) reduction. -/
theorem thm224Claim7WheelTrichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y : Set V} {q z a b x₀ x₁ : V}
    (hopt : OptimalWheel G C Y)
    (hnokite : ¬ ∃ v : V, IsKite G C Y v)
    (hqC : q ∉ C)
    (hqY : q ∉ Y)
    (hqnc : ¬ VertexComplete G q Y)
    (hab : a ≠ b)
    (haC : a ∈ C)
    (hbC : b ∈ C)
    (habAdj : G.Adj a b)
    (haY : VertexComplete G a Y)
    (hbY : VertexComplete G b Y)
    (hopp : OppositeWheelParity G C Y a b)
    (hzC : z ∈ C)
    (hqa : G.Adj q a)
    (hqb : G.Adj q b)
    (hqz : G.Adj q z)
    (haOutside : a ∉ ({x₀, z, x₁} : Set V))
    (hbOutside : b ∉ ({x₀, z, x₁} : Set V))
    (hnb : IsRimNeighbours G C z x₀ x₁) :
    False := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have haz : a ≠ z := by
    intro h
    apply haOutside
    rw [h]
    simp
  have hbz : b ≠ z := by
    intro h
    apply hbOutside
    rw [h]
    simp
  have hza : ¬ G.Adj z a := by
    intro h
    rcases hnb.2.2.2.2.2 a haC h with ha0 | ha1
    · apply haOutside
      rw [ha0]
      simp
    · apply haOutside
      rw [ha1]
      simp
  have hzb : ¬ G.Adj z b := by
    intro h
    rcases hnb.2.2.2.2.2 b hbC h with hb0 | hb1
    · apply hbOutside
      rw [hb0]
      simp
    · apply hbOutside
      rw [hb1]
      simp
  have htri := _root_.Workspace.Statements.S16.SPGT.thm_16_1
    G hG C Y hw q hqC hqY hqnc a b hqa hqb hopp
  rcases htri.2 with ⟨a₁, a₂, ha₁a₂, hneighbors, ha₁a₂adj, ha₁Y, ha₂Y⟩ |
      ⟨p₁, p₂, p₃, hP, hblock, hp₁, hp₂, hp₃, hother⟩ | hlarger
  · have hsub : ({a, b, z} : Set V) ⊆ ({a₁, a₂} : Set V) := by
      rw [← hneighbors]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨haC, hqa⟩
      · exact ⟨hbC, hqb⟩
      · exact ⟨hzC, hqz⟩
    have hcard3 : ({a, b, z} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab, haz]), Set.ncard_pair hbz]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hcard3, Set.ncard_pair ha₁a₂] at hle
    omega
  · have hp₁C : p₁ ∈ C := by
      obtain ⟨k, hk⟩ := hblock
      rcases hk with hk | hk
      · exact List.mem_rotate.mp (hk.subset (by simp))
      · exact List.mem_rotate.mp (hk.subset (by simp))
    have hp₂C : p₂ ∈ C := by
      obtain ⟨k, hk⟩ := hblock
      rcases hk with hk | hk
      · exact List.mem_rotate.mp (hk.subset (by simp))
      · exact List.mem_rotate.mp (hk.subset (by simp))
    have hp₃C : p₃ ∈ C := by
      obtain ⟨k, hk⟩ := hblock
      rcases hk with hk | hk
      · exact List.mem_rotate.mp (hk.subset (by simp))
      · exact List.mem_rotate.mp (hk.subset (by simp))
    have hp₁q : G.Adj q p₁ := (hp₁ q (Or.inr rfl)).symm
    have hp₂q : G.Adj q p₂ := (hp₂ q (Or.inr rfl)).symm
    have hp₃q : G.Adj q p₃ := (hp₃ q (Or.inr rfl)).symm
    have hextra : ∃ r : V,
        r ∈ C ∧ G.Adj q r ∧ r ∉ ({p₁, p₂, p₃} : Set V) := by
      by_cases haP : a ∈ ({p₁, p₂, p₃} : Set V)
      · by_cases hbP : b ∈ ({p₁, p₂, p₃} : Set V)
        · by_cases hzP : z ∈ ({p₁, p₂, p₃} : Set V)
          · have hadj := third_vertex_adjacent_in_three_path hP
              (by simpa using haP) (by simpa using hbP) (by simpa using hzP)
              hab haz hbz
            rcases hadj with hadj | hadj
            · exact (hza hadj).elim
            · exact (hzb hadj).elim
          · exact ⟨z, hzC, hqz, hzP⟩
        · exact ⟨b, hbC, hqb, hbP⟩
      · exact ⟨a, haC, hqa, haP⟩
    obtain ⟨r, hrC, hqr, hrout⟩ := hextra
    have hnd : ([p₁, p₂, p₃] : List V).Nodup := hP.2.1
    have hdistinct : (p₁ ≠ p₂ ∧ p₁ ≠ p₃) ∧ p₂ ≠ p₃ := by
      simpa using hnd
    have hp₁p₂ : p₁ ≠ p₂ := hdistinct.1.1
    have hp₁p₃ : p₁ ≠ p₃ := hdistinct.1.2
    have hp₂p₃ : p₂ ≠ p₃ := hdistinct.2
    have hr₁ : r ≠ p₁ := by
      intro h
      apply hrout
      rw [h]
      simp
    have hr₂ : r ≠ p₂ := by
      intro h
      apply hrout
      rw [h]
      simp
    have hr₃ : r ≠ p₃ := by
      intro h
      apply hrout
      rw [h]
      simp
    have hfour : ({p₁, p₂, p₃, r} : Set V).ncard = 4 := by
      simp [hp₁p₂, hp₁p₃, hp₂p₃, Ne.symm hr₁, Ne.symm hr₂, Ne.symm hr₃]
    have hsub : ({p₁, p₂, p₃, r} : Set V) ⊆ {c : V | c ∈ C ∧ G.Adj q c} := by
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨hp₁C, hp₁q⟩
      · exact ⟨hp₂C, hp₂q⟩
      · exact ⟨hp₃C, hp₃q⟩
      · exact ⟨hrC, hqr⟩
    have hdeg : 4 ≤ {c : V | c ∈ C ∧ G.Adj q c}.ncard := by
      rw [← hfour]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    apply hnokite
    refine ⟨q, hw, hqY, hqC, hqnc, hdeg, ?_⟩
    rcases hblock with ⟨k, hk | hk⟩
    · exact ⟨p₁, p₂, p₃, ⟨k, hk⟩, hp₁q, hp₂q, hp₃q,
        fun v hv => hp₁ v (Or.inl hv), fun v hv => hp₂ v (Or.inl hv),
        fun v hv => hp₃ v (Or.inl hv)⟩
    · exact ⟨p₃, p₂, p₁, ⟨k, hk⟩, hp₃q, hp₂q, hp₁q,
        fun v hv => hp₃ v (Or.inl hv), fun v hv => hp₂ v (Or.inl hv),
        fun v hv => hp₁ v (Or.inl hv)⟩
  · exact hopt.2 ⟨C, Y ∪ {q}, hlarger,
      KiteTailBasics.ssubset_union_singleton hqY⟩

end Workspace.ProofLemmas.Thm224Claim7WheelTrichotomy
