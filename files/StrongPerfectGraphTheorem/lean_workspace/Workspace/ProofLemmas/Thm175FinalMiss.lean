import Workspace.ProofLemmas.Thm175FinalParity
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.Thm203AntipathTools

/-! The first missed vertex is `x₂`, in the last paragraph of 17.5. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Workspace.ProofLemmas.Thm175FinalMiss

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm175Optimal Workspace.ProofLemmas.Thm175Claims
open Workspace.ProofLemmas.Thm175FinalBlocks Workspace.ProofLemmas.Thm175FinalParity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "Choose `s₀` ... minimum such that `p_h` is nonadjacent to `x_{s₀}`.
So `p_j-x₁-...-x_{s₀}-p_h-p_j` is an antihole, and so `s₀` is even.
Hence `x₁-...-x_{s₀}-p_h-z` is an odd antipath ... by 13.6 it has length 3,
that is, `s₀=2`." -/
theorem second_missed {G : SimpleGraph V} (hG : InF7 G) {z : V}
    (c : Counterexample G z)
    (hfirst : ∀ w ∈ c.core.p, VertexComplete G w c.X ↔ w = c.core.p₁)
    (b : AntipathBlocks G c.X c.Y) (last : LastNeighborContext c b)
    (h5 : 0 < last.h) (j : ℕ) (hj : j < c.core.p.length)
    (hjh : last.h + 1 < j)
    (hjX : VertexComplete G (c.core.p[j]'hj) (c.X \ {b.x₁})) :
    ¬ G.Adj (c.core.p[last.h]'last.hlt) (b.qX[1]'b.hXlong) := by
  classical
  let ph := c.core.p[last.h]'last.hlt
  let pj := c.core.p[j]'hj
  have hphP : ph ∈ c.core.p := List.getElem_mem _
  have hpjP : pj ∈ c.core.p := List.getElem_mem _
  have hxX : b.x₁ ∈ c.X := (b.hXverts _).mp (PathBasics.head_mem b.hxhead)
  have hxq : b.x₁ ∈ b.qX := PathBasics.head_mem b.hxhead
  have hqpath : IsPathList Gᶜ b.qX := by
    have h := PathBasics.isPathList_take b.hanti.1 (k := b.qX.length) (by have := b.hXlong; omega)
    simpa using h
  have hq0 : b.qX[0]'(by have := b.hXlong; omega) = b.x₁ :=
    PathBasics.getElem_zero_of_head? b.hxhead _
  have hnotX : ¬ VertexComplete G ph c.X := by
    intro hc
    exact last_not_complete c hfirst b last h5 (fun v hv => hc v hv.1)
  have hex : ∃ k, ∃ hk : k < b.qX.length, ¬ G.Adj ph (b.qX[k]'hk) := by
    by_contra hn
    apply hnotX
    intro v hv
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem ((b.hXverts v).mpr hv)
    by_contra hnv
    exact hn ⟨k, hk, he ▸ hnv⟩
  obtain ⟨k, hk, hmiss, hbefore⟩ :
      ∃ k, ∃ hk : k < b.qX.length, ¬ G.Adj ph (b.qX[k]'hk) ∧
        ∀ i (hi : i < k), G.Adj ph (b.qX[i]'(lt_trans hi hk)) := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
    intro i hi
    by_contra hno
    have hle := Nat.find_min' hex ⟨lt_trans hi (Nat.find_spec hex).1, hno⟩
    omega
  have hkpos : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    subst k
    rw [hq0] at hmiss
    exact hmiss last.hadj.symm
  let q := b.qX.take (k+1)
  have hqFrom : IsAntipathFrom G q b.x₁ (b.qX[k]'hk) := by
    have h := PathBasics.isPathFrom_slice hqpath hkpos hk
    simpa only [List.drop_zero, Nat.sub_zero, hq0] using h
  have hqsub (v : V) (hv : v ∈ q) : v ∈ c.X :=
    (b.hXverts v).mp (List.take_subset _ _ hv)
  have hphq : ph ∉ q := fun h => c.core.houtX ph hphP (hqsub ph h)
  have hphlast : Gᶜ.Adj ph (b.qX[k]'hk) := by
    exact (SimpleGraph.compl_adj _ _ _).mpr
      ⟨fun he => c.core.houtX ph hphP (he ▸ (b.hXverts _).mp (List.getElem_mem _)), hmiss⟩
  let Q := q ++ [ph]
  have hQ : IsAntipathFrom G Q b.x₁ ph := by
    apply PathAttach.isPathFrom_concat hqFrom hphlast hphq
    intro v hv hne hadj
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hv
    have hik : i ≤ k := by have := hi; simp only [q, List.length_take] at this; omega
    have hiq : i < b.qX.length := by omega
    have he' : b.qX[i]'hiq = v := by simpa only [q, List.getElem_take] using he
    have hine : i ≠ k := by intro heq; subst i; exact hne he'.symm
    exact ((SimpleGraph.compl_adj _ _ _).mp hadj).2 (he' ▸ hbefore i (by omega))
  have hQmem (v : V) (hv : v ∈ Q) : v ∈ q ∨ v = ph := by simpa only [Q, List.mem_append, List.mem_singleton] using hv
  have hQint : ∀ v ∈ SPGT.interior Q, v ∈ c.X \ {b.x₁} := by
    intro v hv
    obtain ⟨hvQ, hvx, hvph⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hv
    rcases hQmem v hvQ with hvq | he
    · exact ⟨hqsub v hvq, hvx⟩
    · exact (hvph he).elim
  have hpjx : ¬ G.Adj pj b.x₁ := by
    intro ha
    have hle := last.hmax j hj ha.symm
    omega
  have hpjph : ¬ G.Adj pj ph :=
    PathBasics.path_not_adj_of_gap c.core.hp.1 hj last.hlt (by omega) (by omega)
  have hpjnex : pj ≠ b.x₁ := fun he => c.core.houtX pj hpjP (he ▸ hxX)
  have hpjneph : pj ≠ ph := by
    intro he
    have := c.core.hp.1.2.1.getElem_inj_iff.mp he
    omega
  have hQeven : Even (pathLength Q) :=
    AntiholeCompletion.even_pathLength_of_witness hG.1.1.1.1 last.hadj
      hjX hpjx hpjph hpjnex hpjneph hQ hQint
  have hzq : z ∉ q := fun hzq => c.hz (Or.inl (hqsub z hzq))
  have hzneph : z ≠ ph := fun he => c.core.hzP
    (List.mem_iff_getElem.mpr ⟨last.h, last.hlt, he.symm⟩)
  have hzph : Gᶜ.Adj z ph :=
    (SimpleGraph.compl_adj _ _ _).mpr ⟨hzneph, c.core.hzanti ph hphP⟩
  have hzQ : z ∉ Q := by
    intro hzQ
    rcases hQmem z hzQ with hzq' | he
    · exact hzq hzq'
    · exact hzneph he
  have hQz : IsAntipathFrom G (Q ++ [z]) b.x₁ z := by
    apply PathAttach.isPathFrom_concat hQ hzph hzQ
    intro v hv hvph ha
    rcases hQmem v hv with hvq | he
    · exact ((SimpleGraph.compl_adj _ _ _).mp ha).2 (c.hzXY v (Or.inl (hqsub v hvq)))
    · exact hvph he
  have hqlen : q.length = k+1 := by simp only [q, List.length_take]; omega
  have hQlen : Q.length = k+2 := by simp only [Q, List.length_append, List.length_singleton, hqlen]
  have hQzodd : Odd (pathLength (Q ++ [z])) := by
    simp only [pathLength, List.length_append, List.length_singleton, hQlen] at hQeven ⊢
    exact hQeven.add_odd (by decide : Odd 1)
  let T : Set V := {v | v ∈ c.core.p.drop (last.h+1)}
  have hTcon : ConnectedSet G T :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isChain
      ((InducedPathExtraction.isChain_of_isPathList c.core.hp.1).drop _)
  have hTP (v : V) (hv : v ∈ T) : v ∈ c.core.p := List.drop_subset _ _ hv
  have hphT : ph ∉ T := by
    intro hv
    obtain ⟨i, hi, hhi, he⟩ := (mem_drop_iff _ _ _).mp hv
    have := c.core.hp.1.2.1.getElem_inj_iff.mp he
    omega
  have hQT : ∀ v ∈ Q ++ [z], v ∉ T := by
    intro v hv hvT
    rcases List.mem_append.mp hv with hvQ | hvz
    · rcases hQmem v hvQ with hvq | he
      · exact c.core.houtX v (hTP v hvT) (hqsub v hvq)
      · exact hphT (he ▸ hvT)
    · have he : v = z := by simpa using hvz
      exact c.core.hzP (he ▸ hTP v hvT)
  have hxT : ∀ v ∈ T, ¬ G.Adj b.x₁ v := by
    intro v hv ha
    obtain ⟨i, hi, hhi, he⟩ := (mem_drop_iff _ _ _).mp hv
    have hle := last.hmax i hi (he ▸ ha)
    omega
  have hzT : ∀ v ∈ T, ¬ G.Adj z v := fun v hv => c.core.hzanti v (hTP v hv)
  have hjT : pj ∈ T := (mem_drop_iff _ _ _).mpr ⟨j, hj, by omega, rfl⟩
  have hintT : ∀ v ∈ SPGT.interior (Q ++ [z]), ∃ a ∈ T, G.Adj v a := by
    intro v hv
    obtain ⟨hvQz, hvx, hvz⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQz).mp hv
    rcases List.mem_append.mp hvQz with hvQ | hvz'
    · rcases hQmem v hvQ with hvq | he
      · exact ⟨pj, hjT, (hjX v ⟨hqsub v hvq, hvx⟩).symm⟩
      · subst v
        have hnext : last.h + 1 < c.core.p.length := by omega
        exact ⟨_, (mem_drop_iff _ _ _).mpr ⟨last.h+1, hnext, le_rfl, rfl⟩,
          PathBasics.path_adj_succ c.core.hp.1 hnext⟩
    · exact (hvz (by simpa using hvz')).elim
  have hlen := Thm203AntipathTools.antipath_length_three_of_odd hG.1.1
    hTcon hQz hQzodd (c.hzXY b.x₁ (Or.inl hxX)).symm hQT hxT hzT hintT
  have hk1 : k = 1 := by
    simp only [pathLength, List.length_append, List.length_singleton, hQlen] at hlen
    omega
  subst k
  exact hmiss

end Workspace.ProofLemmas.Thm175FinalMiss
