import Workspace.ProofLemmas.Thm132Claim5
import Workspace.ProofLemmas.Thm132Optimal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # The second optimal banister in the endgame of 13.2. -/

namespace Workspace.ProofLemmas.Thm132SecondBanister

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.ProofLemmas.Thm132Setup
open Workspace.ProofLemmas.Thm132Optimal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A right-star which is the sole term of the first trajectory has an
optimal banister whose left end is born strictly before the first left end. -/
theorem exists_second_optimal
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V} {i : ℕ}
    (hx : IsRightSequence G A C B x)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hlast : IsRightStar G A C B d.last)
    (hwone : d.w.length = 1) :
    ∃ (r' : V) (R' : List V) (j : ℕ) (hj : j < x.length),
      BOptimalBanister G A C B x r' R' d.last ∧
      birth G A C B x r' x[j] ∧ j < d.birthIndex := by
  classical
  have hwne : d.w ≠ [] := by rw [List.ne_nil_iff_length_pos, hwone]; omega
  have hlastMem : d.last ∈ d.w := by
    have hc := d.trajectory_antipath.2.2
    have hc' : d.w.getLast? = some d.last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using hc
    exact PathBasics.getLast_mem hc'
  obtain ⟨k, hk, hkBirth, hkLast⟩ := d.w_indices d.last hlastMem
  have hantiA : VertexAnticomplete G x[k] A := by
    intro z hz
    simpa [hkLast] using hlast.2.2 z (Or.inl hz)
  obtain ⟨a, P, hP, y, hy, hay⟩ := hx.2.2 k hk hantiA
  have haNot : ¬ VertexComplete G a {z : V | z ∈ x} := by
    intro hac
    exact hay (hac y (List.mem_of_mem_take hy))
  obtain ⟨a', P', j, hj, hopt, hbirth, hminimal⟩ :=
    exists_optimalBanister hx ⟨a, P, hP, haNot⟩
  obtain ⟨ℓ, hℓ, hℓy⟩ := List.mem_iff_getElem.mp hy
  have hℓk : ℓ < k := by
    have := hℓ
    rw [List.length_take] at this
    omega
  have hℓx : ℓ < x.length := by omega
  have hℓval : x[ℓ] = y := by
    exact List.getElem_take.symm.trans hℓy
  have hnonℓ : ¬ G.Adj a x[ℓ] := by simpa [hℓval] using hay
  obtain ⟨p, hp, hpBirth⟩ := exists_birth hP.2.2.1 haNot
  obtain ⟨p', hp', hpval, hpnon, hpBefore⟩ := hpBirth.2.2
  have hpp : p' = p := by
    exact (List.Nodup.getElem_inj_iff hx.1.1 (hi := hp') (hj := hp)).mp hpval
  subst p'
  have hpℓ : p ≤ ℓ := by
    by_contra hn
    exact hnonℓ (hpBefore ℓ (by omega))
  have hjp : j ≤ p := hminimal a P p hp hP haNot hpBirth
  refine ⟨a', P', j, hj, ?_, ?_, ?_⟩
  · simpa [hkLast] using hopt
  · simpa [hkLast] using hbirth
  omega

end Workspace.ProofLemmas.Thm132SecondBanister
