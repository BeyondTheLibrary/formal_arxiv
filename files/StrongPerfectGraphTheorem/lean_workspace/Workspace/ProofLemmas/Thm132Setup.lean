import Workspace.ProofLemmas.Thm132OptimalLength
import Workspace.Statements.S13.Thm_13_1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The canonical optimal configuration for 13.2

Starting from the first term which misses the original left end, this module
chooses the optimal replacement banister and its trajectory, and records all
the order information that the rest of the printed proof uses.
-/

namespace Workspace.ProofLemmas.Thm132Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132Reduction
open Workspace.ProofLemmas.Thm132Claim1
open Workspace.ProofLemmas.Thm132OptimalLength

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Data fixed after claim (1) in the printed proof. -/
structure FirstBadData (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V)
    (R₀ x : List V) (i : ℕ) where
  r : V
  R : List V
  birthIndex : ℕ
  birthIndex_lt : birthIndex < x.length
  optimal : BOptimalBanister G A C B x r R b₀
  birth_r : birth G A C B x r x[birthIndex]
  R_length_one : pathLength R = 1
  birth_before_bad : birthIndex < i
  w : List V
  trajectory : trajectoryOfVertex G A x r (r :: w)
  last : V
  trajectory_antipath : IsAntipathFrom G (r :: w) r last
  last_misses_A : ∃ a ∈ A, ¬ G.Adj last a
  before_last_A_complete : ∀ z ∈ w, z ≠ last → VertexComplete G z A
  w_indices : ∀ z ∈ w, ∃ (k : ℕ) (hk : k < x.length),
    k ≤ birthIndex ∧ x[k] = z
  w_B_complete : ∀ z ∈ w, VertexComplete G z B
  w_odd : Odd w.length
  a₀_complete_w : VertexComplete G a₀ {z : V | z ∈ w}

/-- Claim (1), finite minimisation, and 13.1 produce the canonical data above. -/
theorem exists_firstBadData
    {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (hx : IsRightSequence G A C B x)
    (i : ℕ) (hi : i < x.length)
    (hprev : ∀ (j : ℕ) (hj : j < i), G.Adj x[j] a₀)
    (hbad : ¬ G.Adj x[i] a₀) :
    Nonempty (FirstBadData G A C B a₀ b₀ R₀ x i) := by
  classical
  have hP : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have ha_not_complete : ¬ VertexComplete G a₀ {z : V | z ∈ x} := by
    intro hc
    exact hbad (hc x[i] (List.getElem_mem hi)).symm
  have ha_birth : birth G A C B x a₀ x[i] := by
    refine ⟨hP.2.2.1, ha_not_complete, i, hi, rfl, ?_, ?_⟩
    · exact fun hadj => hbad hadj.symm
    · intro k hk
      exact (hprev k hk).symm
  have hvstar := first_bad_isRightStar hG hK4 heven h1br h2br hK hx i hi hprev hbad
  have hnotopt := initial_banister_not_optimal hG hK4 heven h1br h2br hK hx
    i hi hprev hbad hvstar
  have hearlierCandidate : ∃ (a' : V) (R' : List V),
      IsBanister G A C B a' R' b₀ ∧
      ¬ VertexComplete G a' {z : V | z ∈ x} ∧
      ∃ u' u : V, birth G A C B x a' u' ∧
        birth G A C B x a₀ u ∧ Earlier x u' u := by
    by_contra hn
    exact hnotopt ⟨hP, ha_not_complete, hn⟩
  obtain ⟨r, R, j, hj, hopt, hbirth, hminimal⟩ :=
    exists_optimalBanister hx ⟨a₀, R₀, hP, ha_not_complete⟩

  -- The witness to non-optimality of the old banister is born before `x[i]`;
  -- the minimising banister is born no later than that witness.
  obtain ⟨a', R', hban', hanc', u', u, hbirth', hbirthOld, hearlier⟩ :=
    hearlierCandidate
  obtain ⟨p, hp, hpeq, hpnon, -⟩ := hbirth'.2.2
  obtain ⟨ep, eq, hep, heq, hepu, hequ, hepq⟩ := hearlier
  have hpep : p = ep := by
    apply (List.Nodup.getElem_inj_iff hx.1.1).mp
    exact hpeq.trans hepu.symm
  have hqi : eq = i := by
    obtain ⟨q, hq, hqeq, hqnon, -⟩ := hbirthOld.2.2
    have hqi' : q = i := birth_index_unique hx.1.1 hbirthOld ha_birth
      hq hi hqeq hqnon rfl (by simpa using (fun hadj => hbad hadj.symm))
    have heqq : eq = q := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      exact hequ.trans hqeq.symm
    omega
  have hpi : p < i := by omega
  have hji : j < i := lt_of_le_of_lt
    (hminimal a' R' p hp hban' hanc' (by simpa [hpeq] using hbirth')) hpi
  have hRone := optimal_banister_length_one hG hK4 heven h1br h2br hK hx hopt

  obtain ⟨w, q, hq, zidx, hzidx, htraj, hbirthQ, hanti, hwidx⟩ :=
    exists_trajectoryOfVertex_of_leftStar hK.1.1.1 hx hopt.1.2.2.1 hopt.2.1
  have hqj : q = j := by
    obtain ⟨q', hq', hq'eq, hq'non, -⟩ := hbirthQ.2.2
    have hq'q : q' = q :=
      (List.Nodup.getElem_inj_iff hx.1.1).mp hq'eq
    obtain ⟨j', hj', hj'eq, hj'non, -⟩ := hbirth.2.2
    have hj'j : j' = j :=
      (List.Nodup.getElem_inj_iff hx.1.1).mp hj'eq
    have hq'j' := birth_index_unique hx.1.1 hbirthQ hbirth
      hq' hj' hq'eq hq'non hj'eq hj'non
    omega
  subst q
  have hwidx' : ∀ z ∈ w, ∃ (k : ℕ) (hk : k < x.length),
      k ≤ j ∧ x[k] = z := by
    intro z hz
    exact hwidx z hz
  have ha₀W : VertexComplete G a₀ {z : V | z ∈ w} := by
    intro z hz
    obtain ⟨k, hk, hkj, hkz⟩ := hwidx' z hz
    have hki : k < i := lt_of_le_of_lt hkj hji
    simpa [hkz] using (hprev k hki).symm
  let wn : V := x[zidx]
  have hanti' : IsAntipathFrom G (r :: w) r wn := by
    simpa [wn] using hanti
  have htrajCopy := htraj
  obtain ⟨-, ti, hti, wt, -, hwtraj, hshape⟩ := htrajCopy
  have hwt : wt = w := by
    exact (List.cons.inj hshape).2.symm
  subst wt
  have hwpos : 0 < w.length := by
    have := hwtraj.1.1
    omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  obtain ⟨u, huLast, aLast, haLast, hlastmiss⟩ := hwtraj.2.1
  have hwnLast : w.getLast? = some wn := by
    have hc := hanti'.2.2
    simpa [List.getLast?_cons_of_ne_nil hwne] using hc
  have huwn : u = wn := by
    rw [huLast] at hwnLast
    exact Option.some.inj hwnLast
  have hlastA : ∃ a ∈ A, ¬ G.Adj wn a := by
    exact ⟨aLast, haLast, by simpa [huwn] using hlastmiss⟩
  have hbeforeA : ∀ z ∈ w, z ≠ wn → VertexComplete G z A := by
    intro z hz hzne
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
    have hklast : k ≠ w.length - 1 := by
      intro heq
      have hlastElem : w[w.length - 1]'(by omega) = wn :=
        PathBasics.getElem_last_of_getLast? hwnLast (by omega)
      subst k
      exact hzne (hkz.symm.trans hlastElem)
    have hkstep : k + 1 < w.length := by omega
    simpa [hkz] using (hwtraj.2.2 k hkstep).1
  have hwB : ∀ z ∈ w, VertexComplete G z B := by
    intro z hz
    obtain ⟨k, hk, -, hkz⟩ := hwidx' z hz
    simpa [hkz] using hx.1.2 x[k] (List.getElem_mem hk)
  have h13 := Workspace.Statements.S13.SPGT.thm_13_1 G hG hK4 heven h1br h2br
    A C B a₀ b₀ R₀ hK x hx b₀ hK.1.1.2.1.2.2.2.1 r R hopt w htraj
  exact ⟨{
    r := r
    R := R
    birthIndex := j
    birthIndex_lt := hj
    optimal := hopt
    birth_r := hbirth
    R_length_one := hRone
    birth_before_bad := hji
    w := w
    trajectory := htraj
    last := wn
    trajectory_antipath := hanti'
    last_misses_A := hlastA
    before_last_A_complete := hbeforeA
    w_indices := hwidx'
    w_B_complete := hwB
    w_odd := h13.1
    a₀_complete_w := ha₀W
  }⟩

end Workspace.ProofLemmas.Thm132Setup
