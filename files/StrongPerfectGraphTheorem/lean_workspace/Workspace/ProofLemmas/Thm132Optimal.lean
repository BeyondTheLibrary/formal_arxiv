import Workspace.ProofLemmas.Thm132Infrastructure

set_option autoImplicit false

/-!
# Finite optimal choices for §13.2

The paper repeatedly says that a banister can be chosen `b`-optimal.  This is
just minimisation of the index of its left end's birth in the finite
right-sequence; the lemmas below spell out that choice.
-/

namespace Workspace.ProofLemmas.Thm132Optimal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The index occurring in the definition of the birth of a fixed left-star is
unique. -/
theorem birth_index_unique {G : SimpleGraph V} {A C B : Set V} {x : List V}
    (hx : x.Nodup) {a u v : V} (hu : birth G A C B x a u) (hv : birth G A C B x a v)
    {i j : ℕ} (hi : i < x.length) (hj : j < x.length)
    (hiu : x[i] = u) (hiv : ¬ G.Adj a x[i])
    (hju : x[j] = v) (hjv : ¬ G.Adj a x[j]) : i = j := by
  obtain ⟨_, _, i', hi', hi'u, hi'non, hbeforei⟩ := hu
  obtain ⟨_, _, j', hj', hj'v, hj'non, hbeforej⟩ := hv
  have hii : i' = i := by
    apply (List.Nodup.getElem_inj_iff hx).mp
    exact hi'u.trans hiu.symm
  have hjj : j' = j := by
    apply (List.Nodup.getElem_inj_iff hx).mp
    exact hj'v.trans hju.symm
  subst i'
  subst j'
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd (hbeforej i hij) hiv
  · exact hij
  · exact absurd (hbeforei j hij) hjv

/-- A non-`X`-complete left-star has a birth. -/
theorem exists_birth {G : SimpleGraph V} {A C B : Set V} {x : List V} {a : V}
    (ha : IsLeftStar G A C B a)
    (hanc : ¬ VertexComplete G a {v : V | v ∈ x}) :
    ∃ (i : ℕ) (hi : i < x.length), birth G A C B x a x[i] := by
  classical
  have hex : ∃ i : ℕ, ∃ hi : i < x.length, ¬ G.Adj a (x[i]'hi) := by
    rw [VertexComplete] at hanc
    push_neg at hanc
    obtain ⟨v, hv, hnav⟩ := hanc
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hv
    exact ⟨i, hi, by simpa [hiv] using hnav⟩
  set P : ℕ → Prop := fun i => ∃ hi : i < x.length, ¬ G.Adj a (x[i]'hi)
  have hP : ∃ i, P i := hex
  obtain ⟨hi, hni⟩ := Nat.find_spec hP
  set i := Nat.find hP
  have hbefore : ∀ k : ℕ, k < i → ∀ hk : k < x.length, G.Adj a (x[k]'hk) := by
    intro k hki hk
    have hn := Nat.find_min hP hki
    by_contra hc
    exact hn ⟨hk, hc⟩
  refine ⟨i, hi, ha, hanc, i, hi, rfl, hni, ?_⟩
  intro k hk
  exact hbefore k hk (by omega)

/-- Among all banisters ending in `b` whose left end is not complete to the
right-sequence, one has minimum birth index and is therefore `b`-optimal.  The
minimum-index clause is retained for later comparisons. -/
theorem exists_optimalBanister
    {G : SimpleGraph V} {A C B : Set V} {x : List V} {b : V}
    (hx : IsRightSequence G A C B x)
    (hex : ∃ (a : V) (R : List V), IsBanister G A C B a R b ∧
      ¬ VertexComplete G a {v : V | v ∈ x}) :
    ∃ (a : V) (R : List V) (i : ℕ) (hi : i < x.length),
      BOptimalBanister G A C B x a R b ∧ birth G A C B x a x[i] ∧
      ∀ (a' : V) (R' : List V) (j : ℕ) (hj : j < x.length),
        IsBanister G A C B a' R' b →
        ¬ VertexComplete G a' {v : V | v ∈ x} →
        birth G A C B x a' x[j] → i ≤ j := by
  classical
  have hcand : ∃ i : ℕ, ∃ hi : i < x.length, ∃ (a : V) (R : List V),
      IsBanister G A C B a R b ∧
      ¬ VertexComplete G a {v : V | v ∈ x} ∧ birth G A C B x a x[i] := by
    obtain ⟨a, R, hban, hanc⟩ := hex
    obtain ⟨i, hi, hbirth⟩ := exists_birth hban.2.2.1 hanc
    exact ⟨i, hi, a, R, hban, hanc, hbirth⟩
  set P : ℕ → Prop := fun i => ∃ hi : i < x.length, ∃ (a : V) (R : List V),
    IsBanister G A C B a R b ∧
    ¬ VertexComplete G a {v : V | v ∈ x} ∧ birth G A C B x a x[i]
  have hP : ∃ i, P i := hcand
  obtain ⟨hi, a, R, hban, hanc, hbirth⟩ := Nat.find_spec hP
  set i := Nat.find hP
  have hminimal : ∀ j : ℕ, j < i → ¬ P j := by
    intro j hj
    exact Nat.find_min hP hj
  have hle : ∀ (a' : V) (R' : List V) (j : ℕ) (hj : j < x.length),
      IsBanister G A C B a' R' b →
      ¬ VertexComplete G a' {v : V | v ∈ x} →
      birth G A C B x a' x[j] → i ≤ j := by
    intro a' R' j hj hban' hanc' hbirth'
    by_contra hnle
    have hji : j < i := by omega
    exact hminimal j hji ⟨hj, a', R', hban', hanc', hbirth'⟩
  refine ⟨a, R, i, hi, ?_, hbirth, hle⟩
  refine ⟨hban, hanc, ?_⟩
  rintro ⟨a', R', hban', hanc', u', u, hbirth', hbirthCur, hearliers⟩
  obtain ⟨j, hj, hju, hjnon, -⟩ := hbirth'.2.2
  obtain ⟨k, hk, hku, hknon, -⟩ := hbirthCur.2.2
  obtain ⟨ib, hib, hibx, hibnon, -⟩ := hbirth.2.2
  have hki : k = i := birth_index_unique hx.1.1 hbirthCur hbirth hk hi hku hknon rfl
    (by simpa [hibx] using hibnon)
  obtain ⟨p, q, hp, hq, hpu, hqu, hpq⟩ := hearliers
  have hpj : p = j := by
    apply (List.Nodup.getElem_inj_iff hx.1.1).mp
    calc
      x[p] = u' := hpu
      _ = x[j] := hju.symm
  have hqk : q = k := by
    apply (List.Nodup.getElem_inj_iff hx.1.1).mp
    calc
      x[q] = u := hqu
      _ = x[k] := hku.symm
  have hji : j < i := by omega
  exact hminimal j hji ⟨hj, a', R', hban', hanc', by simpa [hju] using hbirth'⟩

end Workspace.ProofLemmas.Thm132Optimal
