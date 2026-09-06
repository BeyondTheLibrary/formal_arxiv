import Workspace.ProofLemmas.HoleBasics

/-!
# Bergeness of an explicit finite graph, by a `2`-regular subset check

A hole is a `2`-regular induced subgraph.  So if no odd-sized vertex subset of size `≥ 5` has
every one of its vertices with exactly two neighbours inside it, then no hole has odd length.
For a graph given explicitly on `Fin n` the second condition is a finite check that `decide`
discharges; connectivity of the subset is never needed, which is what keeps the check cheap.

Both lemmas are stated for an arbitrary finite graph, so they serve any explicit example.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.BergeTwoRegularCriterion

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

/-- In a hole, every vertex has **exactly two** neighbours among the hole's own vertices:
its cyclic successor `c[(i+1) % n]` and its cyclic predecessor `c[(i + (n-1)) % n]`. -/
theorem hole_deg_two {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] {c : List W} (h : IsHoleList G c)
    {i : ℕ} (hi : i < c.length) :
    (c.toFinset.filter (fun w => G.Adj ((c)[i]'hi) w)).card = 2 := by
  have h4 : 4 ≤ c.length := h.1
  have hn : 0 < c.length := by omega
  have hp : (i + 1) % c.length < c.length := Nat.mod_lt _ hn
  have hq : (i + (c.length - 1)) % c.length < c.length := Nat.mod_lt _ hn
  -- the cyclic predecessor's successor index is `i`
  have hqsucc : ((i + (c.length - 1)) % c.length + 1) % c.length = i := by
    rw [Nat.mod_add_mod]
    have he : i + (c.length - 1) + 1 = i + c.length := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  -- the two cyclic neighbours sit at distinct indices
  have hpq : (i + 1) % c.length ≠ (i + (c.length - 1)) % c.length := by
    intro hcon
    have h1 : (1 : ℕ) % c.length = (c.length - 1) % c.length :=
      Nat.ModEq.add_left_cancel' i hcon
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hset : c.toFinset.filter (fun w => G.Adj ((c)[i]'hi) w)
      = {(c)[(i + 1) % c.length]'hp, (c)[(i + (c.length - 1)) % c.length]'hq} := by
    ext w
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hwc, hadj⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hwc
      rcases (HoleBasics.hole_adj_iff h hi hj).mp hadj with hj1 | hj2
      · exact Or.inl ((List.Nodup.getElem_inj_iff h.2.1).mpr hj1)
      · refine Or.inr ((List.Nodup.getElem_inj_iff h.2.1).mpr ?_)
        rcases Nat.lt_or_ge (j + 1) c.length with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hj2
          have hji : i + (c.length - 1) = j + c.length := by omega
          rw [hji, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
        · have hjn : j + 1 = c.length := by omega
          rw [hjn, Nat.mod_self] at hj2
          subst hj2
          have hz : 0 + (c.length - 1) = c.length - 1 := by omega
          rw [hz, Nat.mod_eq_of_lt (by omega)]
          omega
    · have hadjp : G.Adj ((c)[i]'hi) ((c)[(i + 1) % c.length]'hp) :=
        (HoleBasics.hole_adj_iff h hi hp).mpr (Or.inl rfl)
      have hadjq : G.Adj ((c)[i]'hi) ((c)[(i + (c.length - 1)) % c.length]'hq) :=
        (HoleBasics.hole_adj_iff h hi hq).mpr (Or.inr hqsucc.symm)
      rintro (rfl | rfl)
      · exact ⟨List.getElem_mem _, hadjp⟩
      · exact ⟨List.getElem_mem _, hadjq⟩
  rw [hset, Finset.card_pair (HoleBasics.hole_ne_of_ne_index h hp hq hpq)]

/-- If no odd-sized subset of size `≥ 5` is `2`-regular, then every hole has even length. -/
theorem even_of_no_odd_two_regular {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hcheck : ∀ S : Finset W, 5 ≤ S.card → S.card % 2 = 1 →
      ∃ v ∈ S, (S.filter (fun w => G.Adj v w)).card ≠ 2)
    (c : List W) (h : IsHoleList G c) : Even (holeLength c) := by
  by_contra hodd
  have h4 : 4 ≤ c.length := h.1
  have hcard : c.toFinset.card = c.length := List.toFinset_card_of_nodup h.2.1
  have hmod : c.length % 2 = 1 := Nat.not_even_iff.mp hodd
  obtain ⟨v, hv, hne⟩ := hcheck c.toFinset (by omega) (by omega)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hv)
  exact hne (hole_deg_two h hi)


end Workspace.ProofLemmas.BergeTwoRegularCriterion
