import Workspace.ProofLemmas.Thm84K4CaseGeometry
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.Statements.S08.Thm_8_1

/-! # Rung notation for the last paragraph of 8.4 -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84K4CaseRungs

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.StripSystems.SPGT

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}
  {S : U → U → Set V} {N : U → Set V} {R : U → U → List V} {r : U → U → V}

/-- The notation `r_uv` for the first end of a rung, with the last end named `r_vu`.
The two membership fields retain the uniqueness clauses in the definition of a rung. -/
structure Ends (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (R : U → U → List V)
    (r : U → U → V) : Prop where
  path : ∀ u v, J.Adj u v → IsPathFrom G (R u v) (r u v) (r v u)
  sub : ∀ u v, J.Adj u v → ∀ x ∈ R u v, x ∈ S u v
  first : ∀ u v, J.Adj u v → ∀ x ∈ R u v, x ∈ N u ↔ x = r u v
  last : ∀ u v, J.Adj u v → ∀ x ∈ R u v, x ∈ N v ↔ x = r v u

theorem exists_ends (y : V)
    (hR : ∀ u v, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hsym : ∀ u v, J.Adj u v → R v u = (R u v).reverse) :
    ∃ r, Ends G J S N R r := by
  classical
  letI : Nonempty V := ⟨y⟩
  have hex : ∀ u v, J.Adj u v → ∃ s : V, (R u v).head? = some s := by
    intro u v huv
    obtain ⟨-, s, t, hp, -⟩ := hR u v huv
    exact ⟨s, hp.2.1⟩
  choose! r hr using hex
  have hends : ∀ u v, J.Adj u v → ∀ s t,
      IsPathFrom G (R u v) s t → s = r u v ∧ t = r v u := by
    intro u v huv s t hp
    have hlast := hr v u huv.symm
    rw [hsym u v huv, List.head?_reverse] at hlast
    exact ⟨Option.some_injective _ (hp.2.1.symm.trans (hr u v huv)),
      Option.some_injective _ (hp.2.2.symm.trans hlast)⟩
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨-, s, t, hp, -⟩ := hR u v huv
    obtain ⟨hs, ht⟩ := hends u v huv s t hp
    rwa [hs, ht] at hp
  · intro u v huv
    exact StripSystemBasics.rung_subset_strip (hR u v huv)
  · intro u v huv x hx
    obtain ⟨-, s, t, hp, -, hf, -⟩ := hR u v huv
    rw [← (hends u v huv s t hp).1]
    exact hf x hx
  · intro u v huv x hx
    obtain ⟨-, s, t, hp, -, -, hl⟩ := hR u v huv
    rw [← (hends u v huv s t hp).2]
    exact hl x hx

theorem Ends.head_mem (h : Ends G J S N R r) {u v : U} (huv : J.Adj u v) :
    r u v ∈ R u v := PathBasics.head_mem (h.path u v huv).2.1

theorem Ends.last_mem (h : Ends G J S N R r) {u v : U} (huv : J.Adj u v) :
    r v u ∈ R u v := PathBasics.getLast_mem (h.path u v huv).2.2

theorem Ends.head_N (h : Ends G J S N R r) {u v : U} (huv : J.Adj u v) :
    r u v ∈ N u := (h.first u v huv _ (h.head_mem huv)).mpr rfl

theorem Ends.head_strip (h : Ends G J S N R r) {u v : U} (huv : J.Adj u v) :
    r u v ∈ S u v := h.sub u v huv _ (h.head_mem huv)

theorem Ends.zero_iff (h : Ends G J S N R r) {u v : U} (huv : J.Adj u v) :
    pathLength (R u v) = 0 ↔ r u v = r v u := by
  have hp := h.path u v huv
  have hpos := PathBasics.path_length_pos hp.1
  constructor
  · intro hz
    have hl : (R u v).length = 1 := by simp only [pathLength] at hz; omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
    rw [hx] at hp
    have h1 : x = r u v := by simpa using hp.2.1
    have h2 : x = r v u := by simpa using hp.2.2
    exact h1.symm.trans h2
  · intro he
    have h0 := PathBasics.getElem_zero_of_head? hp.2.1 hpos
    have hn := PathBasics.getElem_last_of_getLast? hp.2.2 hpos
    have hh := hp.1.2.1.getElem_inj_iff.mp (h0.trans (he.trans hn.symm))
    simp only [pathLength]
    omega

theorem Ends.disjoint (h : Ends G J S N R r) (hSN : IsJStripSystem G J S N)
    {u v w z : U} (huv : J.Adj u v) (hwz : J.Adj w z)
    (hne : s(u, v) ≠ s(w, z)) : ∀ x ∈ R u v, x ∉ R w z := by
  intro x hx hx'
  exact Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN huv hwz hne)
    (h.sub u v huv x hx) (h.sub w z hwz x hx')

/-- The only edge between two rungs with a common first end is the triangle edge. -/
theorem Ends.cross (h : Ends G J S N R r) (hSN : IsJStripSystem G J S N)
    {u v w : U} (huv : J.Adj u v) (huw : J.Adj u w) (hvw : v ≠ w) :
    ∀ x ∈ R u v, ∀ z ∈ R u w, G.Adj x z ↔ x = r u v ∧ z = r u w := by
  intro x hx z hz
  constructor
  · intro hxz
    obtain ⟨hxN, hzN⟩ := StripSystemBasics.mem_N_of_adj hSN huv huw hvw
      (h.sub u v huv _ hx) (h.sub u w huw _ hz) hxz
    exact ⟨(h.first u v huv _ hx).mp hxN, (h.first u w huw _ hz).mp hzN⟩
  · rintro ⟨hx', hz'⟩
    exact StripSystemBasics.Nuv_complete hSN huv huw hvw x
      ⟨(h.first u v huv _ hx).mpr hx', h.sub u v huv _ hx⟩ z
      ⟨(h.first u w huw _ hz).mpr hz', h.sub u w huw _ hz⟩

/-- Two lists representing the same oriented rung have the same named first end. -/
theorem head_eq_of_eq {R' : U → U → List V} {r' : U → U → V}
    (h : Ends G J S N R r) (h' : Ends G J S N R' r')
    {u v : U} (huv : J.Adj u v) (heq : R u v = R' u v) : r u v = r' u v := by
  have hh := (h.path u v huv).2.1
  rw [heq, (h'.path u v huv).2.1] at hh
  exact (Option.some_injective _ hh).symm

section Parity
variable [Fintype V] [DecidableEq V] [Fintype U]

/-- The last strip-system axiom applies to every rung choice by 8.1. -/
theorem cycle_parity (hG : Berge G) (hJ : IsKConnected J 3)
    (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v, J.Adj u v → IsUVRung G J S N u v (R u v))
    (c : List U) (hlen : 3 ≤ c.length) (hnd : c.Nodup)
    (hadj : ∀ p ∈ c.zip (c.rotate 1), J.Adj p.1 p.2) :
    ((c.zip (c.rotate 1)).map (fun p => pathLength (R p.1 p.2))).sum
      ≡ c.length [MOD 2] := by
  obtain ⟨R₀, hR₀, hcycle₀⟩ := StripSystemBasics.exists_special_rungs hSN
  apply (Nat.ModEq.listSum_map (l := c.zip (c.rotate 1))
    (f := fun p => pathLength (R p.1 p.2))
    (g := fun p => pathLength (R₀ p.1 p.2)) ?_).trans (hcycle₀ c hlen hnd hadj)
  intro p hp
  have hh := _root_.Workspace.Statements.S08.SPGT.thm_8_1
    G hG J hJ S N hSN p.1 p.2 (hadj p hp) _ _
      (hR p.1 p.2 (hadj p hp)) (hR₀ p.1 p.2 (hadj p hp))
  rw [Nat.even_iff, Nat.even_iff] at hh
  change pathLength (R p.1 p.2) % 2 = pathLength (R₀ p.1 p.2) % 2
  omega

/-- The three rung lengths around a triangle have odd sum. -/
theorem triangle_parity (hG : Berge G) (hJ : IsKConnected J 3)
    (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v, J.Adj u v → IsUVRung G J S N u v (R u v))
    {a b c : U} (hab : J.Adj a b) (hbc : J.Adj b c) (hca : J.Adj c a) :
    Odd (pathLength (R a b) + pathLength (R b c) + pathLength (R c a)) := by
  have hnd : [a, b, c].Nodup := by simp [hab.ne, hbc.ne, hca.ne']
  have hh := cycle_parity hG hJ hSN hR [a, b, c] (by simp) hnd (by
    intro p hp
    simp [List.rotate_cons_succ] at hp
    rcases hp with rfl | rfl | rfl
    · exact hab
    · exact hbc
    · exact hca)
  simp [List.rotate_cons_succ, Nat.ModEq, Nat.odd_iff, Nat.add_mod] at hh ⊢
  omega

end Parity
end Workspace.ProofLemmas.Thm84K4CaseRungs
