import Workspace.ProofLemmas.PrismBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm211Hole

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- PAPER (21.1, printed p. 131): "Choose `h` with `1 ≤ h ≤ i` maximum
such that `x` is adjacent to `pₕ`, and choose `j` with `i + 3 ≤ j ≤ n`
minimum such that `x` is adjacent to `pⱼ`. Then `x-pₕ-⋯-pⱼ-x` is a hole
of length ≥ 6, say `C`, and `x, pᵢ, pᵢ₊₁, pᵢ₊₂, pᵢ₊₃` are all vertices
of it." The length bound uses that a Berge graph has no hole of length five. -/
theorem hole_through_gap {G : SimpleGraph V} (hG : Berge G)
    {p : List V} (hp : IsPathList G p) {i : ℕ}
    (hi : 1 ≤ i) (hin : i + 2 < p.length) {x : V} (hxp : x ∉ p)
    (hxfirst : G.Adj x p[0]) (hxlast : G.Adj x p[p.length - 1])
    (hxi : ¬ G.Adj x p[i]) (hxi1 : ¬ G.Adj x p[i + 1]) :
    ∃ C : List V, IsHoleList G C ∧ 6 ≤ holeLength C ∧ x ∈ C ∧
      (∀ v ∈ C, v = x ∨ v ∈ p) ∧
      (∀ k (hk : k < p.length), i - 1 ≤ k → k ≤ i + 2 → p[k] ∈ C) := by
  classical
  let pred : ℕ → Prop := fun k => ∃ hk : k < p.length, G.Adj x p[k]
  let a := Nat.findGreatest pred (i - 1)
  have ha : a ≤ i - 1 := Nat.findGreatest_le (i - 1)
  obtain ⟨hap, hxa⟩ : pred a := Nat.findGreatest_spec (m := 0)
    (n := i - 1) (Nat.zero_le _) ⟨by omega, hxfirst⟩
  have hex : ∃ k, i + 2 ≤ k ∧ pred k :=
    ⟨p.length - 1, by omega, by omega, hxlast⟩
  let b := Nat.find hex
  obtain ⟨hb, hbp, hxb⟩ : i + 2 ≤ b ∧ pred b := Nat.find_spec hex
  have hab : a < b := by omega
  have hxmid : ∀ k (hk : k < p.length), a < k → k < b → ¬ G.Adj x p[k] := by
    intro k hk hak hkb hadj
    by_cases hki : k ≤ i - 1
    · exact Nat.findGreatest_is_greatest (P := pred) (n := i - 1) hak hki ⟨hk, hadj⟩
    by_cases he : k = i
    · subst k
      exact hxi hadj
    by_cases he : k = i + 1
    · subst k
      exact hxi1 hadj
    exact Nat.find_min hex hkb ⟨by omega, hk, hadj⟩
  let q := (p.drop a).take (b - a + 1)
  have hq : IsPathFrom G q p[a] p[b] := PathBasics.isPathFrom_slice hp hab hbp
  have hqlen : q.length = b - a + 1 := PathBasics.length_slice p hab.le hbp
  have hqsub : ∀ v ∈ q, v ∈ p := by
    intro v hv
    exact List.drop_subset _ _ (List.take_subset _ _ hv)
  have hhole : IsHoleList G (x :: q) := PrismBasics.isHoleList_of_path_add_vertex hq
    (by simp only [pathLength, hqlen]; omega) hxa hxb (fun hx => hxp (hqsub x hx)) (by
      intro v hv
      obtain ⟨k, hk, hak, hkb, rfl⟩ := (PathBasics.mem_interior_slice_iff hp hab hbp).mp hv
      exact hxmid k hk hak hkb)
  have heven := hG.1 (x :: q) hhole
  have hlen6 : 6 ≤ holeLength (x :: q) := by
    simp only [holeLength, List.length_cons, hqlen, Nat.even_iff] at heven ⊢
    omega
  refine ⟨x :: q, hhole, hlen6, List.mem_cons_self, ?_, ?_⟩
  · intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · exact Or.inl he
    · exact Or.inr (hqsub v hv)
  · intro k hk hklo hkhi
    apply List.mem_cons_of_mem
    exact (PathBasics.mem_slice_iff p hab.le hbp).mpr ⟨k, hk, by omega, by omega, rfl⟩

end Workspace.ProofLemmas.Thm211Hole
