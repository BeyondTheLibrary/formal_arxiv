import Workspace.ProofLemmas.Thm61Claim12Common

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm61Claim12SixVertices

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.SubdivisionCounting

/-- A vertex outside the branch vertices has no third neighbour. -/
theorem neighbor_of_not_branch {W : Type*} [Finite W] {H : SimpleGraph W}
    {x a b w : W} (hx : x ∉ branchVertices H) (hab : a ≠ b)
    (ha : H.Adj x a) (hb : H.Adj x b) (hw : H.Adj x w) : w = a ∨ w = b := by
  by_contra hn
  push Not at hn
  apply hx
  change 3 ≤ (H.neighborSet x).ncard
  have hs : ({a, b, w} : Set W) ⊆ H.neighborSet x := by
    intro y hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hc : ({a, b, w} : Set W).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, w, hab, hn.1.symm, hn.2.symm, rfl⟩
  have hle := Set.ncard_le_ncard hs (Set.toFinite _)
  omega

/-- The fourth outcome in the sentence "If `v = b₃`, then `B₃` has length 2 and both its
edges belong to `X`, and the fourth outcome of the theorem holds." The four branch vertices
form a four-cycle, and its two missing edges are each subdivided once. -/
theorem six_vertex_k4
    {m n : ℕ} (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (H : SimpleGraph (Fin n)) (hsub : IsSubdivision J H)
    {b b₁ b₂ b₃ u z : Fin n}
    (hnd : [b, b₁, b₂, b₃, u, z].Nodup)
    (hB : IsBranch H [b, z, b₃])
    (h01 : H.Adj b b₁) (h02 : H.Adj b b₂)
    (h13 : H.Adj b₁ b₃) (h23 : H.Adj b₂ b₃)
    (h1u : H.Adj b₁ u) (h2u : H.Adj b₂ u)
    (h0z : H.Adj b z) (h3z : H.Adj b₃ z)
    (hd0 : (H.neighborSet b).ncard = 3)
    (hd1 : (H.neighborSet b₁).ncard = 3)
    (hd2 : (H.neighborSet b₂).ncard = 3)
    (hd3 : (H.neighborSet b₃).ncard = 3) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ Fintype.card (Fin n) = 6 := by
  classical
  have hne := hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
    List.nodup_nil, and_true] at hne
  have hbV : b ∈ branchVertices H := by change 3 ≤ _; omega
  have hb₁V : b₁ ∈ branchVertices H := by change 3 ≤ _; omega
  have hb₂V : b₂ ∈ branchVertices H := by change 3 ≤ _; omega
  have hb₃V : b₃ ∈ branchVertices H := by change 3 ≤ _; omega
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hJdeg := three_le_degree_of_three_connected J hJ
  have hbrange := branchVertices_subset_range htrack hrev hdisj hcover hedges
  have hrange := range_subset_branchVertices hι htrack hlen hdisj hnew hJdeg
  obtain ⟨j₀, hj₀⟩ := hbrange hbV
  obtain ⟨j₁, hj₁⟩ := hbrange hb₁V
  obtain ⟨j₂, hj₂⟩ := hbrange hb₂V
  obtain ⟨j₃, hj₃⟩ := hbrange hb₃V
  have hfrom : IsTrackFrom H [b, z, b₃] b b₃ := ⟨hB.1, rfl, rfl⟩
  have hJ03 := original_adj_of_branch_ends hι htrack hlen hrev hdisj hnew hcover hedges
    hJdeg hB hfrom (by simp [trackLength]) hj₀.symm hj₃.symm
  have lift_adj {p q : Fin m} (h : H.Adj (ι p) (ι q)) : J.Adj p q :=
    original_adj_of_subdivision_adj hι htrack hnew hedges h
  have hJ01 : J.Adj j₀ j₁ := lift_adj (by simpa [hj₀, hj₁] using h01)
  have hJ02 : J.Adj j₀ j₂ := lift_adj (by simpa [hj₀, hj₂] using h02)
  have hJ13 : J.Adj j₁ j₃ := lift_adj (by simpa [hj₁, hj₃] using h13)
  have hJ23 : J.Adj j₂ j₃ := lift_adj (by simpa [hj₂, hj₃] using h23)
  have hj12 : j₁ ≠ j₂ := by
    intro h
    have hh := congrArg ι h
    simp only [hj₁, hj₂] at hh
    tauto
  have deg {j : Fin m} (h : (H.neighborSet (ι j)).ncard = 3) :
      (J.neighborSet j).ncard = 3 := by
    have := original_degree_le_subdivision_degree hι htrack hlen hdisj hnew j
    have := hJdeg j
    omega
  have hall := four_vertices_of_two_degree_three hJ hJ03 hJ01 hJ02
    hJ13.symm hJ23.symm hj12 (deg (by simpa [hj₀] using hd0))
      (deg (by simpa [hj₃] using hd3))
  have hJ12 : J.Adj j₁ j₂ := by
    by_contra hn
    have hs : J.neighborSet j₁ ⊆ ({j₀, j₃} : Set (Fin m)) := by
      intro x hx
      rcases hall x with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact False.elim (J.irrefl hx)
      · exact False.elim (hn hx)
    have hc := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [Set.ncard_pair hJ03.ne] at hc
    have := hJdeg j₁
    omega
  have hiso := iso_top_of_four_vertices hJ03.ne hJ01.ne hJ02.ne hJ13.ne.symm
    hJ23.ne.symm hj12 hall hJ03 hJ01 hJ02 hJ13.symm hJ23.symm hJ12
  have hBV : ∀ x ∈ branchVertices H, x = b ∨ x = b₃ ∨ x = b₁ ∨ x = b₂ := by
    intro x hx
    obtain ⟨j, rfl⟩ := hbrange hx
    rcases hall j with rfl | rfl | rfl | rfl
    · exact Or.inl hj₀
    · exact Or.inr (Or.inl hj₃)
    · exact Or.inr (Or.inr (Or.inl hj₁))
    · exact Or.inr (Or.inr (Or.inr hj₂))
  have huV : u ∉ branchVertices H := by
    intro hu
    have := hBV u hu
    omega
  have hzV : z ∉ branchVertices H := hB.2.1 z (by simp [trackInterior])
  let S : Set (Fin n) := {x | x ∈ [b, b₁, b₂, b₃, u, z]}
  have hclosed : ∀ a ∈ S, ∀ c, H.Adj a c → c ∈ S := by
    intro a ha c hac
    have ha' : a = b ∨ a = b₁ ∨ a = b₂ ∨ a = b₃ ∨ a = u ∨ a = z := by
      simpa [S] using ha
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl
    · have hc := neighbor_of_degree_three hd0 (by omega) (by omega) (by omega) h01 h02 h0z hac
      rcases hc with rfl | rfl | rfl <;> simp [S]
    · have hc := neighbor_of_degree_three hd1 (by omega) (by omega) (by omega) h01.symm h13 h1u hac
      rcases hc with rfl | rfl | rfl <;> simp [S]
    · have hc := neighbor_of_degree_three hd2 (by omega) (by omega) (by omega) h02.symm h23 h2u hac
      rcases hc with rfl | rfl | rfl <;> simp [S]
    · have hc := neighbor_of_degree_three hd3 (by omega) (by omega) (by omega) h13.symm h23.symm h3z hac
      rcases hc with rfl | rfl | rfl <;> simp [S]
    · have hc := neighbor_of_not_branch huV (by omega) h1u.symm h2u.symm hac
      rcases hc with rfl | rfl <;> simp [S]
    · have hc := neighbor_of_not_branch hzV (by omega) h0z.symm h3z.symm hac
      rcases hc with rfl | rfl <;> simp [S]
  have hold : ∀ j, ι j ∈ S := by
    intro j
    have := hBV (ι j) (hrange ⟨j, rfl⟩)
    simpa [S] using (show ι j = b ∨ ι j = b₁ ∨ ι j = b₂ ∨ ι j = b₃ ∨ ι j = u ∨ ι j = z by tauto)
  have hwhole : ∀ x, x ∈ S := by
    intro x
    rcases hcover x with ⟨j, rfl⟩ | ⟨p, q, hpq, hx⟩
    · exact hold j
    · have ht := htrack p q hpq
      have hmem : x ∈ T p q := Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
      have hiS : ∀ i (hi : i < (T p q).length), (T p q)[i]'hi ∈ S := by
        intro i
        induction i with
        | zero => intro hi; rw [track_head ht hi]; exact hold p
        | succ i ih =>
          intro hi
          exact hclosed _ (ih (by omega)) _ (ht.1.2.2 i hi)
      exact hiS i hi
  have heq : Finset.univ = [b, b₁, b₂, b₃, u, z].toFinset := by
    ext x
    simp only [Finset.mem_univ, List.mem_toFinset, true_iff]
    exact hwhole x
  have hc := congrArg Finset.card heq
  rw [Finset.card_univ, List.toFinset_card_of_nodup hnd] at hc
  exact ⟨hiso, hc⟩

end Workspace.ProofLemmas.Thm61Claim12SixVertices
