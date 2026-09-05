import Workspace.ProofLemmas.Thm61Claim12K33Core

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Workspace.ProofLemmas.Thm61Claim12Shape

open Workspace.Types.Tracks.SPGT Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61EvenEndgameClaim12
open Workspace.ProofLemmas.SubdivisionCounting

/-- The graph and branch in "`H` consists of the vertices `b,b₁,b₂,b₃,v` and a branch `B`
with ends `b₃` and `u`; but then `J = K₃,₃`". The eight displayed edges fix all the other
branches. If the remaining branch has length one, the appearance is degenerate. -/
theorem shape
    {m n : ℕ} (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (H : SimpleGraph (Fin n)) (hsub : IsBipartiteSubdivision J H)
    {b b₁ b₂ b₃ u v : Fin n} (hnd : [b, b₁, v, b₂, b₃, u].Nodup)
    (hb₃V : b₃ ∈ branchVertices H)
    (h01 : H.Adj b b₁) (h02 : H.Adj b b₂) (h03 : H.Adj b b₃)
    (h1v : H.Adj b₁ v) (h2v : H.Adj b₂ v) (h3v : H.Adj b₃ v)
    (h1u : H.Adj b₁ u) (h2u : H.Adj b₂ u)
    (hd0 : (H.neighborSet b).ncard = 3) (hd1 : (H.neighborSet b₁).ncard = 3)
    (hd2 : (H.neighborSet b₂).ncard = 3) (hdv : (H.neighborSet v).ncard = 3) :
    Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      u ∈ branchVertices H ∧
      ∃ B : List (Fin n), IsBranch H B ∧ IsTrackFrom H B b₃ u ∧
        Odd (trackLength B) ∧ (trackLength B = 1 → DegenerateAppearance J H) := by
  classical
  have hn := hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hn
  have hbV : b ∈ branchVertices H := by change 3 ≤ _; omega
  have hb₁V : b₁ ∈ branchVertices H := by change 3 ≤ _; omega
  have hb₂V : b₂ ∈ branchVertices H := by change 3 ≤ _; omega
  have hvV : v ∈ branchVertices H := by change 3 ≤ _; omega
  have hBfrom : IsTrackFrom H [b, b₃] b b₃ := by
    refine ⟨⟨by simp, by simp [h03.ne], ?_⟩, rfl, rfl⟩
    intro i hi
    have : i = 0 := by simpa using hi
    subst i
    exact h03
  have hB : IsBranch H [b, b₃] :=
    Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch hBfrom h03.ne
      (by simp [trackInterior]) hbV hb₃V
  have huV : u ∈ branchVertices H := by
    by_contra hu
    have hsmall : ¬ 3 ≤ (H.neighborSet u).ncard := hu
    have hs : ({b₁, b₂} : Set (Fin n)) ⊆ H.neighborSet u := by
      intro x hx
      rcases hx with rfl | rfl
      · exact h1u.symm
      · exact h2u.symm
    have hle := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [Set.ncard_pair (show b₁ ≠ b₂ by omega)] at hle
    have hdu : (H.neighborSet u).ncard = 2 := by omega
    have heq := (claim12_degree_two_structure J hJ H hsub.1 hB hBfrom
      (by simp [trackLength]) hbV hb₁V hb₂V hb₃V
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      h01 h02 h1v h2v.symm h1u h2u.symm hd1 hd2 hdu).1
    omega
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub.1
  have hJdeg := three_le_degree_of_three_connected J hJ
  have hbrange := branchVertices_subset_range htrack hrev hdisj hcover hedges
  obtain ⟨j₀, hj₀⟩ := hbrange hbV
  obtain ⟨j₁, hj₁⟩ := hbrange hb₁V
  obtain ⟨j₂, hj₂⟩ := hbrange hb₂V
  obtain ⟨j₃, hj₃⟩ := hbrange hb₃V
  obtain ⟨ju, hju⟩ := hbrange huV
  obtain ⟨jv, hjv⟩ := hbrange hvV
  have hndJ : [j₀, j₁, jv, j₂, j₃, ju].Nodup := by
    have hm : ([j₀, j₁, jv, j₂, j₃, ju].map ι).Nodup := by
      simpa only [List.map_cons, List.map_nil, hj₀, hj₁, hjv, hj₂, hj₃, hju] using hnd
    exact List.Nodup.of_map ι hm
  have lift_adj {p q : Fin m} (h : H.Adj (ι p) (ι q)) : J.Adj p q :=
    original_adj_of_subdivision_adj hι htrack hnew hedges h
  have hJ01 : J.Adj j₀ j₁ := lift_adj (by simpa [hj₀, hj₁] using h01)
  have hJ02 : J.Adj j₀ j₂ := lift_adj (by simpa [hj₀, hj₂] using h02)
  have hJ03 : J.Adj j₀ j₃ := lift_adj (by simpa [hj₀, hj₃] using h03)
  have hJ1v : J.Adj j₁ jv := lift_adj (by simpa [hj₁, hjv] using h1v)
  have hJ2v : J.Adj j₂ jv := lift_adj (by simpa [hj₂, hjv] using h2v)
  have hJ3v : J.Adj j₃ jv := lift_adj (by simpa [hj₃, hjv] using h3v)
  have hJ1u : J.Adj j₁ ju := lift_adj (by simpa [hj₁, hju] using h1u)
  have hJ2u : J.Adj j₂ ju := lift_adj (by simpa [hj₂, hju] using h2u)
  have deg {j : Fin m} (h : (H.neighborSet (ι j)).ncard = 3) :
      (J.neighborSet j).ncard = 3 := by
    have := original_degree_le_subdivision_degree hι htrack hlen hdisj hnew j
    have := hJdeg j
    omega
  obtain ⟨hiso, hJ3u, hall, hn0v, hn0u, hnvu, hn12, hn13, hn23⟩ :=
    Thm61Claim12K33Core.identify hJ hndJ hJ01 hJ1v hJ2v.symm hJ02.symm
      hJ03 hJ3v.symm hJ1u hJ2u
      (deg (by simpa [hj₀] using hd0)) (deg (by simpa [hj₁] using hd1))
      (deg (by simpa [hjv] using hdv)) (deg (by simpa [hj₂] using hd2))
  have ht : IsTrackFrom H (T j₃ ju) b₃ u := by simpa [hj₃, hju] using htrack j₃ ju hJ3u
  have htB : IsBranch H (T j₃ ju) :=
    subdivision_track_isBranch hι htrack hlen hrev hdisj hnew hcover hedges hJdeg hJ3u
  have hodd : Odd (trackLength (T j₃ ju)) := by
    obtain ⟨col⟩ := Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
    apply Nat.not_even_iff_odd.mp
    intro heven
    have hcol := (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col ht).mp heven
    have hbu := bool_eq_of_ne_ne (col b₁) (col b) (col u) (col.valid h01.symm) (col.valid h1u)
    exact col.valid h03 (hbu.trans hcol.symm)
  refine ⟨hiso, huV, T j₃ ju, htB, ht, hodd, ?_⟩
  intro hone
  have h3u : H.Adj b₃ u := by
    have htwo : (T j₃ ju).length = 2 := by simp only [trackLength] at hone; omega
    have he := ht.1.2.2 0 (by omega)
    rw [track_head ht (by omega), track_last ht htwo] at he
    exact he
  have forward : ∀ p q, J.Adj p q → H.Adj (ι p) (ι q) := by
    intro p q hpq
    rcases hall p with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hall q with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [hj₀, hj₁, hjv, hj₂, hj₃, hju] <;>
      first
      | exact h01 | exact h01.symm | exact h02 | exact h02.symm
      | exact h03 | exact h03.symm | exact h1v | exact h1v.symm
      | exact h2v | exact h2v.symm | exact h3v | exact h3v.symm
      | exact h1u | exact h1u.symm | exact h2u | exact h2u.symm
      | exact h3u | exact h3u.symm
      | exact False.elim (J.irrefl hpq)
      | exact False.elim (hn0v hpq) | exact False.elim (hn0v hpq.symm)
      | exact False.elim (hn0u hpq) | exact False.elim (hn0u hpq.symm)
      | exact False.elim (hnvu hpq) | exact False.elim (hnvu hpq.symm)
      | exact False.elim (hn12 hpq) | exact False.elim (hn12 hpq.symm)
      | exact False.elim (hn13 hpq) | exact False.elim (hn13 hpq.symm)
      | exact False.elim (hn23 hpq) | exact False.elim (hn23 hpq.symm)
  have surj : Function.Surjective ι := by
    intro x
    rcases hcover x with ⟨j, hj⟩ | ⟨p, q, hpq, hx⟩
    · exact ⟨j, hj.symm⟩
    · have htwo := subdivision_track_length_two_of_adj hι htrack hrev hnew hedges (forward p q hpq)
      obtain ⟨a, c, heq⟩ := List.length_eq_two.mp htwo
      simp [heq, trackInterior] at hx
  let ψ : J ≃g H :=
    { toEquiv := Equiv.ofBijective ι ⟨hι, surj⟩
      map_rel_iff' := by
        intro p q
        exact ⟨lift_adj, forward p q⟩ }
  obtain ⟨σ⟩ := hiso
  have hHiso : Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := ⟨ψ.symm.trans σ⟩
  have hnotK4 : ¬ Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := by
    rintro ⟨τ⟩
    have hcard := Fintype.card_congr (τ.symm.trans σ).toEquiv
    norm_num at hcard
  exact Or.inr ⟨hnotK4, ⟨σ⟩, hHiso⟩

end Workspace.ProofLemmas.Thm61Claim12Shape
