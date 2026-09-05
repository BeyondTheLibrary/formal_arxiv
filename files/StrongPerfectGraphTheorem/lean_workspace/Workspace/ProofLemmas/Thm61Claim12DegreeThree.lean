import Workspace.ProofLemmas.Thm61Claim12Shape
import Workspace.ProofLemmas.Thm61Claim12ThirdEdge
import Workspace.ProofLemmas.Thm61Claim12Short

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm61Claim12DegreeThree

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61EvenClaims Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61EvenEndgameClaim12
open Workspace.ProofLemmas.Thm61Claim1Helpers Workspace.ProofLemmas.Thm84RungEndDictionary

/-- Claim (12): "If `v ≠ b₃` and `v` has degree 3, then the third edge incident with `v`
is `vb₃`, and `b` is a triad ... but then `J = K₃,₃`, and if `B` has length 1 then the
second outcome of the theorem holds, and otherwise the first outcome holds." -/
theorem conclusion
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ d₁ d₂ : Sym2 (Fin n)) (u v : Fin n)
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁)
    (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂)
    (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂))
    (hd₁ : d₁ ∈ incidentEdges H b₁) (hd₁X : d₁ ∈ extraEdges G H K φ Y y₂)
    (hd₂ : d₂ ∈ incidentEdges H b₂) (hd₂X : d₂ ∈ extraEdges G H K φ Y y₁)
    (hf₁eq : f₁ = s(b₁, u)) (hf₂eq : f₂ = s(b₂, u))
    (hd₁eq : d₁ = s(b₁, v)) (hd₂eq : d₂ = s(b₂, v))
    (hu₁ : u ≠ b₁) (hu₂ : u ≠ b₂) (hv₁ : v ≠ b₁) (hv₂ : v ≠ b₂)
    (huv : u ≠ v) (hvb₃ : v ≠ b₃) (hvdeg : (H.neighborSet v).ncard = 3) :
    Thm61Concl G m J n H K φ Y := by
  classical
  rcases hbc with ⟨hbV, hnon, he₁, he₁X, he₂, he₂X, he₃, he₃ne₁, he₃ne₂,
    hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁, he₁X, he₂, he₂X, he₃, he₃ne₁, he₃ne₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, -, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
      hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc'
  obtain ⟨htri₁, htri₂, hB₁one, hB₂one⟩ :=
    claim12_triads_and_short G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' f₁ f₂
      hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne
  obtain ⟨hb₁deg, -, -, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₁ htri₁
  obtain ⟨hb₂deg, -, -, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ htri₂
  have he₁eq : e₁ = s(b, b₁) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₁ hB₁one] at he₁B₁
    exact Set.mem_singleton_iff.mp he₁B₁
  have he₂eq : e₂ = s(b, b₂) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₂ hB₂one] at he₂B₂
    exact Set.mem_singleton_iff.mp he₂B₂
  obtain ⟨hXE, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁ he₁X he₂ he₂X he₃
      he₃ne₁ he₃ne₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have hf₁dis : DisjointEdges f₁ e₃ := by
    unfold MeetEdges at hf₁e
    exact Classical.byContradiction hf₁e
  have hf₂dis : DisjointEdges f₂ e₃ := by
    unfold MeetEdges at hf₂e
    exact Classical.byContradiction hf₂e
  have hub : u ≠ b := by
    intro hub
    have heq : f₁ = e₁ := by rw [hf₁eq, hub, he₁eq, Sym2.eq_swap]
    exact (Set.disjoint_left.mp hXX₁ hf₁X) (heq ▸ he₁X)
  have hvb : v ≠ b := by
    intro hvb
    have heq : d₁ = e₁ := by rw [hd₁eq, hvb, he₁eq, Sym2.eq_swap]
    exact (Set.disjoint_left.mp hX₁X₂ he₁X) (by rw [← heq]; exact hd₁X)
  have hbb₁A : H.Adj b b₁ := by
    apply H.mem_edgeSet.mp
    rw [← he₁eq]
    exact he₁.1
  have hbb₂A : H.Adj b b₂ := by
    apply H.mem_edgeSet.mp
    rw [← he₂eq]
    exact he₂.1
  have hb₁uA : H.Adj b₁ u := by
    apply H.mem_edgeSet.mp
    rw [← hf₁eq]
    exact hXE hf₁X
  have hub₂A : H.Adj u b₂ := by
    apply H.mem_edgeSet.mp
    rw [Sym2.eq_swap, ← hf₂eq]
    exact hXE hf₂X
  have hb₁vA : H.Adj b₁ v := by
    apply H.mem_edgeSet.mp
    rw [← hd₁eq]
    exact hd₁.1
  have hvb₂A : H.Adj v b₂ := by
    apply H.mem_edgeSet.mp
    rw [Sym2.eq_swap, ← hd₂eq]
    exact hd₂.1
  have hbf₁ : b ∉ f₁ := fun hb => hf₁dis b ⟨hb, he₃.2⟩
  have hother := claim12_other_edge_at_v G n H K hsub.2 φ Y hmin y₁ y₂ Q hQ hQY hy h9
    he₁ he₁X he₂ he₂X he₃ he₃ne₁ he₃ne₂ hd₁ hd₁X hd₂ hd₂X hf₁X
    he₁eq he₂eq hd₁eq hd₂eq hf₁eq hbb₁ hbb₂ hb₁b₂ hv₁ hv₂ huv hbf₁
  have hd₁d₂ : d₁ ≠ d₂ := by
    intro h
    exact Set.disjoint_left.mp hX₁X₂ (h ▸ hd₂X) hd₁X
  obtain ⟨hg, hgd₁, hgd₂, hgX, he₃eq, hB₃one⟩ :=
    Thm61Claim12ThirdEdge.third_edge J hJ H hsub hB₃ hfrom₃ hB₃pos he₃B₃ he₃ hbb₃
      hbb₁A hb₁vA hvb hvb₃ hvdeg hd₁d₂ hother
  have htri := Thm61Claim12Common.triad_at_b G n H K hsub.2 φ Y hmin y₁ y₂ Q hQ hQY hy h9
    hbV he₁ he₁X he₂ he₂X hd₁ hd₁X hd₂ hd₂X hf₁X he₁eq he₂eq hd₁eq hd₂eq
    hf₁eq hbb₁ hbb₂ hb₁b₂ hv₁ hv₂ hub huv hg hgd₁ hgd₂
  have hbdeg := (triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b htri).1
  have hbb₃A : H.Adj b b₃ := H.mem_edgeSet.mp (he₃eq ▸ he₃.1)
  have hvb₃A : H.Adj v b₃ := H.mem_edgeSet.mp hg.1
  have hub₃ : u ≠ b₃ := by
    intro h
    apply hf₁dis u
    exact ⟨by simp [hf₁eq], by simp [he₃eq, h]⟩
  have hnd : [b, b₁, v, b₂, b₃, u].Nodup := by
    simp [hbb₁, hvb.symm, hbb₂, hbb₃, hub.symm, hv₁.symm, hb₁b₂, hb₁b₃,
      hu₁.symm, hv₂, hvb₃, huv.symm, hb₂b₃, hu₂.symm, hub₃.symm]
  obtain ⟨hJiso, huV, B, hB, hfrom, hodd, hdeg⟩ := Thm61Claim12Shape.shape J hJ H hsub
    hnd hb₃V hbb₁A hbb₂A hbb₃A hb₁vA hvb₂A.symm hvb₃A.symm hb₁uA hub₂A.symm
    hbdeg hb₁deg hb₂deg hvdeg
  by_cases hone : trackLength B = 1
  · have hdegapp := hdeg hone
    have htwo : B.length = 2 := by simp only [trackLength] at hone; omega
    have h3u : H.Adj b₃ u := by
      have hh := hfrom.1.2.2 0 (by omega)
      rw [Workspace.ProofLemmas.SubdivisionCounting.track_head hfrom (by omega),
        Workspace.ProofLemmas.SubdivisionCounting.track_last hfrom htwo] at hh
      exact hh
    obtain ⟨n', H', K', φ', happ, hover⟩ :=
      Thm61Claim12Short.short_complement G H K Y φ Q y₁ y₂ hQ hQY hy hQeven
        (fun x hx => (hYmajor x hx).1) hnd
        (he₁eq ▸ he₁X) (he₂eq ▸ he₂X) (he₃eq ▸ he₃X)
        (by simpa only [hd₁eq, Sym2.eq_swap] using hd₁X)
        (by simpa only [hd₂eq, Sym2.eq_swap] using hd₂X) hgX
        (by simpa only [hf₁eq, Sym2.eq_swap] using hf₁X)
        (by simpa only [hf₂eq, Sym2.eq_swap] using hf₂X)
        (H.mem_edgeSet.mpr h3u.symm)
    obtain ⟨σ⟩ := hJiso
    have happJ : IsAppearance Gᶜ J H' K' :=
      ⟨⟨Workspace.ProofLemmas.Thm85Five8Transported.isSubdivision_of_iso σ.symm happ.1.1,
        happ.1.2⟩, happ.2⟩
    exact Or.inr (Or.inl ⟨Or.inl ⟨σ⟩, hdegapp, n', H', K', φ', happJ, hover⟩)
  · have hlong : 3 ≤ trackLength B := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
    have hover := overshadowed_of_major_branch φ hB hfrom hodd hlong hb₃V huV (hYmajor y₁ hy₁Y)
    exact Or.inl ⟨Or.inl hJiso, n, H, K, φ, ⟨hsub, ⟨φ⟩⟩, hover⟩


end Workspace.ProofLemmas.Thm61Claim12DegreeThree
