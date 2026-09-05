import Workspace.ProofLemmas.Thm61Claim12SixVertices

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm61Claim12VEq

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61EvenClaims Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61EvenEndgameClaim12
open Workspace.ProofLemmas.Thm61Claim1Helpers Workspace.ProofLemmas.Thm84RungEndDictionary

/-- The first terminal case of claim (12): "If `v = b₃`, then `B₃` has length 2 and both
its edges belong to `X`, and the fourth outcome of the theorem holds." -/
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
    (huv : u ≠ v) (hvdeg : (H.neighborSet v).ncard = 2 ∨
      (H.neighborSet v).ncard = 3) (hvb₃ : v = b₃) :
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
  subst v
  obtain ⟨hB₃two, hB₃X, hb₃deg⟩ := claim12_v_eq_b3_short_complete H hsub.2
    hB₃ hfrom₃ hB₃pos hb₁V hb₂V hbb₁ hbb₂ hbb₃ hb₁b₃ hb₂b₃
    he₃B₃ he₃.2 he₃X hd₁ hd₁eq hd₂ hd₂eq hbb₂A hd₁d₂ hvdeg hother
  have hlen : B₃.length = 3 := by simp only [trackLength] at hB₃two; omega
  obtain ⟨a, z, c, hlist⟩ := List.length_eq_three.mp hlen
  have ha : a = b := by simpa [hlist] using hfrom₃.2.1
  have hc : c = b₃ := by simpa [hlist] using hfrom₃.2.2
  subst a c
  have hB : IsBranch H [b, z, b₃] := hlist ▸ hB₃
  have hbz : b ≠ z := (List.nodup_cons.mp hB.1.2.1).1 ∘ (fun h => by simp [h])
  have hzb₃ : z ≠ b₃ := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp hB.1.2.1).2).1
  have hzV : z ∉ branchVertices H := hB.2.1 z (by simp [trackInterior])
  have hzb₁ : z ≠ b₁ := fun h => hzV (h ▸ hb₁V)
  have hzb₂ : z ≠ b₂ := fun h => hzV (h ▸ hb₂V)
  have he₃eq : e₃ = s(b, z) := by
    have hh := trackEdge_at_head hfrom₃ (by omega) he₃B₃ he₃.2
    simpa [hlist] using hh
  have huz : u ≠ z := by
    intro h
    apply hf₁dis u
    exact ⟨by simp [hf₁eq], by simp [he₃eq, h]⟩
  have hnd : [b, b₁, b₂, b₃, u, z].Nodup := by
    simp [hbb₁, hbb₂, hbb₃, hub.symm, hbz, hb₁b₂, hb₁b₃, hu₁.symm,
      hzb₁.symm, hb₂b₃, hu₂.symm, hzb₂.symm, huv.symm, hzb₃.symm, huz]
  have h0z : H.Adj b z := by simpa using hB.1.2.2 0 (by simp)
  have h3z : H.Adj b₃ z := by
    have hh : H.Adj z b₃ := by simpa using hB.1.2.2 1 (by simp)
    exact hh.symm
  have hg : s(b₃, z) ∈ incidentEdges H b₃ := ⟨h3z, by simp⟩
  have hgd₁ : s(b₃, z) ≠ d₁ := by
    rw [hd₁eq]
    simp [Sym2.eq_iff, hb₁b₃.symm, hzb₁]
  have hgd₂ : s(b₃, z) ≠ d₂ := by
    rw [hd₂eq]
    simp [Sym2.eq_iff, hb₂b₃.symm, hzb₂]
  have htri := Thm61Claim12Common.triad_at_b G n H K hsub.2 φ Y hmin y₁ y₂ Q hQ hQY hy h9
    hbV he₁ he₁X he₂ he₂X hd₁ hd₁X hd₂ hd₂X hf₁X he₁eq he₂eq hd₁eq hd₂eq
    hf₁eq hbb₁ hbb₂ hb₁b₂ hv₁ hv₂ hub huv hg hgd₁ hgd₂
  have hbdeg := (triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b htri).1
  have hout := Thm61Claim12SixVertices.six_vertex_k4 J hJ H hsub.1 hnd hB
    hbb₁A hbb₂A hb₁vA hvb₂A.symm hb₁uA hub₂A.symm h0z h3z
    hbdeg hb₁deg hb₂deg hb₃deg
  exact Or.inr (Or.inr (Or.inr (Or.inl hout)))


end Workspace.ProofLemmas.Thm61Claim12VEq
