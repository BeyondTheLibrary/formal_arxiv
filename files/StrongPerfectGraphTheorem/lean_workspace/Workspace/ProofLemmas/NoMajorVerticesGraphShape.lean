import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm86ClaimTwo

/-!
# The four-vertex graph step in 8.6, claim (1)

This is the finite graph part of the sentence that concludes that the strip graph is `K₄`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoMajorVerticesGraphShape

open Workspace.Types.Tracks.SPGT

/-- If deleting two adjacent hubs leaves maximum degree one, while every remaining vertex sees
both hubs, then a 3-connected graph is `K₄`. -/
theorem k4_of_two_hubs
    {U : Type*} [Fintype U] (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (b₁ b₂ : U) (hb₁b₂ : J.Adj b₁ b₂)
    (hends : ∀ w : U, w ≠ b₁ → w ≠ b₂ → J.Adj w b₁ ∧ J.Adj w b₂)
    (hout : ∀ w : U, w ≠ b₁ → w ≠ b₂ →
      {v : U | J.Adj w v ∧ v ≠ b₁ ∧ v ≠ b₂}.Subsingleton) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := by
  classical
  have hbne : b₁ ≠ b₂ := hb₁b₂.ne
  have hdeg₁ : 3 ≤ (J.neighborSet b₁).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ b₁
  obtain ⟨c, hcb₁, hcb₁ne, hcb₂ne⟩ :=
    Workspace.ProofLemmas.Thm86ClaimTwo.exists_mem_ne_two hdeg₁ b₁ b₂
  have hdegc : 3 ≤ (J.neighborSet c).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ c
  obtain ⟨d, hcd, hdb₁, hdb₂⟩ :=
    Workspace.ProofLemmas.Thm86ClaimTwo.exists_mem_ne_two hdegc b₁ b₂
  have hdc : d ≠ c := hcd.ne.symm
  let T : Set U := ({b₁, b₂} : Set U)ᶜ
  have hcT : c ∈ T := by
    intro hc
    rcases hc with hc | hc
    · exact hcb₁ne hc
    · exact hcb₂ne hc
  have hdT : d ∈ T := by
    intro hd
    rcases hd with hd | hd
    · exact hdb₁ hd
    · exact hdb₂ hd
  have hpaircard : ({b₁, b₂} : Set U).ncard < 3 := by
    have hle := Set.ncard_insert_le b₁ ({b₂} : Set U)
    rw [Set.ncard_singleton] at hle
    omega
  have hTconn : (J.induce T).Connected := by
    simpa [T] using hJ.2 ({b₁, b₂} : Set U) hpaircard
  have hleaf : ∀ x : T, ((J.induce T).neighborSet x).Subsingleton := by
    intro x y hy z hz
    apply Subtype.ext
    apply hout x.1
      (fun h => x.2 (Or.inl h)) (fun h => x.2 (Or.inr h))
    · exact ⟨hy, fun h => y.2 (Or.inl h), fun h => y.2 (Or.inr h)⟩
    · exact ⟨hz, fun h => z.2 (Or.inl h), fun h => z.2 (Or.inr h)⟩
  have hTpair : ∀ w : U, w ∈ T → w = c ∨ w = d := by
    intro w hwT
    by_contra hw
    push Not at hw
    let cT : T := ⟨c, hcT⟩
    let dT : T := ⟨d, hdT⟩
    let wT : T := ⟨w, hwT⟩
    have hcTwT : cT ≠ wT := by
      intro h
      exact hw.1 (congrArg Subtype.val h).symm
    have hdTcT : dT ≠ cT := by
      intro h
      exact hdc (congrArg Subtype.val h)
    have hdTwT : dT ≠ wT := by
      intro h
      exact hw.2 (congrArg Subtype.val h).symm
    obtain ⟨p, hp⟩ := hTconn.exists_isPath cT wT
    have hpnon : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hcTwT
    have hcdT : (J.induce T).Adj cT dT := hcd
    have hsnd : p.snd = dT := hleaf cT (p.adj_snd hpnon) hcdT
    have hsndmem : p.snd ∈ p.support :=
      (List.tail_sublist p.support).subset (p.snd_mem_tail_support hpnon)
    have hdmem : dT ∈ p.support := by simpa [hsnd] using hsndmem
    exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
      hdTcT hdTwT (hleaf dT)) hdmem
  have hUsub : (Set.univ : Set U) ⊆ ({b₁, b₂, c, d} : Set U) := by
    intro w _
    by_cases hw₁ : w = b₁
    · subst w; simp
    by_cases hw₂ : w = b₂
    · subst w; simp
    rcases hTpair w (by
      intro hw
      rcases hw with hw | hw
      · exact hw₁ hw
      · exact hw₂ hw) with rfl | rfl <;> simp
  have hcardle : Fintype.card U ≤ 4 := by
    have hle := Set.ncard_le_ncard hUsub (Set.toFinite _)
    have hfour : ({b₁, b₂, c, d} : Set U).ncard ≤ 4 := by
      calc
        ({b₁, b₂, c, d} : Set U).ncard
            ≤ ({b₂, c, d} : Set U).ncard + 1 := Set.ncard_insert_le _ _
        _ ≤ ({c, d} : Set U).ncard + 2 := by
          have := Set.ncard_insert_le b₂ ({c, d} : Set U)
          omega
        _ ≤ ({d} : Set U).ncard + 3 := by
          have := Set.ncard_insert_le c ({d} : Set U)
          omega
        _ = 4 := by rw [Set.ncard_singleton]
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using hle.trans hfour
  have hcard4 : Fintype.card U = 4 := by
    have hcardgt := hJ.1
    omega
  have hcomplete : ∀ x z : U, x ≠ z → J.Adj x z := by
    intro x z hxz
    have hdx : 3 ≤ (J.neighborSet x).ncard :=
      Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ x
    have hsub : J.neighborSet x ⊆ ((Set.univ : Set U) \ {x}) := by
      intro q hq
      exact ⟨Set.mem_univ q, fun h => J.irrefl (Set.mem_singleton_iff.mp h ▸ hq)⟩
    have hcard3 : ((Set.univ : Set U) \ {x}).ncard = 3 := by
      rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ x), Set.ncard_univ,
        Nat.card_eq_fintype_card, hcard4]
    have heq : J.neighborSet x = (Set.univ : Set U) \ {x} :=
      Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
    change z ∈ J.neighborSet x
    rw [heq]
    exact ⟨Set.mem_univ z, fun h => hxz (Set.mem_singleton_iff.mp h).symm⟩
  exact ⟨⟨Fintype.equivFinOfCardEq hcard4, by
    intro x z
    simp only [SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact ⟨fun h => hcomplete x z h, fun h => h.ne⟩⟩⟩

end Workspace.ProofLemmas.NoMajorVerticesGraphShape
