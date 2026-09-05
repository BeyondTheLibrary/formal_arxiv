/-  Proof attempt for **10.3**, following the printed proof (perfect.pdf, p. 58) step for step.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.Statements.S10.Thm_10_1
import Workspace.Statements.S10.Thm_10_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.Thm103UniqueAttach
import Workspace.ProofLemmas.Thm103Endgame

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S10

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_10_3 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFmaj : ∀ v ∈ F, ¬ MajorForPrism G a b v)
    (x₁ x₂ : V)
    (hx₁ : IsAttachment G F K x₁) (hx₁R : x₁ ∈ SPGT.interior (R 0))
    (hx₂ : IsAttachment G F K x₂) (hx₂R : x₂ ∉ R 0) :
    ∃ (f : List V) (f₁ fn : V), IsPathFrom G f f₁ fn ∧ (∀ v ∈ f, v ∈ F) ∧
      ((G.Adj f₁ (a 1) ∧ G.Adj f₁ (a 2) ∧ (∃ y ∈ R 0, y ≠ a 0 ∧ G.Adj fn y) ∧
          (∀ x ∈ f, ∀ k ∈ K, k ≠ a 0 → G.Adj x k →
            (x = f₁ ∧ (k = a 1 ∨ k = a 2)) ∨ (x = fn ∧ k ∈ R 0))) ∨
        (G.Adj f₁ (b 1) ∧ G.Adj f₁ (b 2) ∧ (∃ y ∈ R 0, y ≠ b 0 ∧ G.Adj fn y) ∧
          (∀ x ∈ f, ∀ k ∈ K, k ≠ b 0 → G.Adj x k →
            (x = f₁ ∧ (k = b 1 ∨ k = b 2)) ∨ (x = fn ∧ k ∈ R 0)))) := by
  classical
  -- ### Ambient prism bookkeeping
  have hfin3 : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
  have hpath : ∀ i : Fin 3, IsPathFrom G (R i) (a i) (b i) := fun i =>
    HyperprismFromPrism.formPrism_path hprism i
  have hmemA : ∀ i : Fin 3, a i ∈ R i := fun i =>
    List.mem_of_mem_head? (by rw [(hpath i).2.1]; rfl)
  have hmemB : ∀ i : Fin 3, b i ∈ R i := fun i =>
    List.mem_of_mem_getLast? (by rw [(hpath i).2.2]; rfl)
  have hdisj : ∀ {i j : Fin 3}, i ≠ j → ∀ u ∈ R i, u ∉ R j := fun {_ _} h =>
    HyperprismFromPrism.formPrism_disjoint hprism h
  have hx₁mem : x₁ ∈ R 0 ∧ x₁ ≠ a 0 ∧ x₁ ≠ b 0 :=
    (PathBasics.mem_interior_iff_of_pathFrom (hpath 0)).mp hx₁R
  have hmem3 : ∀ (e : Fin 3 → V) (m : Fin 3), e m ∈ ({e 0, e 1, e 2} : Set V) := by
    intro e m
    rcases hfin3 m with h | h | h <;> rw [h] <;> simp
  have hne0 : ∀ (m : Fin 3), m ≠ 0 → ∀ y : V, y ∈ R m → (y ∈ R 1 ∨ y ∈ R 2) := by
    intro m hm y hy
    rcases hfin3 m with h | h | h
    · exact absurd h hm
    · rw [h] at hy; exact Or.inl hy
    · rw [h] at hy; exact Or.inr hy
  -- ### "We may assume `F` is minimal such that …"
  obtain ⟨F₀, hF₀mem, hF₀min⟩ :=
    Set.exists_min_image {S : Set V | S ⊆ F ∧ ConnectedSet G S ∧ IsAttachment G S K x₁ ∧
        ∃ z, IsAttachment G S K z ∧ z ∉ R 0} Set.ncard (Set.toFinite _)
      ⟨F, subset_rfl, hFconn, hx₁, x₂, hx₂, hx₂R⟩
  obtain ⟨hF₀F, hF₀conn, hF₀x₁, z₀, hz₀, hz₀R⟩ := hF₀mem
  have hFmin : ∀ F' ⊆ F₀, ConnectedSet G F' → IsAttachment G F' K x₁ →
      (∃ z, IsAttachment G F' K z ∧ z ∉ R 0) → F' = F₀ := by
    intro F' hsub hconn hatt hz
    exact Set.eq_of_subset_of_ncard_le hsub
      (hF₀min F' ⟨hsub.trans hF₀F, hconn, hatt, hz⟩) (Set.toFinite _)
  have hF₀K : F₀ ⊆ Kᶜ := hF₀F.trans hFK
  have hF₀maj : ∀ v ∈ F₀, ¬ MajorForPrism G a b v := fun v hv => hFmaj v (hF₀F hv)
  -- ### "`v₁` is the only vertex of `F` with a neighbour in `V(R₂) ∪ V(R₃)`"
  have huniq := Thm103UniqueAttach.thm103_unique_attach G a b R K F₀ hprism hK hF₀K hF₀conn
    x₁ hF₀x₁ hx₁R hFmin
  -- ### The attachments of `F₀` are not local
  have hnotloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F₀ K) := by
    have hx₁att : x₁ ∈ attachments G F₀ K := hF₀x₁
    have hz₀att : z₀ ∈ attachments G F₀ K := hz₀
    rintro (h | h | h | h | h)
    · exact hz₀R (h hz₀att)
    · exact hdisj (show (0 : Fin 3) ≠ 1 by decide) x₁ hx₁mem.1 (h hx₁att)
    · exact hdisj (show (0 : Fin 3) ≠ 2 by decide) x₁ hx₁mem.1 (h hx₁att)
    · have hm := h hx₁att
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with h1 | h1 | h1
      · exact hx₁mem.2.1 h1
      · exact hdisj (show (0 : Fin 3) ≠ 1 by decide) x₁ hx₁mem.1 (by rw [h1]; exact hmemA 1)
      · exact hdisj (show (0 : Fin 3) ≠ 2 by decide) x₁ hx₁mem.1 (by rw [h1]; exact hmemA 2)
    · have hm := h hx₁att
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with h1 | h1 | h1
      · exact hx₁mem.2.2 h1
      · exact hdisj (show (0 : Fin 3) ≠ 1 by decide) x₁ hx₁mem.1 (by rw [h1]; exact hmemB 1)
      · exact hdisj (show (0 : Fin 3) ≠ 2 by decide) x₁ hx₁mem.1 (by rw [h1]; exact hmemB 2)
  -- ### "By 10.1, there is a subpath `f₁-⋯-fₙ` such that one of 10.1.1-4 holds"
  obtain ⟨f, f₁, fn, hf, hfF₀, hflen, a', b', R', σ, hR', hab', hcase⟩ :=
    thm_10_1 G hG a b R K F₀ hprism hK hF₀K hF₀conn hnotloc hF₀maj
  subst hR'
  obtain ⟨c, d, hcd, hac, hbd⟩ :
      ∃ c d : Fin 3 → V, ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) ∧
        (∀ i, a' i = c (σ i)) ∧ (∀ i, b' i = d (σ i)) := by
    rcases hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, fun i => by rw [h1], fun i => by rw [h2]⟩
    · exact ⟨b, a, Or.inr ⟨rfl, rfl⟩, fun i => by rw [h1], fun i => by rw [h2]⟩
  have hcmem : ∀ i : Fin 3, c i ∈ R i := by
    rcases hcd with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact hmemA
    · rw [h1]; exact hmemB
  have hdmem : ∀ i : Fin 3, d i ∈ R i := by
    rcases hcd with ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [h2]; exact hmemB
    · rw [h2]; exact hmemA
  have hf₁F : f₁ ∈ F₀ := hfF₀ f₁ (List.mem_of_mem_head? (by rw [hf.2.1]; rfl))
  have hfnF : fn ∈ F₀ := hfF₀ fn (List.mem_of_mem_getLast? (by rw [hf.2.2]; rfl))
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? (by rw [hf.2.1]; rfl)
  have hinj := σ.injective
  refine ⟨f, f₁, fn, hf, fun v hv => hF₀F (hfF₀ v hv), ?_⟩
  rcases hcase with hc1 | hc2 | hc3 | hc4
  -- ### 10.1.1 : killed by 10.2 together with the minimality of `F`
  · exfalso
    obtain ⟨u, u', hu, hu', huu', hf₁u, hf₁u', w, w', hw, hw', hww', hfnw, hfnw', hoth, hL⟩ := hc1
    have hu0 : u ∈ R (σ 0) := hu
    have hu'0 : u' ∈ R (σ 0) := hu'
    have hw1 : w ∈ R (σ 1) := hw
    have hw'1 : w' ∈ R (σ 1) := hw'
    have hlen1 : pathLength (R (σ 0)) = 1 ∧ pathLength (R (σ 1)) = 1 := by
      rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hp' : FormPrism G (fun i => a (σ i)) (fun i => b (σ i))
            (R (σ 0)) (R (σ 1)) (R (σ 2)) := PrismSymmetry.formPrism_perm hprism σ
        have hK' : K = {v : V | v ∈ R (σ 0)} ∪ {v : V | v ∈ R (σ 1)} ∪ {v : V | v ∈ R (σ 2)} :=
          hK.trans (PrismSymmetry.prismVertices_perm R σ).symm
        have hloc' : ¬ LocalForPrism (fun i => a (σ i)) (fun i => b (σ i))
            (R (σ 0)) (R (σ 1)) (R (σ 2)) (attachments G F₀ K) :=
          fun h => hnotloc ((PrismSymmetry.localForPrism_perm σ).mp h)
        have hmaj' : ∀ v ∈ F₀, ¬ MajorForPrism G (fun i => a (σ i)) (fun i => b (σ i)) v :=
          fun v hv h => hF₀maj v hv ((PrismSymmetry.majorForPrism_perm σ).mp h)
        rcases thm_10_2 G hG (fun i => a (σ i)) (fun i => b (σ i)) (fun i => R (σ i)) K F₀
            hp' hK' hF₀K hF₀conn hloc' hmaj' f f₁ fn hf hfF₀ hflen u u' w w'
            hu0 hu'0 huu' hf₁u hf₁u' hw1 hw'1 hww' hfnw hfnw' hoth hL with h | h
        · exact h
        · exact absurd h hK4
      · have hp' : FormPrism G (fun i => b (σ i)) (fun i => a (σ i))
            (R (σ 0)).reverse (R (σ 1)).reverse (R (σ 2)).reverse :=
          PrismSymmetry.formPrism_swap (PrismSymmetry.formPrism_perm hprism σ)
        have hK' : K = {v : V | v ∈ (R (σ 0)).reverse} ∪ {v : V | v ∈ (R (σ 1)).reverse} ∪
            {v : V | v ∈ (R (σ 2)).reverse} :=
          (hK.trans (PrismSymmetry.prismVertices_perm R σ).symm).trans
            (PrismSymmetry.prismVertices_reverse (R (σ 0)) (R (σ 1)) (R (σ 2))).symm
        have hloc' : ¬ LocalForPrism (fun i => b (σ i)) (fun i => a (σ i))
            (R (σ 0)).reverse (R (σ 1)).reverse (R (σ 2)).reverse (attachments G F₀ K) :=
          fun h => hnotloc ((PrismSymmetry.localForPrism_perm σ).mp
            (PrismSymmetry.localForPrism_swap.mp h))
        have hmaj' : ∀ v ∈ F₀, ¬ MajorForPrism G (fun i => b (σ i)) (fun i => a (σ i)) v :=
          fun v hv h => hF₀maj v hv ((PrismSymmetry.majorForPrism_perm σ).mp
            (PrismSymmetry.majorForPrism_swap.mp h))
        rcases thm_10_2 G hG (fun i => b (σ i)) (fun i => a (σ i))
            (fun i => (R (σ i)).reverse) K F₀
            hp' hK' hF₀K hF₀conn hloc' hmaj' f f₁ fn hf hfF₀ hflen u u' w w'
            (List.mem_reverse.mpr hu0) (List.mem_reverse.mpr hu'0) huu' hf₁u hf₁u'
            (List.mem_reverse.mpr hw1) (List.mem_reverse.mpr hw'1) hww' hfnw hfnw'
            hoth hL with h | h
        · constructor
          · have := h.1
            simpa [pathLength] using this
          · have := h.2
            simpa [pathLength] using this
        · exact absurd h hK4
    have hR0len : 2 ≤ pathLength (R 0) := by
      have h1 : 0 < (SPGT.interior (R 0)).length := List.length_pos_of_mem hx₁R
      rw [PathBasics.interior_length] at h1
      simp only [pathLength]
      omega
    have hσ0 : σ 0 ≠ 0 := by
      intro h; rw [h] at hlen1; omega
    have hσ1 : σ 1 ≠ 0 := by
      intro h; rw [h] at hlen1; omega
    have heq : f₁ = fn :=
      huniq f₁ hf₁F fn hfnF ⟨u, hne0 _ hσ0 u hu0, hf₁u⟩ ⟨w, hne0 _ hσ1 w hw1, hfnw⟩
    -- `f₁ = fₙ` is then adjacent to both ends of two distinct rungs, hence major
    have hlist : ∀ (m : Fin 3), pathLength (R m) = 1 → ∀ t ∈ R m, t = a m ∨ t = b m := by
      intro m hm t ht
      have h2 := HyperprismFromPrism.formPrism_two_le_length hprism m
      have hlen2 : (R m).length = 2 := by simp only [pathLength] at hm; omega
      obtain ⟨p, q, hpq⟩ := PrismBasics.length_eq_two hlen2
      have hhd : p = a m := by
        have := (hpath m).2.1; rw [hpq] at this; simpa using this
      have htl : q = b m := by
        have := (hpath m).2.2; rw [hpq] at this; simpa using this
      rw [hpq, hhd, htl] at ht
      simpa using ht
    have hends : ∀ (m : Fin 3), pathLength (R m) = 1 → ∀ s t : V, s ∈ R m → t ∈ R m →
        G.Adj s t → ∀ v : V, G.Adj v s → G.Adj v t → G.Adj v (a m) ∧ G.Adj v (b m) := by
      intro m hm s t hs ht hst v hvs hvt
      rcases hlist m hm s hs with rfl | rfl <;> rcases hlist m hm t ht with rfl | rfl
      · exact absurd hst (by simp)
      · exact ⟨hvs, hvt⟩
      · exact ⟨hvt, hvs⟩
      · exact absurd hst (by simp)
    obtain ⟨hva0, hvb0⟩ := hends (σ 0) hlen1.1 u u' hu0 hu'0 huu' f₁ hf₁u hf₁u'
    obtain ⟨hva1, hvb1⟩ := hends (σ 1) hlen1.2 w w' hw1 hw'1 hww' f₁
      (by rw [heq]; exact hfnw) (by rw [heq]; exact hfnw')
    have hσ01 : σ 0 ≠ σ 1 := fun h => by simpa using hinj h
    refine hF₀maj f₁ hf₁F ⟨?_, ?_⟩
    · have hsub : ({a (σ 0), a (σ 1)} : Set V) ⊆ ({a 0, a 1, a 2} : Set V) ∩ G.neighborSet f₁ := by
        rintro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with rfl | rfl
        · exact ⟨hmem3 a (σ 0), hva0⟩
        · exact ⟨hmem3 a (σ 1), hva1⟩
      have hne : a (σ 0) ≠ a (σ 1) := fun h => (hprism.1 (σ 0) (σ 1) hσ01).ne h
      calc (2 : ℕ) = ({a (σ 0), a (σ 1)} : Set V).ncard := (Set.ncard_pair hne).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    · have hsub : ({b (σ 0), b (σ 1)} : Set V) ⊆ ({b 0, b 1, b 2} : Set V) ∩ G.neighborSet f₁ := by
        rintro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with rfl | rfl
        · exact ⟨hmem3 b (σ 0), hvb0⟩
        · exact ⟨hmem3 b (σ 1), hvb1⟩
      have hne : b (σ 0) ≠ b (σ 1) := fun h => (hprism.2.1 (σ 0) (σ 1) hσ01).ne h
      calc (2 : ℕ) = ({b (σ 0), b (σ 1)} : Set V).ncard := (Set.ncard_pair hne).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  -- ### 10.1.2 : two distinct vertices of `f` see `V(R₂) ∪ V(R₃)`
  · exfalso
    obtain ⟨hn2, hfa, hfb, -⟩ := hc2
    have hne : f₁ ≠ fn := PathBasics.isPathFrom_ends_ne hf (by simp only [pathLength]; omega)
    have hm : σ (σ.symm 1) = 1 := σ.apply_symm_apply 1
    have h1 : a' (σ.symm 1) ∈ R 1 := by rw [hac (σ.symm 1), hm]; exact hcmem 1
    have h2 : b' (σ.symm 1) ∈ R 1 := by rw [hbd (σ.symm 1), hm]; exact hdmem 1
    exact hne (huniq f₁ hf₁F fn hfnF ⟨_, Or.inl h1, hfa _⟩ ⟨_, Or.inl h2, hfb _⟩)
  -- ### 10.1.3 : same
  · exfalso
    obtain ⟨hn2, hA0, hA1, hB0, hB1, -⟩ := hc3
    have hne : f₁ ≠ fn := PathBasics.isPathFrom_ends_ne hf (by simp only [pathLength]; omega)
    have hσ01 : σ 0 ≠ σ 1 := fun h => by simpa using hinj h
    have hor : σ 0 ≠ 0 ∨ σ 1 ≠ 0 := by
      by_cases h : σ 0 = 0
      · exact Or.inr (fun h' => hσ01 (h.trans h'.symm))
      · exact Or.inl h
    rcases hor with h | h
    · refine hne (huniq f₁ hf₁F fn hfnF ⟨a' 0, ?_, hA0⟩ ⟨b' 0, ?_, hB0⟩)
      · exact hne0 _ h _ (by rw [hac 0]; exact hcmem (σ 0))
      · exact hne0 _ h _ (by rw [hbd 0]; exact hdmem (σ 0))
    · refine hne (huniq f₁ hf₁F fn hfnF ⟨a' 1, ?_, hA1⟩ ⟨b' 1, ?_, hB1⟩)
      · exact hne0 _ h _ (by rw [hac 1]; exact hcmem (σ 1))
      · exact hne0 _ h _ (by rw [hbd 1]; exact hdmem (σ 1))
  -- ### 10.1.4 : the surviving alternative
  · obtain ⟨hA0, hA1, ⟨y, hy, hyne, hfny⟩, hoth⟩ := hc4
    have hy2 : y ∈ R (σ 2) := hy
    by_cases hσ2 : σ 2 = 0
    · -- "Hence `i = 1`, and the theorem is satisfied."
      have h02 : σ 0 ≠ 0 := by
        intro h; exact absurd (hinj (h.trans hσ2.symm)) (by decide)
      have h12 : σ 1 ≠ 0 := by
        intro h; exact absurd (hinj (h.trans hσ2.symm)) (by decide)
      have h01 : σ 0 ≠ σ 1 := fun h => by simpa using hinj h
      have hkey : ∀ p q : Fin 3, p ≠ 0 → q ≠ 0 → p ≠ q →
          (p = 1 ∧ q = 2) ∨ (p = 2 ∧ q = 1) := by decide
      have hσ01 := hkey _ _ h02 h12 h01
      have hy0 : y ∈ R 0 := by rw [← hσ2]; exact hy2
      have hyc : y ≠ c 0 := by rw [hac 2, hσ2] at hyne; exact hyne
      have hkeyfact : G.Adj f₁ (c 1) ∧ G.Adj f₁ (c 2) ∧ (∃ y' ∈ R 0, y' ≠ c 0 ∧ G.Adj fn y') ∧
          (∀ x ∈ f, ∀ m ∈ K, m ≠ c 0 → G.Adj x m →
            (x = f₁ ∧ (m = c 1 ∨ m = c 2)) ∨ (x = fn ∧ m ∈ R 0)) := by
        rw [hac 0] at hA0
        rw [hac 1] at hA1
        refine ⟨?_, ?_, ⟨y, hy0, hyc, hfny⟩, ?_⟩
        · rcases hσ01 with ⟨h, -⟩ | ⟨-, h⟩
          · rw [h] at hA0; exact hA0
          · rw [h] at hA1; exact hA1
        · rcases hσ01 with ⟨-, h⟩ | ⟨h, -⟩
          · rw [h] at hA1; exact hA1
          · rw [h] at hA0; exact hA0
        · intro x hx m hm hmc hadj
          have hm2 : m ≠ a' 2 := by rw [hac 2, hσ2]; exact hmc
          rcases hoth x hx m hm hm2 hadj with ⟨hx1, hmm⟩ | ⟨hxn, hmm⟩
          · refine Or.inl ⟨hx1, ?_⟩
            rcases hσ01 with ⟨hp, hq⟩ | ⟨hp, hq⟩
            · rcases hmm with h | h
              · rw [hac 0, hp] at h; exact Or.inl h
              · rw [hac 1, hq] at h; exact Or.inr h
            · rcases hmm with h | h
              · rw [hac 0, hp] at h; exact Or.inr h
              · rw [hac 1, hq] at h; exact Or.inl h
          · refine Or.inr ⟨hxn, ?_⟩
            rw [← hσ2]; exact hmm
      rcases hcd with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hkeyfact; exact Or.inl hkeyfact
      · rw [h1] at hkeyfact; exact Or.inr hkeyfact
    · -- "Suppose first that `i > 1` … contrary to 2.4."
      exfalso
      have hnb1 : ∃ y', (y' ∈ R 1 ∨ y' ∈ R 2) ∧ G.Adj f₁ y' := by
        by_cases h : σ 0 = 0
        · have h12 : σ 1 ≠ 0 := by
            intro h'; exact absurd (hinj (h.trans h'.symm)) (by decide)
          exact ⟨a' 1, hne0 _ h12 _ (by rw [hac 1]; exact hcmem (σ 1)), hA1⟩
        · exact ⟨a' 0, hne0 _ h _ (by rw [hac 0]; exact hcmem (σ 0)), hA0⟩
      have hnb2 : ∃ y', (y' ∈ R 1 ∨ y' ∈ R 2) ∧ G.Adj fn y' :=
        ⟨y, hne0 _ hσ2 y hy2, hfny⟩
      have heq : f₁ = fn := huniq f₁ hf₁F fn hfnF hnb1 hnb2
      refine Thm103Endgame.thm103_endgame G hG a b R K F₀ hprism hK hF₀K hF₀conn hF₀maj
        x₁ hF₀x₁ hx₁R hFmin c d hcd (σ 2) (σ 0) (σ 1) hσ2
        (fun h => by simpa using hinj h) (fun h => by simpa using hinj h)
        (fun h => by simpa using hinj h) f₁ hf₁F
        (by rw [← hac 0]; exact hA0) (by rw [← hac 1]; exact hA1)
        y hy2 (by rw [← hac 2]; exact hyne) (by rw [heq]; exact hfny) ?_
      intro m hm hmc hadj
      have hm2 : m ≠ a' 2 := by rw [hac 2]; exact hmc
      rcases hoth f₁ hf₁mem m hm hm2 hadj with ⟨-, hmm⟩ | ⟨-, hmm⟩
      · rcases hmm with h | h
        · rw [hac 0] at h; exact Or.inl h
        · rw [hac 1] at h; exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr hmm)

end SPGT

end Workspace.Statements.S10
