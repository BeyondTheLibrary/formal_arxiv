import Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iCore

/-!
# 10.6, claim (2): the interior-attachment block, assembled

Here the printed sentences

> *"Suppose first that there exists `x₁ ∈ X ∩ C₁`.  Since `X` is not local, we may assume that
> there exists `x₂ ∈ X ∩ S₂`.  For `i = 1, 2, 3` choose an `i`-rung `Rᵢ` … Then `R₁, R₂, R₃`
> form an even prism `K` say.  By 10.5 we may assume no vertex in `F` is major with respect to
> `K`; so by 10.3 …"*

(printed p. 61) are carried out, and the two symmetric outcomes of 10.3 are fed to
`HyperprismLocalEnlargementhyp3iCore.coreFromA`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iStep

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismRungStructure
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iCore
open Workspace.ProofLemmas.Thm106Assembly

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

/-- A copy of `HyperprismLocalEnlargementInterior.ExtensionData`, available before that
module. -/
def ExtData (G : SimpleGraph V) (A B C : Fin 3 → Set V) : Prop :=
  ∃ (p : List V) (u : V),
    u ∈ p ∧ p.Nodup ∧
    (∀ z ∈ p, z ∉ hyperVerts A B C) ∧
    (∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A k, G.Adj u a) ∧
    (∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
      ∀ y ∈ A k ∪ B k ∪ C k, G.Adj z y → z = u ∧ y ∈ A k) ∧
    (let A' := fun k : Fin 3 => if k = 0 then A k ∪ {u} else A k
     let C' := fun k : Fin 3 =>
       if k = 0 then C k ∪ {z : V | z ∈ p ∧ z ≠ u} else C k
     ∃ q : List V, IsRungOfHyperprism G A' B C' 0 q ∧ ∀ z ∈ p, z ∈ q)

/-- PAPER (10.6, claim (2), printed p. 61), the block opened by *"Suppose first that there
exists `x₁ ∈ X ∩ C₁`"*, with the first strip already moved to index `0` and the second
attachment already in the strip of index `1`. -/
theorem coreStep [Fintype V] [DecidableEq V] {F : Set V}
    (hG : Berge G) (hK4 : NoK4 G) (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    {x₁ x₂ : V}
    (hx₁ : x₁ ∈ attachments G F (hyperVerts A B C)) (hx₁C : x₁ ∈ C 0)
    (hx₂ : x₂ ∈ attachments G F (hyperVerts A B C)) (hx₂S : x₂ ∈ A 1 ∪ B 1 ∪ C 1) :
    ExtData G A B C ∨ ExtData G B A C := by
  classical
  obtain ⟨P0, α0, β0, hP0, hx₁P0⟩ := exists_rung_through hH 0 (Or.inr hx₁C)
  obtain ⟨P1, α1, β1, hP1, hx₂P1⟩ := exists_rung_through hH 1 hx₂S
  obtain ⟨P2, α2, β2, hP2⟩ := exists_rung hH 2
  set R : Fin 3 → List V := ![P0, P1, P2] with hRdef
  set a : Fin 3 → V := ![α0, α1, α2] with hadef
  set b : Fin 3 → V := ![β0, β1, β2] with hbdef
  have hR : ∀ i : Fin 3, IsRungFrom G A B C i (R i) (a i) (b i) := by
    intro i
    fin_cases i
    · exact hP0
    · exact hP1
    · exact hP2
  have hx₁int : x₁ ∈ SPGT.interior (R 0) := mem_interior_of_mem_C hH hP0 hx₁P0 hx₁C
  have hFout : F ⊆ (prismVerts R)ᶜ := by
    intro v hv hvK
    refine hF.1.2.1 hv ?_
    rcases mem_prismVerts.mp hvK with h | h | h
    · exact rung_subset_hyperVerts (hR 0) v h
    · exact rung_subset_hyperVerts (hR 1) v h
    · exact rung_subset_hyperVerts (hR 2) v h
  have hEven : IsEvenPrism G a b (R 0) (R 1) (R 2) := rungs_isEvenPrism hG hH hR
  have hmaj : ∀ v ∈ F, ¬ MajorForPrism G a b v := by
    intro v _ hv
    exact hNoBalanced (Workspace.Statements.S10.SPGT.thm_10_5 G hG hK4 a b
      (R 0) (R 1) (R 2) v hEven hv)
  have hx₁K : IsAttachment G F (prismVerts R) x₁ :=
    ⟨mem_prismVerts.mpr (Or.inl hx₁P0), hx₁.2⟩
  have hx₂K : IsAttachment G F (prismVerts R) x₂ :=
    ⟨mem_prismVerts.mpr (Or.inr (Or.inl hx₂P1)), hx₂.2⟩
  have hx₂R0 : x₂ ∉ R 0 :=
    rung_disj hH (show (1 : Fin 3) ≠ 0 by decide) (hR 1) (hR 0) x₂ hx₂P1
  obtain ⟨f, f₁, fn, hf, hfF, hcase⟩ :=
    Workspace.Statements.S10.SPGT.thm_10_3 G hG hK4 a b R (prismVerts R) F
      (rungs_formPrism hH hR) rfl hFout hF.1.1 hmaj x₁ x₂ hx₁K hx₁int hx₂K hx₂R0
  rcases hcase with hAcase | hBcase
  · exact Or.inl (coreFromA hG hK4 hNoBalanced hH hF hR hx₁.2 hx₁int hf hfF hAcase)
  · refine Or.inr (coreFromA hG hK4 hNoBalanced
      (Workspace.ProofLemmas.HyperprismTwoAttachments.isHyperprism_swap hH)
      (minimalBad_swap hF) (R := fun i => (R i).reverse) (a := b) (b := a) ?_ hx₁.2 ?_
      hf hfF ?_)
    · intro i
      exact ⟨(hR i).2.1, (hR i).1,
        Workspace.ProofLemmas.PathBasics.isPathFrom_reverse (hR i).2.2.1,
        fun w hw => (hR i).2.2.2 w
          (Workspace.ProofLemmas.PathBasics.mem_interior_reverse.mp hw)⟩
    · exact Workspace.ProofLemmas.PathBasics.mem_interior_reverse.mpr hx₁int
    · obtain ⟨hb1, hb2, ⟨y, hyR, hyne, hfny⟩, honly⟩ := hBcase
      refine ⟨hb1, hb2, ⟨y, List.mem_reverse.mpr hyR, hyne, hfny⟩, ?_⟩
      intro x hx k hk hkne hadj
      have hk' : k ∈ prismVerts R := by
        rcases mem_prismVerts.mp hk with h | h | h
        · exact mem_prismVerts.mpr (Or.inl (List.mem_reverse.mp h))
        · exact mem_prismVerts.mpr (Or.inr (Or.inl (List.mem_reverse.mp h)))
        · exact mem_prismVerts.mpr (Or.inr (Or.inr (List.mem_reverse.mp h)))
      rcases honly x hx k hk' hkne hadj with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, List.mem_reverse.mpr h.2⟩

/-- PAPER (10.6, claim (2), printed p. 61): *"Suppose first that there exists `x₁ ∈ X ∩ C₁`.
Since `X` is not local, we may assume that there exists `x₂ ∈ X ∩ S₂`."*

The two *"we may assume"*s are the permutation `σ` of the three strips. -/
theorem interiorProducesExtData [Fintype V] [DecidableEq V] {F : Set V}
    (hG : Berge G) (hK4 : NoK4 G) (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hInterior : ∃ (i : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) ∧ x ∈ C i) :
    (∃ σ : Equiv.Perm (Fin 3),
      ExtData G (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k))) ∨
    (∃ σ : Equiv.Perm (Fin 3),
      ExtData G (fun k => B (σ k)) (fun k => A (σ k)) (fun k => C (σ k))) := by
  classical
  obtain ⟨i, x₁, hx₁att, hx₁C⟩ := hInterior
  have hnotS : ¬ (attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i) := by
    intro h
    refine hF.1.2.2 ?_
    fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨x₂, hx₂att, hx₂S⟩ := Set.not_subset.mp hnotS
  obtain ⟨j, hj⟩ := mem_hyperVerts_iff.mp hx₂att.1
  have hji : j ≠ i := by rintro rfl; exact hx₂S hj
  -- a permutation carrying `0` to `i` and `1` to `j`
  set τ : Equiv.Perm (Fin 3) := Equiv.swap 0 i with hτ
  have hτ0 : τ 0 = i := Equiv.swap_apply_left 0 i
  set m : Fin 3 := τ.symm j with hm
  have hm0 : m ≠ 0 := by
    intro h
    exact hji (by rw [← hτ0, ← h, hm, Equiv.apply_symm_apply])
  set ρ : Equiv.Perm (Fin 3) := Equiv.swap 1 m with hρ
  have hρ0 : ρ 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hm0)
  have hρ1 : ρ 1 = m := Equiv.swap_apply_left 1 m
  set σ : Equiv.Perm (Fin 3) := ρ.trans τ with hσ
  have hσ0 : σ 0 = i := by rw [hσ, Equiv.trans_apply, hρ0, hτ0]
  have hσ1 : σ 1 = j := by rw [hσ, Equiv.trans_apply, hρ1, hm, Equiv.apply_symm_apply]
  have hH' := Workspace.ProofLemmas.HyperprismTwoAttachments.isHyperprism_perm hG hH σ
  have hF' := minimalBad_perm σ hF
  have hVerts : hyperVerts (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k))
      = hyperVerts A B C := hyperVerts_perm A B C σ
  have hx₁att' : x₁ ∈ attachments G F
      (hyperVerts (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k))) := by
    rw [hVerts]; exact hx₁att
  have hx₂att' : x₂ ∈ attachments G F
      (hyperVerts (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k))) := by
    rw [hVerts]; exact hx₂att
  have hx₁C' : x₁ ∈ (fun k => C (σ k)) 0 := by show x₁ ∈ C (σ 0); rw [hσ0]; exact hx₁C
  have hx₂S' : x₂ ∈ (fun k => A (σ k)) 1 ∪ (fun k => B (σ k)) 1 ∪ (fun k => C (σ k)) 1 := by
    show x₂ ∈ A (σ 1) ∪ B (σ 1) ∪ C (σ 1)
    rw [hσ1]; exact hj
  rcases coreStep hG hK4 hNoBalanced hH' hF' hx₁att' hx₁C' hx₂att' hx₂S' with h | h
  · exact Or.inl ⟨σ, h⟩
  · exact Or.inr ⟨σ, h⟩

end Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iStep
