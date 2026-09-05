import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.NoAntitwinsInCriticalImperfect
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Decompositions

/-- The two-tag inner gadget associated with a proper homogeneous pair is
perfect. Tags `0,1` are respectively `x1,x2`; they are adjacent, while `x1`
is complete exactly to the old vertices in `A` and `x2` exactly to those in
`B`. -/
theorem ProperHomogeneousPairInnerGadgetPerfect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G)
    (A B : Set V) (hAB : SPGT.IsProperHomogeneousPair G A B)
    (F : SimpleGraph (↥(A ∪ B) ⊕ Fin 2))
    (hF : ∀ x y, F.Adj x y ↔
      match x, y with
      | Sum.inl a, Sum.inl b => G.Adj a.1 b.1
      | Sum.inl a, Sum.inr i =>
          (i = 0 ∧ a.1 ∈ A) ∨ (i = 1 ∧ a.1 ∈ B)
      | Sum.inr i, Sum.inl a =>
          (i = 0 ∧ a.1 ∈ A) ∨ (i = 1 ∧ a.1 ∈ B)
      | Sum.inr i, Sum.inr j =>
          (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) :
    SPGT.IsPerfect F := by
  classical
  rcases hAB with
    ⟨hABdisj, hAne, hBne, hAcover, hBcover, hCC, hCA, hAC, hAA⟩
  obtain ⟨c₁₂, hc₁₂A, hc₁₂B⟩ := hCA
  obtain ⟨c₂₁, hc₂₁A, hc₂₁B⟩ := hAC
  have hc₁₂C : c₁₂ ∈ (A ∪ B)ᶜ := by
    rw [← hAcover]
    exact Or.inl hc₁₂A
  have hc₂₁C : c₂₁ ∈ (A ∪ B)ᶜ := by
    rw [← hBcover]
    exact Or.inl hc₂₁B
  have hc₁₂_ne_c₂₁ : c₁₂ ≠ c₂₁ := by
    intro h
    obtain ⟨a, haA⟩ := hAne
    exact hc₂₁A a haA (h ▸ hc₁₂A a haA)
  have hc₁₂_old (a : ↥(A ∪ B)) :
      G.Adj a.1 c₁₂ ↔ a.1 ∈ A := by
    constructor
    · intro hac
      rcases a.2 with haA | haB
      · exact haA
      · exact False.elim (hc₁₂B a.1 haB hac.symm)
    · intro haA
      exact (hc₁₂A a.1 haA).symm
  have hc₂₁_old (a : ↥(A ∪ B)) :
      G.Adj a.1 c₂₁ ↔ a.1 ∈ B := by
    constructor
    · intro hac
      rcases a.2 with haA | haB
      · exact False.elim (hc₂₁A a.1 haA hac.symm)
      · exact haB
    · intro haB
      exact (hc₂₁B a.1 haB).symm
  let motive := fun n : ℕ ↦
    ∀ X : Set (↥(A ∪ B) ⊕ Fin 2), Nat.card X = n →
      SPGT.IsPerfect (F.induce X)
  have hcritical : ∀ n : ℕ, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hXcard
      by_contra hXnonperfect
      have hXproper : ∀ Y : Set X, Y ≠ Set.univ →
          SPGT.IsPerfect ((F.induce X).induce Y) := by
        intro Y hY
        let Z : Set (↥(A ∪ B) ⊕ Fin 2) := Subtype.val '' Y
        have hZX : Z ⊆ X := by
          rintro z ⟨y, hy, rfl⟩
          exact y.2
        have hZXstrict : Z ⊂ X := by
          refine ⟨hZX, ?_⟩
          intro hXZ
          apply hY
          ext y
          simp only [Set.mem_univ, iff_true]
          have hyZ : (y : ↥(A ∪ B) ⊕ Fin 2) ∈ Z := hXZ y.2
          rcases hyZ with ⟨z, hzY, hz⟩
          have : z = y := Subtype.ext hz
          simpa [this] using hzY
        have hZcard : Nat.card Z < n := by
          rw [← hXcard]
          exact Set.Finite.card_lt_card (Set.toFinite X) hZXstrict
        have hZperfect : SPGT.IsPerfect (F.induce Z) :=
          ih (Nat.card Z) hZcard Z rfl
        let e : (F.induce X).induce Y ≃g F.induce Z :=
          { Equiv.Set.image (Subtype.val : X → (↥(A ∪ B) ⊕ Fin 2)) Y
              Subtype.val_injective with
            map_rel_iff' := by
              intro x y
              rfl }
        exact IsoTransport.isPerfect_of_iso e.symm hZperfect
      have hnotboth : ¬
          (Sum.inr (0 : Fin 2) ∈ X ∧ Sum.inr (1 : Fin 2) ∈ X) := by
        rintro ⟨h0, h1⟩
        let x₁ : X := ⟨Sum.inr 0, h0⟩
        let x₂ : X := ⟨Sum.inr 1, h1⟩
        have hx₁x₂ : x₁ ≠ x₂ := by
          intro h
          have := congrArg (fun z : X ↦ z.1) h
          simp [x₁, x₂] at this
        apply NoAntitwinsInCriticalImperfect
          (F.induce X) hXnonperfect hXproper
        refine ⟨x₁, x₂, hx₁x₂, ?_⟩
        intro z hzx₁ hzx₂
        rcases z with ⟨(a | i), hai⟩
        · change Xor'
            (F.Adj (Sum.inl a) (Sum.inr 0))
            (F.Adj (Sum.inl a) (Sum.inr 1))
          rw [hF, hF]
          rcases a.2 with haA | haB
          · have haB' : a.1 ∉ B := fun haB ↦
              Set.disjoint_left.mp hABdisj haA haB
            simp [haA, haB']
          · have haA' : a.1 ∉ A := fun haA ↦
              Set.disjoint_left.mp hABdisj haA haB
            simp [haA', haB]
        · fin_cases i
          · exact False.elim (hzx₁ (Subtype.ext rfl))
          · exact False.elim (hzx₂ (Subtype.ext rfl))
      let f : X → V := fun x ↦
        match x.1 with
        | Sum.inl a => a.1
        | Sum.inr i => if i = 0 then c₁₂ else c₂₁
      have hf_injective : Function.Injective f := by
        rintro ⟨(a | i), hai⟩ ⟨(b | j), hbj⟩ hab
        · apply Subtype.ext
          exact congrArg Sum.inl (Subtype.ext hab)
        · dsimp only [f] at hab
          split at hab
          · exact False.elim (hc₁₂C (hab ▸ a.2))
          · exact False.elim (hc₂₁C (hab ▸ a.2))
        · dsimp only [f] at hab
          split at hab
          · exact False.elim (hc₁₂C (hab.symm ▸ b.2))
          · exact False.elim (hc₂₁C (hab.symm ▸ b.2))
        · have hij : i = j := by
            fin_cases i <;> fin_cases j
            · rfl
            · exact False.elim (hc₁₂_ne_c₂₁ (by simpa [f] using hab))
            · exact False.elim (hc₁₂_ne_c₂₁ (by simpa [f] using hab.symm))
            · rfl
          subst j
          rfl
      have hf_adj : ∀ x y : X,
          (F.induce X).Adj x y ↔ G.Adj (f x) (f y) := by
        rintro ⟨(a | i), hai⟩ ⟨(b | j), hbj⟩
        · simpa [f] using hF (Sum.inl a) (Sum.inl b)
        · change F.Adj (Sum.inl a) (Sum.inr j) ↔ _
          fin_cases j
          · rw [hF]
            simpa [f] using (hc₁₂_old a).symm
          · rw [hF]
            simpa [f] using (hc₂₁_old a).symm
        · change F.Adj (Sum.inr i) (Sum.inl b) ↔ _
          fin_cases i
          · rw [hF]
            simpa [f, G.adj_comm] using (hc₁₂_old b).symm
          · rw [hF]
            simpa [f, G.adj_comm] using (hc₂₁_old b).symm
        · change F.Adj (Sum.inr i) (Sum.inr j) ↔ _
          fin_cases i <;> fin_cases j
          · simp
          · exact False.elim (hnotboth ⟨hai, hbj⟩)
          · exact False.elim (hnotboth ⟨hbj, hai⟩)
          · simp
      let f' : X → {v : V | v ∈ Set.range f} := fun x ↦ ⟨f x, x, rfl⟩
      have hf'bij : Function.Bijective f' := by
        constructor
        · intro x y hxy
          apply hf_injective
          exact congrArg Subtype.val hxy
        · rintro ⟨w, x, rfl⟩
          exact ⟨x, rfl⟩
      let e₀ : X ≃ {v : V | v ∈ Set.range f} := Equiv.ofBijective f' hf'bij
      let e : F.induce X ≃g G.induce (Set.range f) :=
        { e₀ with
          map_rel_iff' := by
            intro x y
            exact (hf_adj x y).symm }
      have hrange_ne : Set.range f ≠ (Set.univ : Set V) := by
        by_cases h0 : Sum.inr (0 : Fin 2) ∈ X
        · have h1 : Sum.inr (1 : Fin 2) ∉ X := by
            intro h1
            exact hnotboth ⟨h0, h1⟩
          have hc₂₁range : c₂₁ ∉ Set.range f := by
            rintro ⟨⟨(a | i), hai⟩, hi⟩
            · have ha : a.1 = c₂₁ := by simpa only [f] using hi
              exact hc₂₁C (ha ▸ a.2)
            · fin_cases i
              · exact hc₁₂_ne_c₂₁ (by simpa [f] using hi)
              · exact h1 hai
          intro h
          exact hc₂₁range (h.symm ▸ Set.mem_univ c₂₁)
        · have hc₁₂range : c₁₂ ∉ Set.range f := by
            rintro ⟨⟨(a | i), hai⟩, hi⟩
            · have ha : a.1 = c₁₂ := by simpa only [f] using hi
              exact hc₁₂C (ha ▸ a.2)
            · fin_cases i
              · exact h0 hai
              · exact hc₁₂_ne_c₂₁ (by simpa [f] using hi.symm)
          intro h
          exact hc₁₂range (h.symm ▸ Set.mem_univ c₁₂)
      have hrangePerfect : SPGT.IsPerfect (G.induce (Set.range f)) :=
        SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hrange_ne
      exact hXnonperfect (IsoTransport.isPerfect_of_iso e.symm hrangePerfect)
  have hAll : ∀ X : Set (↥(A ∪ B) ⊕ Fin 2),
      SPGT.IsPerfect (F.induce X) := fun X ↦ hcritical (Nat.card X) X rfl
  intro X
  have h := hAll X Set.univ
  rw [IsoTransport.chromaticNumber_iso (SimpleGraph.induceUnivIso (F.induce X)),
    IsoTransport.cliqueNum_iso (SimpleGraph.induceUnivIso (F.induce X))] at h
  exact h

end Workspace.ProofLemmas
