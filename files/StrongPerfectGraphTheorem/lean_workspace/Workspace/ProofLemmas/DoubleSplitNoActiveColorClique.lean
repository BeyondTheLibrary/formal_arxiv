import Workspace.Types.BasicClasses

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace Workspace.ProofLemmas

/-- A double-split witness with no active right pair supplies matching coloring and clique witnesses. -/
theorem DoubleSplitNoActiveColorClique
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (m n : ℕ)
    (a b : Fin m → W) (c d : Fin n → W)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hbij : Function.Bijective (Sum.elim (Sum.elim a b) (Sum.elim c d)))
    (hab : ∀ i : Fin m, K.Adj (a i) (b i))
    (hcd : ∀ j : Fin n, ¬ K.Adj (c j) (d j))
    (hleft : ∀ i i' : Fin m, i ≠ i' →
      ¬ K.Adj (a i) (a i') ∧ ¬ K.Adj (a i) (b i') ∧
      ¬ K.Adj (b i) (a i') ∧ ¬ K.Adj (b i) (b i'))
    (hright : ∀ j j' : Fin n, j ≠ j' →
      K.Adj (c j) (c j') ∧ K.Adj (c j) (d j') ∧
      K.Adj (d j) (c j') ∧ K.Adj (d j) (d j'))
    (hcross : ∀ (i : Fin m) (j : Fin n),
      (K.Adj (a i) (c j) ∧ K.Adj (b i) (d j) ∧ ¬ K.Adj (a i) (d j) ∧
        ¬ K.Adj (b i) (c j)) ∨
      (¬ K.Adj (a i) (c j) ∧ ¬ K.Adj (b i) (d j) ∧ K.Adj (a i) (d j) ∧
        K.Adj (b i) (c j)))
    (X : Set W)
    (hJ : Finset.univ.filter (fun j : Fin n => c j ∈ X ∨ d j ∈ X) = ∅) :
    ∃ k : ℕ, (K.induce X).Colorable k ∧
      ∃ Q : Finset X, (K.induce X).IsClique (↑Q : Set X) ∧ Q.card = k := by
  classical
  let T := (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n)
  let f : T → W := Sum.elim (Sum.elim a b) (Sum.elim c d)
  have hab_ne : ∀ i j, a i ≠ b j := by
    intro i j hij
    have ht := hbij.1 (show f (Sum.inl (Sum.inl i)) = f (Sum.inl (Sum.inr j)) by
      simpa [f] using hij)
    simp at ht
  let J : Finset (Fin n) := Finset.univ.filter fun j => c j ∈ X ∨ d j ∈ X
  have hJ' : J = ∅ := by
    exact hJ
  have hc : ∀ j, c j ∉ X := by
    intro j hcj
    have hj : j ∈ J := by simp [J, hcj]
    simpa [hJ'] using hj
  have hd : ∀ j, d j ∉ X := by
    intro j hdj
    have hj : j ∈ J := by simp [J, hdj]
    simpa [hJ'] using hj
  have hcover : ∀ v : ↥X, (∃ i, v.1 = a i) ∨ ∃ i, v.1 = b i := by
    intro v
    rcases hbij.2 v.1 with ⟨t, ht⟩
    rcases t with (⟨i | i⟩ | ⟨j | j⟩)
    · exact Or.inl ⟨i, by simpa [f] using ht.symm⟩
    · exact Or.inr ⟨i, by simpa [f] using ht.symm⟩
    · exfalso
      apply hc j
      rw [show c j = v.1 by simpa [f] using ht]
      exact v.2
    · exfalso
      apply hd j
      rw [show d j = v.1 by simpa [f] using ht]
      exact v.2
  by_cases hX : X = ∅
  · subst X
    refine ⟨0, ?_, ?_⟩
    · letI : IsEmpty (↥(∅ : Set W)) := ⟨by simp⟩
      exact ⟨SimpleGraph.Coloring.ofIsEmpty⟩
    · refine ⟨∅, ?_, rfl⟩
      simp
  · by_cases hpair : ∃ i : Fin m, a i ∈ X ∧ b i ∈ X
    · rcases hpair with ⟨i₀, hai₀, hbi₀⟩
      let color : ↥X → Bool := fun v => if ∃ i, v.1 = a i then false else true
      have hproper : ∀ {v w : ↥X}, (K.induce X).Adj v w → color v ≠ color w := by
        intro v w hvw
        change K.Adj v.1 w.1 at hvw
        rcases hcover v with ⟨i, hvi⟩ | ⟨i, hvi⟩ <;>
          rcases hcover w with ⟨j, hwj⟩ | ⟨j, hwj⟩
        · rw [hvi, hwj] at hvw
          by_cases hij : i = j
          · subst j; exact (hvw.ne rfl).elim
          · exact ((hleft i j hij).1 hvw).elim
        · have hva : ∃ k, v.1 = a k := ⟨i, hvi⟩
          have hwb : ¬ ∃ k, w.1 = a k := by
            rintro ⟨k, hk⟩
            exact hab_ne k j (hk.symm.trans hwj)
          simp [color, hva, hwb]
        · have hvb : ¬ ∃ k, v.1 = a k := by
            rintro ⟨k, hk⟩
            exact hab_ne k i (hk.symm.trans hvi)
          have hwa : ∃ k, w.1 = a k := ⟨j, hwj⟩
          simp [color, hvb, hwa]
        · rw [hvi, hwj] at hvw
          by_cases hij : i = j
          · subst j; exact (hvw.ne rfl).elim
          · exact ((hleft i j hij).2.2.2 hvw).elim
      let C : (K.induce X).Coloring Bool := SimpleGraph.Coloring.mk color hproper
      have hcolor : (K.induce X).Colorable 2 := by
        simpa using C.colorable
      refine ⟨2, hcolor, ?_⟩
      let va : ↥X := ⟨a i₀, hai₀⟩
      let vb : ↥X := ⟨b i₀, hbi₀⟩
      refine ⟨{va, vb}, ?_, ?_⟩
      · rw [Finset.coe_insert, Finset.coe_singleton]
        apply SimpleGraph.isClique_pair.mpr
        intro _
        exact hab i₀
      · have hvab : va ≠ vb := by
          intro hv
          exact (hab_ne i₀ i₀) (congrArg Subtype.val hv)
        simp [hvab]
    · have hnoedge : ∀ {v w : ↥X}, ¬ (K.induce X).Adj v w := by
        intro v w hvw
        change K.Adj v.1 w.1 at hvw
        rcases hcover v with ⟨i, hvi⟩ | ⟨i, hvi⟩ <;>
          rcases hcover w with ⟨j, hwj⟩ | ⟨j, hwj⟩
        · rw [hvi, hwj] at hvw
          by_cases hij : i = j
          · subst j; exact hvw.ne rfl
          · exact (hleft i j hij).1 hvw
        · rw [hvi, hwj] at hvw
          by_cases hij : i = j
          · subst j
            apply hpair
            exact ⟨i, hvi ▸ v.2, hwj ▸ w.2⟩
          · exact (hleft i j hij).2.1 hvw
        · rw [hvi, hwj] at hvw
          by_cases hij : i = j
          · subst j
            apply hpair
            exact ⟨i, hwj ▸ w.2, hvi ▸ v.2⟩
          · exact (hleft i j hij).2.2.1 hvw
        · rw [hvi, hwj] at hvw
          by_cases hij : i = j
          · subst j; exact hvw.ne rfl
          · exact (hleft i j hij).2.2.2 hvw
      let C : (K.induce X).Coloring Unit :=
        SimpleGraph.Coloring.mk (fun _ => ()) (by
          intro v w hvw
          exact (hnoedge hvw).elim)
      have hcolor : (K.induce X).Colorable 1 := by
        simpa using C.colorable
      refine ⟨1, hcolor, ?_⟩
      have hXne : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hX
      rcases hXne with ⟨x, hx⟩
      let vx : ↥X := ⟨x, hx⟩
      refine ⟨{vx}, ?_, by simp⟩
      simp

end Workspace.ProofLemmas
