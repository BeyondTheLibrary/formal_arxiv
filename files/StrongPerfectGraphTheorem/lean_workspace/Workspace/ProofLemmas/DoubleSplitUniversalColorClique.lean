import Workspace.Types.BasicClasses

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

/-- In the nonempty active-right-pair case, a selected left vertex that meets
every active right pair yields matching coloring and clique witnesses. -/
theorem DoubleSplitUniversalColorClique
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (m n : ℕ) (a b : Fin m → W) (c d : Fin n → W)
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
      (K.Adj (a i) (c j) ∧ K.Adj (b i) (d j) ∧
        ¬ K.Adj (a i) (d j) ∧ ¬ K.Adj (b i) (c j)) ∨
      (¬ K.Adj (a i) (c j) ∧ ¬ K.Adj (b i) (d j) ∧
        K.Adj (a i) (d j) ∧ K.Adj (b i) (c j)))
    (X : Set W) :
    letI : DecidablePred (fun j : Fin n => c j ∈ X ∨ d j ∈ X) := Classical.decPred _
    let J := Finset.univ.filter (fun j : Fin n => c j ∈ X ∨ d j ∈ X)
    J.Nonempty →
      (∃ z : W,
        z ∈ X ∧ (∃ i : Fin m, z = a i ∨ z = b i) ∧
          ∀ j : Fin n, j ∈ J →
            ∃ y : W, y ∈ X ∧ (y = c j ∨ y = d j) ∧ K.Adj z y) →
        (K.induce X).Colorable (J.card + 1) ∧
          ∃ Q : Finset X,
            (K.induce X).IsClique (↑Q : Set X) ∧ Q.card = J.card + 1 := by
  classical
  intro J hJne huniv
  have hJmem : ∀ j : Fin n, j ∈ J ↔ (c j ∈ X ∨ d j ∈ X) := by
    intro j
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨j0, hj0⟩ := hJne
  -- ## the tag map inverting the bijection
  obtain ⟨tag, htag, htag'⟩ :
      ∃ tag : W → (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n),
        (∀ t, tag (Sum.elim (Sum.elim a b) (Sum.elim c d) t) = t) ∧
        (∀ w, Sum.elim (Sum.elim a b) (Sum.elim c d) (tag w) = w) := by
    refine ⟨(Equiv.ofBijective _ hbij).symm, ?_, ?_⟩
    · intro t; exact (Equiv.ofBijective _ hbij).symm_apply_apply t
    · intro w; exact (Equiv.ofBijective _ hbij).apply_symm_apply w
  have htag_a : ∀ i, tag (a i) = Sum.inl (Sum.inl i) := fun i =>
    htag (Sum.inl (Sum.inl i))
  have htag_b : ∀ i, tag (b i) = Sum.inl (Sum.inr i) := fun i =>
    htag (Sum.inl (Sum.inr i))
  have htag_c : ∀ j, tag (c j) = Sum.inr (Sum.inl j) := fun j =>
    htag (Sum.inr (Sum.inl j))
  have htag_d : ∀ j, tag (d j) = Sum.inr (Sum.inr j) := fun j =>
    htag (Sum.inr (Sum.inr j))
  have hcover : ∀ w : W,
      (∃ i, w = a i) ∨ (∃ i, w = b i) ∨ (∃ j, w = c j) ∨ (∃ j, w = d j) := by
    intro w
    have hw := htag' w
    rcases h : tag w with (i | i) | (j | j) <;> rw [h] at hw
    · exact Or.inl ⟨i, hw.symm⟩
    · exact Or.inr (Or.inl ⟨i, hw.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, hw.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨j, hw.symm⟩))
  have htagL : ∀ x : W, (∃ i : Fin m, x = a i ∨ x = b i) →
      ∃ t, tag x = Sum.inl t := by
    rintro x ⟨i, rfl | rfl⟩
    · exact ⟨Sum.inl i, htag_a i⟩
    · exact ⟨Sum.inr i, htag_b i⟩
  have htagR : ∀ y : W, (∃ j : Fin n, y = c j ∨ y = d j) →
      ∃ t, tag y = Sum.inr t := by
    rintro y ⟨j, rfl | rfl⟩
    · exact ⟨Sum.inl j, htag_c j⟩
    · exact ⟨Sum.inr j, htag_d j⟩
  have hLRne : ∀ x y : W, (∃ i : Fin m, x = a i ∨ x = b i) →
      (∃ j : Fin n, y = c j ∨ y = d j) → x ≠ y := by
    intro x y hx hy h
    obtain ⟨t, ht⟩ := htagL x hx
    obtain ⟨s, hs⟩ := htagR y hy
    rw [h, hs] at ht
    simp at ht
  -- ## a left vertex sees exactly one of `c j`, `d j`
  have hxor : ∀ x : W, (∃ i : Fin m, x = a i ∨ x = b i) →
      ∀ j : Fin n, (K.Adj x (c j) ↔ ¬ K.Adj x (d j)) := by
    rintro x ⟨i, rfl | rfl⟩ j
    · rcases hcross i j with ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩
      · exact iff_of_true h1 h3
      · exact iff_of_false h1 (not_not_intro h3)
    · rcases hcross i j with ⟨-, h2, -, h4⟩ | ⟨-, h2, -, h4⟩
      · exact iff_of_false h4 (not_not_intro h2)
      · exact iff_of_true h4 h2
  -- ## the pivot-based color of a left vertex
  obtain ⟨lc, hlc⟩ : ∃ lc : W → Fin n ⊕ Unit, ∀ w : W,
      (lc w = Sum.inr () ∧ K.Adj w (c j0)) ∨
        (lc w = Sum.inl j0 ∧ ¬ K.Adj w (c j0)) := by
    refine ⟨fun w => if K.Adj w (c j0) then Sum.inr () else Sum.inl j0, ?_⟩
    intro w
    by_cases h : K.Adj w (c j0)
    · exact Or.inl ⟨if_pos h, h⟩
    · exact Or.inr ⟨if_neg h, h⟩
  obtain ⟨dc, hdc0, hdcne⟩ : ∃ dc : Fin n → Fin n ⊕ Unit,
      dc j0 = Sum.inr () ∧ ∀ j, j ≠ j0 → dc j = Sum.inl j := by
    refine ⟨fun j => if j = j0 then Sum.inr () else Sum.inl j, ?_, ?_⟩
    · exact if_pos rfl
    · intro j hj; exact if_neg hj
  -- ## the coloring, valued in `Fin n ⊕ Unit`
  obtain ⟨colu, hcolu_a, hcolu_b, hcolu_c, hcolu_d⟩ :
      ∃ colu : W → Fin n ⊕ Unit,
        (∀ i, colu (a i) = lc (a i)) ∧ (∀ i, colu (b i) = lc (b i)) ∧
        (∀ j, colu (c j) = Sum.inl j) ∧ (∀ j, colu (d j) = dc j) := by
    refine ⟨fun w => Sum.elim (fun _ => lc w)
      (Sum.elim (fun j => (Sum.inl j : Fin n ⊕ Unit)) dc) (tag w), ?_, ?_, ?_, ?_⟩
    · intro i; show Sum.elim _ _ (tag (a i)) = _; rw [htag_a i]; rfl
    · intro i; show Sum.elim _ _ (tag (b i)) = _; rw [htag_b i]; rfl
    · intro j; show Sum.elim _ _ (tag (c j)) = _; rw [htag_c j]; rfl
    · intro j; show Sum.elim _ _ (tag (d j)) = _; rw [htag_d j]; rfl
  have hcolu_left : ∀ x : W, (∃ i : Fin m, x = a i ∨ x = b i) →
      colu x = lc x := by
    rintro x ⟨i, rfl | rfl⟩
    · exact hcolu_a i
    · exact hcolu_b i
  have hcolu_mem : ∀ w : W, w ∈ X → ∀ j, colu w = Sum.inl j → j ∈ J := by
    intro w hwX j hj
    rcases hcover w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · rw [hcolu_left _ ⟨i, Or.inl rfl⟩] at hj
      rcases hlc (a i) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hj
      · simp at hj
      · have h0 : j0 = j := Sum.inl.inj hj
        exact h0 ▸ hj0
    · rw [hcolu_left _ ⟨i, Or.inr rfl⟩] at hj
      rcases hlc (b i) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hj
      · simp at hj
      · have h0 : j0 = j := Sum.inl.inj hj
        exact h0 ▸ hj0
    · rw [hcolu_c] at hj
      have : j' = j := Sum.inl.inj hj
      rw [← this]
      exact (hJmem j').2 (Or.inl hwX)
    · by_cases hjj : j' = j0
      · rw [hcolu_d, hjj, hdc0] at hj; simp at hj
      · rw [hcolu_d, hdcne j' hjj] at hj
        have : j' = j := Sum.inl.inj hj
        rw [← this]
        exact (hJmem j').2 (Or.inr hwX)
  -- ## properness
  have hpair : ∀ i : Fin m, colu (a i) ≠ colu (b i) := by
    intro i
    rw [hcolu_a, hcolu_b]
    rcases hlc (a i) with ⟨e1, p1⟩ | ⟨e1, p1⟩ <;>
      rcases hlc (b i) with ⟨e2, p2⟩ | ⟨e2, p2⟩ <;> rw [e1, e2]
    · rcases hcross i j0 with ⟨-, -, -, h4⟩ | ⟨h1, -, -, -⟩
      · exact absurd p2 h4
      · exact absurd p1 h1
    · simp
    · simp
    · rcases hcross i j0 with ⟨h1, -, -, -⟩ | ⟨-, -, -, h4⟩
      · exact absurd h1 p1
      · exact absurd h4 p2
  have key : ∀ x y : W, K.Adj x y →
      (∃ i : Fin m, x = a i ∨ x = b i) → (∃ j : Fin n, y = c j ∨ y = d j) →
      colu x ≠ colu y := by
    rintro x y hadj hxL ⟨j, hj | hj⟩
    · subst hj
      rw [hcolu_c, hcolu_left x hxL]
      rcases hlc x with ⟨he, -⟩ | ⟨he, hp⟩ <;> rw [he]
      · simp
      · intro hcon
        have : j0 = j := Sum.inl.inj hcon
        rw [this] at hp
        exact hp hadj
    · subst hj
      have hnc : ¬ K.Adj x (c j) := by
        intro hc
        exact ((hxor x hxL j).1 hc) hadj
      rw [hcolu_d, hcolu_left x hxL]
      by_cases hjj : j = j0
      · subst hjj
        rw [hdc0]
        rcases hlc x with ⟨-, hp⟩ | ⟨he, -⟩
        · exact absurd hp hnc
        · rw [he]; simp
      · rw [hdcne j hjj]
        rcases hlc x with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he]
        · simp
        · intro hcon
          exact hjj (Sum.inl.inj hcon).symm
  have hproper : ∀ x y : W, x ∈ X → y ∈ X → K.Adj x y → colu x ≠ colu y := by
    intro x y _hxX _hyX hadj
    rcases hcover x with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      rcases hcover y with ⟨i', rfl⟩ | ⟨i', rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · by_cases h : i = i'
      · subst h; exact absurd rfl hadj.ne
      · exact absurd hadj (hleft i i' h).1
    · by_cases h : i = i'
      · subst h; exact hpair i
      · exact absurd hadj (hleft i i' h).2.1
    · exact key _ _ hadj ⟨i, Or.inl rfl⟩ ⟨j', Or.inl rfl⟩
    · exact key _ _ hadj ⟨i, Or.inl rfl⟩ ⟨j', Or.inr rfl⟩
    · by_cases h : i = i'
      · subst h; exact fun hEq => hpair i hEq.symm
      · exact absurd hadj (hleft i i' h).2.2.1
    · by_cases h : i = i'
      · subst h; exact absurd rfl hadj.ne
      · exact absurd hadj (hleft i i' h).2.2.2
    · exact key _ _ hadj ⟨i, Or.inr rfl⟩ ⟨j', Or.inl rfl⟩
    · exact key _ _ hadj ⟨i, Or.inr rfl⟩ ⟨j', Or.inr rfl⟩
    · exact fun hEq => key _ _ hadj.symm ⟨i', Or.inl rfl⟩ ⟨j, Or.inl rfl⟩ hEq.symm
    · exact fun hEq => key _ _ hadj.symm ⟨i', Or.inr rfl⟩ ⟨j, Or.inl rfl⟩ hEq.symm
    · by_cases h : j = j'
      · subst h; exact absurd rfl hadj.ne
      · rw [hcolu_c, hcolu_c]; intro hcon; exact h (Sum.inl.inj hcon)
    · by_cases h : j = j'
      · subst h; exact absurd hadj (hcd j)
      · rw [hcolu_c, hcolu_d]
        by_cases hjj : j' = j0
        · rw [hjj, hdc0]; simp
        · rw [hdcne j' hjj]; intro hcon; exact h (Sum.inl.inj hcon)
    · exact fun hEq => key _ _ hadj.symm ⟨i', Or.inl rfl⟩ ⟨j, Or.inr rfl⟩ hEq.symm
    · exact fun hEq => key _ _ hadj.symm ⟨i', Or.inr rfl⟩ ⟨j, Or.inr rfl⟩ hEq.symm
    · by_cases h : j = j'
      · subst h; exact absurd hadj.symm (hcd j)
      · rw [hcolu_d, hcolu_c]
        by_cases hjj : j = j0
        · rw [hjj, hdc0]; simp
        · rw [hdcne j hjj]; intro hcon; exact h (Sum.inl.inj hcon)
    · by_cases h : j = j'
      · subst h; exact absurd rfl hadj.ne
      · rw [hcolu_d, hcolu_d]
        by_cases hjj : j = j0
        · rw [hjj, hdc0, hdcne j' (by rw [← hjj]; exact fun hx => h hx.symm)]; simp
        · rw [hdcne j hjj]
          by_cases hjj' : j' = j0
          · rw [hjj', hdc0]; simp
          · rw [hdcne j' hjj']; intro hcon; exact h (Sum.inl.inj hcon)
  -- ## transport to a `J.card + 1` coloring
  obtain ⟨mk, hmk_val⟩ :
      ∃ mk : Fin n → {j : Fin n // j ∈ J}, ∀ j, j ∈ J → (mk j).1 = j := by
    refine ⟨fun j => if h : j ∈ J then ⟨j, h⟩ else ⟨j0, hj0⟩, ?_⟩
    intro j hj
    dsimp only
    rw [dif_pos hj]
  have hmapne : ∀ u v : Fin n ⊕ Unit,
      (∀ j, u = Sum.inl j → j ∈ J) → (∀ j, v = Sum.inl j → j ∈ J) →
      u ≠ v → Sum.map mk id u ≠ Sum.map mk id v := by
    rintro (j | u) (j' | v) hu hv hne
    · intro h
      have hmm : mk j = mk j' := by
        simpa only [Sum.map_inl, Sum.inl.injEq] using h
      have h1 := hmk_val j (hu j rfl)
      have h2 := hmk_val j' (hv j' rfl)
      exact hne (by rw [← h1, ← h2, hmm])
    · simp
    · simp
    · exact absurd (congrArg Sum.inr (Subsingleton.elim u v)) hne
  have hcolorable : (K.induce X).Colorable (J.card + 1) := by
    have hC : (K.induce X).Coloring ({j : Fin n // j ∈ J} ⊕ Unit) :=
      SimpleGraph.Coloring.mk (fun x => Sum.map mk id (colu x.1)) (by
        intro x y hxy
        have hadj : K.Adj x.1 y.1 := hxy
        exact hmapne _ _ (hcolu_mem x.1 x.2) (hcolu_mem y.1 y.2)
          (hproper x.1 y.1 x.2 y.2 hadj))
    have hcc := hC.colorable
    have hcard : Fintype.card ({j : Fin n // j ∈ J} ⊕ Unit) = J.card + 1 := by
      simp [Fintype.card_sum, Fintype.card_coe]
    rw [hcard] at hcc
    exact hcc
  refine ⟨hcolorable, ?_⟩
  -- ## the `(J.card + 1)`-clique
  obtain ⟨z, hzX, hzL, hzall⟩ := huniv
  obtain ⟨yy, hyy⟩ : ∃ yy : Fin n → W, ∀ j, j ∈ J →
      (yy j ∈ X ∧ (yy j = c j ∨ yy j = d j) ∧ K.Adj z (yy j)) := by
    refine ⟨fun j => if h : ∃ y : W, y ∈ X ∧ (y = c j ∨ y = d j) ∧ K.Adj z y
      then h.choose else c j, ?_⟩
    intro j hj
    have h : ∃ y : W, y ∈ X ∧ (y = c j ∨ y = d j) ∧ K.Adj z y := hzall j hj
    dsimp only
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨ridx, hridx_c, hridx_d⟩ :
      ∃ r : W → Fin n, (∀ j, r (c j) = j) ∧ (∀ j, r (d j) = j) := by
    refine ⟨fun w => Sum.elim (fun _ => j0) (Sum.elim id id) (tag w), ?_, ?_⟩
    · intro j; show Sum.elim _ _ (tag (c j)) = _; rw [htag_c j]; rfl
    · intro j; show Sum.elim _ _ (tag (d j)) = _; rw [htag_d j]; rfl
  have hyy_ridx : ∀ j, j ∈ J → ridx (yy j) = j := by
    intro j hj
    rcases (hyy j hj).2.1 with h | h <;> rw [h]
    · exact hridx_c j
    · exact hridx_d j
  have hyy_inj : Function.Injective
      (fun j : {x : Fin n // x ∈ J} => (⟨yy j.1, (hyy j.1 j.2).1⟩ : X)) := by
    intro j j' h
    have hv : yy j.1 = yy j'.1 := congrArg Subtype.val h
    have h1 := hyy_ridx j.1 j.2
    have h2 := hyy_ridx j'.1 j'.2
    exact Subtype.ext (by rw [← h1, ← h2, hv])
  set Y : Finset X := J.attach.image (fun j => (⟨yy j.1, (hyy j.1 j.2).1⟩ : X))
    with hY
  have hYcard : Y.card = J.card := by
    rw [hY, Finset.card_image_of_injective _ hyy_inj, Finset.card_attach]
  have hYmem : ∀ u : X, u ∈ Y → ∃ j : Fin n, j ∈ J ∧ (u : W) = yy j := by
    intro u hu
    rw [hY] at hu
    obtain ⟨j, -, hju⟩ := Finset.mem_image.mp hu
    exact ⟨j.1, j.2, by rw [← hju]⟩
  have hzY : (⟨z, hzX⟩ : X) ∉ Y := by
    intro hcon
    obtain ⟨j, hj, hzj⟩ := hYmem _ hcon
    exact hLRne z (yy j) hzL ⟨j, (hyy j hj).2.1⟩ hzj
  refine ⟨insert (⟨z, hzX⟩ : X) Y, ?_, ?_⟩
  · intro u hu v hv huv
    rw [Finset.coe_insert] at hu hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact absurd rfl huv
      · obtain ⟨j, hj, hvj⟩ := hYmem v (Finset.mem_coe.mp hv)
        show K.Adj z (v : W)
        rw [hvj]
        exact (hyy j hj).2.2
    · rcases hv with rfl | hv
      · obtain ⟨j, hj, huj⟩ := hYmem u (Finset.mem_coe.mp hu)
        show K.Adj (u : W) z
        rw [huj]
        exact ((hyy j hj).2.2).symm
      · obtain ⟨j, hj, huj⟩ := hYmem u (Finset.mem_coe.mp hu)
        obtain ⟨j', hj', hvj⟩ := hYmem v (Finset.mem_coe.mp hv)
        have hne : j ≠ j' := by
          intro hEq
          apply huv
          apply Subtype.ext
          rw [huj, hvj, hEq]
        show K.Adj (u : W) (v : W)
        rw [huj, hvj]
        rcases (hyy j hj).2.1 with h | h <;> rcases (hyy j' hj').2.1 with h' | h' <;>
          rw [h, h']
        · exact (hright j j' hne).1
        · exact (hright j j' hne).2.1
        · exact (hright j j' hne).2.2.1
        · exact (hright j j' hne).2.2.2
  · rw [Finset.card_insert_of_notMem hzY, hYcard]

end Workspace.ProofLemmas
