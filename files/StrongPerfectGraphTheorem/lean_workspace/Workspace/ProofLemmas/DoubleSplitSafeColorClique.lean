import Workspace.Types.BasicClasses

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Classical

namespace Workspace.ProofLemmas

/-- In the safe active-pair case of a double split graph, an induced subgraph has
a coloring and clique indexed by its active right pairs. -/
theorem DoubleSplitSafeColorClique
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (m n : ℕ)
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
      (K.Adj (a i) (c j) ∧ K.Adj (b i) (d j) ∧
        ¬ K.Adj (a i) (d j) ∧ ¬ K.Adj (b i) (c j)) ∨
      (¬ K.Adj (a i) (c j) ∧ ¬ K.Adj (b i) (d j) ∧
        K.Adj (a i) (d j) ∧ K.Adj (b i) (c j)))
    (X : Set W) :
    let J : Finset (Fin n) :=
      Finset.univ.filter (fun j : Fin n => c j ∈ X ∨ d j ∈ X)
    let q : ℕ := J.card
    J.Nonempty →
    (¬ ∃ z : W,
      z ∈ X ∧ (∃ i : Fin m, z = a i ∨ z = b i) ∧
        ∀ j : Fin n, j ∈ J →
          ∃ y : W, y ∈ X ∧ (y = c j ∨ y = d j) ∧ K.Adj z y) →
    (K.induce X).Colorable q ∧
      ∃ Q : Finset X, (K.induce X).IsClique (↑Q : Set X) ∧ Q.card = q := by
  classical
  intro J q hJne hnouniv
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
  -- ## the safe index of a left vertex
  obtain ⟨sIdx, hsIdx_mem, hsIdx_safe⟩ :
      ∃ s : W → Fin n, (∀ z, s z ∈ J) ∧
        (∀ z, (∃ j, j ∈ J ∧
              ∀ y : W, y ∈ X → (y = c j ∨ y = d j) → ¬ K.Adj z y) →
          (s z ∈ J ∧
            ∀ y : W, y ∈ X → (y = c (s z) ∨ y = d (s z)) → ¬ K.Adj z y)) := by
    refine ⟨fun z => if h : ∃ j, j ∈ J ∧
        ∀ y : W, y ∈ X → (y = c j ∨ y = d j) → ¬ K.Adj z y then h.choose else j0,
      ?_, ?_⟩
    · intro z
      dsimp only
      by_cases h : ∃ j, j ∈ J ∧
          ∀ y : W, y ∈ X → (y = c j ∨ y = d j) → ¬ K.Adj z y
      · rw [dif_pos h]; exact h.choose_spec.1
      · rw [dif_neg h]; exact hj0
    · intro z h
      dsimp only
      rw [dif_pos h]
      exact h.choose_spec
  have hleft_safe : ∀ z : W, z ∈ X → (∃ i : Fin m, z = a i ∨ z = b i) →
      (sIdx z ∈ J ∧
        ∀ y : W, y ∈ X → (y = c (sIdx z) ∨ y = d (sIdx z)) → ¬ K.Adj z y) := by
    intro z hzX hzL
    apply hsIdx_safe
    by_contra hno
    apply hnouniv
    refine ⟨z, hzX, hzL, ?_⟩
    intro j hjJ
    by_contra hy
    exact hno ⟨j, hjJ, fun y hyX hyR hadj => hy ⟨y, hyX, hyR, hadj⟩⟩
  -- ## the coloring, valued in `Fin n`
  obtain ⟨col, hcol_a, hcol_b, hcol_c, hcol_d⟩ :
      ∃ col : W → Fin n,
        (∀ i, col (a i) = sIdx (a i)) ∧ (∀ i, col (b i) = sIdx (b i)) ∧
        (∀ j, col (c j) = j) ∧ (∀ j, col (d j) = j) := by
    refine ⟨fun w => Sum.elim (fun _ => sIdx w) (Sum.elim id id) (tag w),
      ?_, ?_, ?_, ?_⟩
    · intro i; show Sum.elim _ _ (tag (a i)) = _; rw [htag_a i]; rfl
    · intro i; show Sum.elim _ _ (tag (b i)) = _; rw [htag_b i]; rfl
    · intro j; show Sum.elim _ _ (tag (c j)) = _; rw [htag_c j]; rfl
    · intro j; show Sum.elim _ _ (tag (d j)) = _; rw [htag_d j]; rfl
  have hcol_left : ∀ x : W, (∃ i : Fin m, x = a i ∨ x = b i) → col x = sIdx x := by
    rintro x ⟨i, rfl | rfl⟩
    · exact hcol_a i
    · exact hcol_b i
  have hcol_mem : ∀ w : W, w ∈ X → col w ∈ J := by
    intro w hwX
    rcases hcover w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hcol_a]; exact hsIdx_mem _
    · rw [hcol_b]; exact hsIdx_mem _
    · rw [hcol_c]; exact (hJmem j).2 (Or.inl hwX)
    · rw [hcol_d]; exact (hJmem j).2 (Or.inr hwX)
  -- ## the two endpoints of a selected left edge get different colors
  have hleftpair_col : ∀ i : Fin m, a i ∈ X → b i ∈ X →
      col (a i) ≠ col (b i) := by
    intro i haX hbX hEq
    have hsa := hleft_safe (a i) haX ⟨i, Or.inl rfl⟩
    have hsb := hleft_safe (b i) hbX ⟨i, Or.inr rfl⟩
    rw [hcol_a, hcol_b] at hEq
    rw [← hEq] at hsb
    obtain ⟨hjJ, hsa2⟩ := hsa
    obtain ⟨-, hsb2⟩ := hsb
    rcases (hJmem _).1 hjJ with hcX | hdX
    · rcases hcross i (sIdx (a i)) with ⟨h1, -, -, -⟩ | ⟨-, -, -, h4⟩
      · exact hsa2 _ hcX (Or.inl rfl) h1
      · exact hsb2 _ hcX (Or.inl rfl) h4
    · rcases hcross i (sIdx (a i)) with ⟨-, h2, -, -⟩ | ⟨-, -, h3, -⟩
      · exact hsb2 _ hdX (Or.inr rfl) h2
      · exact hsa2 _ hdX (Or.inr rfl) h3
  -- ## properness
  have key : ∀ x y : W, x ∈ X → y ∈ X → K.Adj x y →
      (∃ i : Fin m, x = a i ∨ x = b i) → (∃ j : Fin n, y = c j ∨ y = d j) →
      col x ≠ col y := by
    rintro x y hxX hyX hadj hxL ⟨j, hj⟩ hEq
    have hs := hleft_safe x hxX hxL
    have hcy : col y = j := by
      rcases hj with rfl | rfl
      · exact hcol_c j
      · exact hcol_d j
    have hsx : sIdx x = j := by rw [← hcol_left x hxL, hEq, hcy]
    exact hs.2 y hyX (by rw [hsx]; exact hj) hadj
  have hproper : ∀ x y : W, x ∈ X → y ∈ X → K.Adj x y → col x ≠ col y := by
    intro x y hxX hyX hadj
    rcases hcover x with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      rcases hcover y with ⟨i', rfl⟩ | ⟨i', rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · by_cases h : i = i'
      · subst h; exact absurd rfl hadj.ne
      · exact absurd hadj (hleft i i' h).1
    · by_cases h : i = i'
      · subst h; exact hleftpair_col i hxX hyX
      · exact absurd hadj (hleft i i' h).2.1
    · exact key _ _ hxX hyX hadj ⟨i, Or.inl rfl⟩ ⟨j', Or.inl rfl⟩
    · exact key _ _ hxX hyX hadj ⟨i, Or.inl rfl⟩ ⟨j', Or.inr rfl⟩
    · by_cases h : i = i'
      · subst h; exact fun hEq => hleftpair_col i hyX hxX hEq.symm
      · exact absurd hadj (hleft i i' h).2.2.1
    · by_cases h : i = i'
      · subst h; exact absurd rfl hadj.ne
      · exact absurd hadj (hleft i i' h).2.2.2
    · exact key _ _ hxX hyX hadj ⟨i, Or.inr rfl⟩ ⟨j', Or.inl rfl⟩
    · exact key _ _ hxX hyX hadj ⟨i, Or.inr rfl⟩ ⟨j', Or.inr rfl⟩
    · exact fun hEq =>
        key _ _ hyX hxX hadj.symm ⟨i', Or.inl rfl⟩ ⟨j, Or.inl rfl⟩ hEq.symm
    · exact fun hEq =>
        key _ _ hyX hxX hadj.symm ⟨i', Or.inr rfl⟩ ⟨j, Or.inl rfl⟩ hEq.symm
    · by_cases h : j = j'
      · subst h; exact absurd rfl hadj.ne
      · rw [hcol_c, hcol_c]; exact h
    · by_cases h : j = j'
      · subst h; exact absurd hadj (hcd j)
      · rw [hcol_c, hcol_d]; exact h
    · exact fun hEq =>
        key _ _ hyX hxX hadj.symm ⟨i', Or.inl rfl⟩ ⟨j, Or.inr rfl⟩ hEq.symm
    · exact fun hEq =>
        key _ _ hyX hxX hadj.symm ⟨i', Or.inr rfl⟩ ⟨j, Or.inr rfl⟩ hEq.symm
    · by_cases h : j = j'
      · subst h; exact absurd hadj.symm (hcd j)
      · rw [hcol_d, hcol_c]; exact h
    · by_cases h : j = j'
      · subst h; exact absurd rfl hadj.ne
      · rw [hcol_d, hcol_d]; exact h
  -- ## the `q`-coloring
  obtain ⟨mk, hmk_val⟩ :
      ∃ mk : Fin n → {j : Fin n // j ∈ J}, ∀ j, j ∈ J → (mk j).1 = j := by
    refine ⟨fun j => if h : j ∈ J then ⟨j, h⟩ else ⟨j0, hj0⟩, ?_⟩
    intro j hj
    dsimp only
    rw [dif_pos hj]
  have hcolorable : (K.induce X).Colorable q := by
    have hC : (K.induce X).Coloring {j : Fin n // j ∈ J} :=
      SimpleGraph.Coloring.mk (fun x => mk (col x.1)) (by
        intro x y hxy hEq
        have hadj : K.Adj x.1 y.1 := hxy
        have h1 : (mk (col x.1)).1 = col x.1 := hmk_val _ (hcol_mem _ x.2)
        have h2 : (mk (col y.1)).1 = col y.1 := hmk_val _ (hcol_mem _ y.2)
        have hEq' : (mk (col x.1)).1 = (mk (col y.1)).1 := congrArg Subtype.val hEq
        exact hproper x.1 y.1 x.2 y.2 hadj (by rw [← h1, ← h2]; exact hEq'))
    have hcc := hC.colorable
    rw [Fintype.card_coe] at hcc
    exact hcc
  refine ⟨hcolorable, ?_⟩
  -- ## the canonical `q`-clique
  obtain ⟨rr, hrr_form⟩ :
      ∃ rr : Fin n → W, ∀ j, (rr j = c j ∧ c j ∈ X) ∨ (rr j = d j ∧ c j ∉ X) := by
    refine ⟨fun j => if c j ∈ X then c j else d j, ?_⟩
    intro j
    by_cases h : c j ∈ X
    · exact Or.inl ⟨if_pos h, h⟩
    · exact Or.inr ⟨if_neg h, h⟩
  have hrr_mem : ∀ j, j ∈ J → rr j ∈ X := by
    intro j hj
    rcases hrr_form j with ⟨he, hc⟩ | ⟨he, hc⟩
    · rw [he]; exact hc
    · rw [he]
      rcases (hJmem j).1 hj with h' | h'
      · exact absurd h' hc
      · exact h'
  have hrr_cd : ∀ j, rr j = c j ∨ rr j = d j := by
    intro j
    rcases hrr_form j with ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl he
    · exact Or.inr he
  have hrr_col : ∀ j, col (rr j) = j := by
    intro j
    rcases hrr_cd j with h | h <;> rw [h]
    · exact hcol_c j
    · exact hcol_d j
  have hrr_inj : Function.Injective
      (fun j : {x : Fin n // x ∈ J} => (⟨rr j.1, hrr_mem j.1 j.2⟩ : X)) := by
    intro j j' h
    have hv : rr j.1 = rr j'.1 := congrArg Subtype.val h
    have := congrArg col hv
    rw [hrr_col, hrr_col] at this
    exact Subtype.ext this
  refine ⟨J.attach.image (fun j => (⟨rr j.1, hrr_mem j.1 j.2⟩ : X)), ?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    have hne : j.1 ≠ j'.1 := by
      intro h
      exact huv (Subtype.ext (show rr j.1 = rr j'.1 by rw [h]))
    show K.Adj (rr j.1) (rr j'.1)
    rcases hrr_cd j.1 with h | h <;> rcases hrr_cd j'.1 with h' | h' <;> rw [h, h']
    · exact (hright _ _ hne).1
    · exact (hright _ _ hne).2.1
    · exact (hright _ _ hne).2.2.1
    · exact (hright _ _ hne).2.2.2
  · rw [Finset.card_image_of_injective _ hrr_inj, Finset.card_attach]

end Workspace.ProofLemmas
