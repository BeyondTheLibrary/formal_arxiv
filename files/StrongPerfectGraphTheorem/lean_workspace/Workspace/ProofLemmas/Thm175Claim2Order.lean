import Workspace.ProofLemmas.Thm175Claim2Basics

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm175Claim2Order

open Workspace.ProofLemmas.Thm175Claim2Basics

/-- Exchanging the two sets does not change the lines. -/
theorem line_swap {A B : ℕ → Prop} {a b : ℕ} (h : Line A B a b) : Line B A a b := by
  exact ⟨h.1, h.2.1, h.2.2.1.symm, fun i hi hj => (h.2.2.2 i hi hj).symm⟩

/-- Between differently marked vertices there is a line: take the first
vertex of the second kind, then the last vertex of the first kind before it. -/
theorem exists_line_between (A B : ℕ → Prop) (a b : ℕ)
    (ha : 0 < a) (hab : a < b) (hA : A a) (hB : B b) :
    ∃ i j, a ≤ i ∧ j ≤ b ∧ Line A B i j := by
  classical
  have hex : ∃ j, a < j ∧ j ≤ b ∧ B j := ⟨b, hab, le_rfl, hB⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  have hjmin : ∀ k, a < k → k < j → ¬ B k := by
    intro k hak hkj hk
    have := Nat.find_min' hex ⟨hak, by omega, hk⟩
    omega
  let i := Nat.findGreatest A (j - 1)
  have hai : a ≤ i := Nat.le_findGreatest (by omega) hA
  have hij : i < j := by
    have := Nat.findGreatest_le (P := A) (n := j - 1)
    omega
  have hiA : A i := Nat.findGreatest_spec (by omega) hA
  refine ⟨i, j, hai, hj.2.1, by omega, hij, Or.inl ⟨hiA, hj.2.2⟩, ?_⟩
  intro k hik hkj
  refine ⟨?_, hjmin k (by omega) hkj⟩
  exact Nat.findGreatest_is_greatest (n := j - 1) hik (by omega)

/-- PAPER: "If there is a line contained in the path `p_r-⋯-p_s`, ...
one of the paths `p_r-⋯-p_h` and `p_k-⋯-p_s` is odd, contrary to the
minimality of `s-r`."
This is the same parity argument as induction on the right endpoint of a
line. The previous vertex of the right endpoint's kind is either index zero
or the start of an earlier line. -/
theorem even_line_ends (A B : ℕ → Prop)
    (hA0 : A 0) (hB0 : B 0)
    (hsep : ∀ i, A i → B i → i = 0)
    (hcleanA : ∀ i j, i + 1 < j → A i → A j →
      (∀ k, i < k → k < j → ¬ A k) → Even (j - i))
    (hcleanB : ∀ i j, i + 1 < j → B i → B j →
      (∀ k, i < k → k < j → ¬ B k) → Even (j - i))
    (hlines : ∀ a b, Line A B a b → Even (b - a)) :
    ∀ a b, Line A B a b → Even a ∧ Even b := by
  classical
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    intro hl
    have hablt := hl.2.1
    have finish (C D : ℕ → Prop) (hD0 : D 0)
        (hCa : C a) (hDb : D b) (hDa : ¬ D a)
        (hclear : ∀ k, a < k → k < b → ¬ D k)
        (hcleanD : ∀ i j, i + 1 < j → D i → D j →
          (∀ k, i < k → k < j → ¬ D k) → Even (j - i))
        (hmap : ∀ i j, Line D C i j → Line A B i j) : Even a ∧ Even b := by
      let t := Nat.findGreatest D (a - 1)
      have ht : t < a := by
        have := Nat.findGreatest_le (P := D) (n := a - 1)
        have := hl.1
        omega
      have htD : D t := Nat.findGreatest_spec (Nat.zero_le _) hD0
      have htEven : Even t := by
        by_cases ht0 : t = 0
        · simp [ht0]
        obtain ⟨i, j, hti, hja, hij⟩ :=
          exists_line_between D C t a (by omega) ht htD hCa
        have hijlt := hij.2.1
        have hiD : D i := by
          rcases hij.2.2.1 with h | h
          · exact h.1
          · by_cases hit : i = t
            · simpa [hit] using htD
            have hn := Nat.findGreatest_is_greatest (P := D) (n := a - 1)
              (show t < j by omega) (show j ≤ a - 1 by
                by_contra hn
                have hje : j = a := by omega
                exact hDa (hje ▸ h.2))
            exact (hn h.2).elim
        have hit : i = t := by
          by_contra hn
          exact (Nat.findGreatest_is_greatest (P := D) (n := a - 1)
            (show t < i by omega) (show i ≤ a - 1 by omega)) hiD
        have he := ih j (by omega) i (hmap i j hij)
        simpa [hit] using he.1
      have hgap : Even (b - t) := by
        apply hcleanD t b (by have := hl.2.1; omega) htD hDb
        intro k htk hkb
        rcases lt_trichotomy k a with hka | rfl | hak
        · exact Nat.findGreatest_is_greatest (n := a - 1) htk (by omega)
        · exact hDa
        · exact hclear k hak hkb
      have hline := hlines a b hl
      simp only [Nat.even_iff] at htEven hgap hline ⊢
      constructor <;> omega
    rcases hl.2.2.1 with h | h
    · apply finish A B hB0 h.1 h.2
        (fun hBa => by have := hsep a h.1 hBa; have := hl.1; omega)
        (fun k hk hj => (hl.2.2.2 k hk hj).2) hcleanB
      exact fun i j h => line_swap h
    · apply finish B A hA0 h.1 h.2
        (fun hAa => by have := hsep a hAa h.1; have := hl.1; omega)
        (fun k hk hj => (hl.2.2.2 k hk hj).1) hcleanA
      exact fun _ _ h => h

/-- PAPER: "Choose `j` ... maximum such that `{p_j,…,p_n}` includes a
line. ... `W_k ∩ {p_j,…,p_n} = {p_j}`. ... So `n-j` is even."
Together with the parity of all line ends, this contradicts the odd path
length. This is the final index argument of claim (2). -/
theorem even_lines_absurd (A B : ℕ → Prop) (n : ℕ) (hn : Odd n)
    (hA0 : A 0) (hB0 : B 0)
    (hbound : ∀ i, A i ∨ B i → i ≤ n)
    (hsep : ∀ i, A i → B i → i = 0)
    (hA : ∃ i, 0 < i ∧ A i) (hB : ∃ i, 0 < i ∧ B i)
    (hcleanA : ∀ i j, i + 1 < j → A i → A j →
      (∀ k, i < k → k < j → ¬ A k) → Even (j - i))
    (hcleanB : ∀ i j, i + 1 < j → B i → B j →
      (∀ k, i < k → k < j → ¬ B k) → Even (j - i))
    (htailA : ∀ i, 0 < i → i + 2 ≤ n → A i →
      (∀ k, i < k → ¬ A k) → Even (n - i))
    (htailB : ∀ i, 0 < i → i + 2 ≤ n → B i →
      (∀ k, i < k → ¬ B k) → Even (n - i))
    (hlines : ∀ a b, Line A B a b → Even (b - a)) : False := by
  classical
  have hend := even_line_ends A B hA0 hB0 hsep hcleanA hcleanB hlines
  have hex : ∃ a b, Line A B a b := by
    obtain ⟨a, ha, hAa⟩ := hA
    obtain ⟨b, hb, hBb⟩ := hB
    have hab : a ≠ b := by
      rintro rfl
      have := hsep a hAa hBb
      omega
    rcases lt_or_gt_of_ne hab with h | h
    · obtain ⟨i, j, _, _, hl⟩ := exists_line_between A B a b ha h hAa hBb
      exact ⟨i, j, hl⟩
    · obtain ⟨i, j, _, _, hl⟩ := exists_line_between B A b a hb h hBb hAa
      exact ⟨i, j, line_swap hl⟩
  have line_bound : ∀ a b, Line A B a b → b ≤ n := by
    intro a b hl
    apply hbound b
    rcases hl.2.2.1 with h | h
    · exact Or.inr h.2
    · exact Or.inl h.2
  let a := Nat.findGreatest (fun a => ∃ b, Line A B a b) n
  obtain ⟨a₀, b₀, hl₀⟩ := hex
  have ha₀ : a₀ ≤ n := by have := line_bound a₀ b₀ hl₀; have := hl₀.2.1; omega
  obtain ⟨b, hl⟩ := Nat.findGreatest_spec
    (P := fun a => ∃ b, Line A B a b) ha₀ ⟨b₀, hl₀⟩
  have hmax : ∀ i j, Line A B i j → i ≤ a := by
    intro i j hij
    apply Nat.le_findGreatest
    · have := line_bound i j hij
      have := hij.2.1
      omega
    · exact ⟨j, hij⟩
  have hea := (hend a b hl).1
  have habEven := hlines a b hl
  have hab2 : a + 2 ≤ n := by
    have := line_bound a b hl
    have := hl.2.1
    rw [Nat.even_iff] at habEven
    omega
  have finish (C D : ℕ → Prop) (hCa : C a) (hDb : D b)
      (hCb : ¬ C b) (hclear : ∀ k, a < k → k < b → ¬ C k)
      (hmap : ∀ i j, Line D C i j → Line A B i j)
      (htail : ∀ i, 0 < i → i + 2 ≤ n → C i →
        (∀ k, i < k → ¬ C k) → Even (n - i)) : False := by
    have hlast : ∀ k, a < k → ¬ C k := by
      intro k hak hk
      rcases lt_trichotomy k b with hkb | rfl | hbk
      · exact hclear k hak hkb hk
      · exact hCb hk
      · obtain ⟨i, j, hbi, _, hij⟩ := exists_line_between D C b k
          (by have := hl.1; have := hl.2.1; omega) hbk hDb hk
        have := hmax i j (hmap i j hij)
        have := hl.2.1
        omega
    have he := htail a hl.1 hab2 hCa hlast
    rw [Nat.even_iff] at he hea
    rw [Nat.odd_iff] at hn
    omega
  rcases hl.2.2.1 with h | h
  · exact finish A B h.1 h.2
      (fun hAb => by have := hsep b hAb h.2; have := hl.1; have := hl.2.1; omega)
      (fun k hk hj => (hl.2.2.2 k hk hj).1) (fun _ _ h => line_swap h) htailA
  · exact finish B A h.1 h.2
      (fun hBb => by have := hsep b h.2 hBb; have := hl.1; have := hl.2.1; omega)
      (fun k hk hj => (hl.2.2.2 k hk hj).2) (fun _ _ h => h) htailB

end Workspace.ProofLemmas.Thm175Claim2Order
