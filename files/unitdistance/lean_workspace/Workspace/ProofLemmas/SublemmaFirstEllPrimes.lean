import Mathlib

/-- For every `ℓ : ℕ` there is a strictly increasing enumeration `r : Fin ℓ → ℕ+`
of the first `ℓ` primes congruent to `1 mod 3`: each `r i` is prime with
`(r i) % 3 = 1`, and the minimality clause holds — any prime `p ≡ 1 mod 3` that
is not among the `r i` exceeds every `r i`. -/
theorem SublemmaFirstEllPrimes :
    ∀ (ℓ : ℕ), ∃ r : Fin ℓ → ℕ+,
      StrictMono r ∧
      (∀ i, ((r i : ℕ)).Prime) ∧
      (∀ i, (r i : ℕ) % 3 = 1) ∧
      (∀ p : ℕ, p.Prime → p % 3 = 1 → (¬ ∃ i, (r i : ℕ) = p) → ∀ i, (r i : ℕ) < p) := by
  intro ℓ
  classical
  set pred : ℕ → Prop := fun n => n.Prime ∧ n % 3 = 1 with hpred
  -- The set of primes ≡ 1 mod 3 is infinite (Dirichlet).
  have hinf : {n | pred n}.Infinite := by
    have h := Nat.infinite_setOf_prime_and_modEq (q := 3) (a := 1) (by norm_num) (by decide)
    have hset : {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 3]} = {n | pred n} := by
      ext n
      simp only [Set.mem_setOf_eq, hpred, Nat.ModEq]
    rwa [hset] at h
  have hmem : ∀ n, pred (Nat.nth pred n) := fun n => Nat.nth_mem_of_infinite hinf n
  have hmono : StrictMono (Nat.nth pred) := Nat.nth_strictMono hinf
  refine ⟨fun i => ⟨Nat.nth pred i, (hmem i).1.pos⟩, ?_, ?_, ?_, ?_⟩
  · -- StrictMono r
    intro i j hij
    exact hmono hij
  · intro i; exact (hmem i).1
  · intro i; exact (hmem i).2
  · intro p hp hmp hnotin i
    have hpp : pred p := ⟨hp, hmp⟩
    have hcount : Nat.nth pred (Nat.count pred p) = p := Nat.nth_count hpp
    have hkge : ℓ ≤ Nat.count pred p := by
      by_contra hlt
      push_neg at hlt
      exact hnotin ⟨⟨Nat.count pred p, hlt⟩, hcount⟩
    have hik : (i : ℕ) < Nat.count pred p := lt_of_lt_of_le i.isLt hkge
    have hlt2 := hmono hik
    rw [hcount] at hlt2
    exact hlt2
