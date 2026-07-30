import Mathlib
import Workspace.ProofLemmas.IdealNormCount

/-!
# `#{I : N(I) ≤ m} ≤ #{n-tuples of positive integers with product ≤ m}`

The combinatorial ideal-to-divisor-tuple comparison underlying `IdealCountByNormBound` (equivalently
the classical `#{I : N(I) = k} ≤ d_n(k)`), for `n = [K : ℚ]`.

The injection.  For a rational prime `q` there are at most `n` primes of `𝓞 K` above `q`
(`card_Sq_le`, from `∑_{P|q} e_P f_P = n`), so they can be indexed injectively by `Fin n` (`idxAt`).
Writing `q(P) = absNorm (P ∩ ℤ)` for the rational prime below `P`, every nonzero prime gets an index
`idx P`, and two nonzero primes with the same `q(·)` and the same index coincide (`idx_inj`).

For a nonzero ideal `I` put `Φ I i = ∏_{idx P = i} N(P)^{v_P(I)}` (a product over the multiset
`normalizedFactors I`).  Then

* `∏ i, Φ I i = N(I)` (`prod_Φ`), by partitioning the factor multiset and multiplicativity of
  `Ideal.absNorm`;
* `Φ` is injective on nonzero ideals (`Φ_inj`): since `N(P) = q(P)^{f(P)}`, reading the `q(P)`-adic
  valuation of `Φ I (idx P)` returns `v_P(I) · f(P)`, and `f(P) > 0`, so all the valuations of `I`
  — hence `normalizedFactors I`, hence `I` — are determined by `Φ I`.
-/

open scoped NumberField
open UniqueFactorizationMonoid

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.IdealCountInjection

variable (K : Type) [Field K] [NumberField K]

/-- The rational prime below a prime ideal, as a natural number. -/
noncomputable def qOf (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (Ideal.under ℤ P)

/-- The finset of primes of `𝓞 K` above the rational prime `q`. -/
noncomputable def Sq (q : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K)

/-- There are at most `[K : ℚ]` primes above a rational prime. -/
theorem card_Sq_le (q : ℕ) (hq : q.Prime) : (Sq K q).card ≤ Module.finrank ℚ K := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hmax : (Ideal.span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  have hne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by simp [hq.ne_zero]
  have hsum := Ideal.sum_ramification_inertia (S := 𝓞 K) (K := ℚ) (L := K)
    (p := Ideal.span {(q : ℤ)}) hne
  rw [Sq, ← hsum, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum ?_
  intro P hP
  have hPmem : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 K) := by
    rw [← IsDedekindDomain.coe_primesOverFinset hne (𝓞 K)] at *
    exact hP
  obtain ⟨hPprime, hPlies⟩ := hPmem
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hPlies
  have he : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hne
  have hf : 0 < Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P := Ideal.inertiaDeg_pos _ _
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he (Nat.pos_iff_ne_zero.mp hf))

/-- The residue degree of a prime of `𝓞 K` over the rational prime below it. -/
noncomputable def fOf (P : Ideal (𝓞 K)) : ℕ := Ideal.inertiaDeg (Ideal.under ℤ P) P

variable {K}

theorem qOf_prime (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) : (qOf K P).Prime := by
  haveI : NeZero P := ⟨hP0⟩
  exact Nat.absNorm_under_prime P

theorem under_eq_span (P : Ideal (𝓞 K)) :
    Ideal.under ℤ P = Ideal.span {(qOf K P : ℤ)} := by
  rw [qOf, Int.ideal_span_absNorm_eq_self]

theorem liesOver_qOf (P : Ideal (𝓞 K)) : P.LiesOver (Ideal.span {(qOf K P : ℤ)}) :=
  Int.liesOver_span_absNorm P

theorem mem_Sq_qOf (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) : P ∈ Sq K (qOf K P) := by
  haveI := liesOver_qOf P
  have hq := qOf_prime P hP0
  haveI : Fact (qOf K P).Prime := ⟨hq⟩
  have hne : (Ideal.span {((qOf K P : ℕ) : ℤ)}) ≠ ⊥ := by simp [hq.ne_zero]
  rw [Sq, ← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hne (𝓞 K)]
  exact ⟨hP, inferInstance⟩

theorem absNorm_eq_qOf_pow (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    Ideal.absNorm P = (qOf K P) ^ (fOf K P) := by
  haveI : NeZero P := ⟨hP0⟩
  have hpp : (Ideal.under ℤ P).IsPrime := Ideal.IsPrime.under ℤ P
  have hne : Ideal.under ℤ P ≠ ⊥ := by
    intro h
    exact hP0 (Ideal.eq_bot_of_comap_eq_bot h)
  haveI : P.LiesOver (Ideal.under ℤ P) := ⟨rfl⟩
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P (Ideal.under ℤ P) hpp hne

theorem fOf_pos (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) : 0 < fOf K P := by
  haveI : P.LiesOver (Ideal.under ℤ P) := ⟨rfl⟩
  have hpp : (Ideal.under ℤ P).IsPrime := Ideal.IsPrime.under ℤ P
  have hne : Ideal.under ℤ P ≠ ⊥ := fun h => hP0 (Ideal.eq_bot_of_comap_eq_bot h)
  haveI : (Ideal.under ℤ P).IsMaximal := hpp.isMaximal hne
  exact Ideal.inertiaDeg_pos _ _

variable (K)

/-- An injective indexing of the primes above a fixed rational prime by `Fin [K:ℚ]`. -/
noncomputable def idxAt (q : ℕ) (P : Ideal (𝓞 K)) : Fin (Module.finrank ℚ K) :=
  if h : q.Prime ∧ P ∈ Sq K q then
    Fin.castLE (card_Sq_le K q h.1) ((Sq K q).equivFin ⟨P, h.2⟩)
  else ⟨0, Module.finrank_pos⟩

/-- The index of a prime of `𝓞 K`. -/
noncomputable def idx (P : Ideal (𝓞 K)) : Fin (Module.finrank ℚ K) := idxAt K (qOf K P) P

variable {K}

theorem idxAt_inj {q : ℕ} (hq : q.Prime) {P P' : Ideal (𝓞 K)}
    (hP : P ∈ Sq K q) (hP' : P' ∈ Sq K q) (h : idxAt K q P = idxAt K q P') : P = P' := by
  rw [idxAt, dif_pos ⟨hq, hP⟩, idxAt, dif_pos ⟨hq, hP'⟩] at h
  have h1 := Fin.castLE_injective (card_Sq_le K q hq) h
  have h2 := (Sq K q).equivFin.injective h1
  exact congrArg Subtype.val h2

/-- Two nonzero primes with the same rational prime below and the same index are equal. -/
theorem idx_inj {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime] (hP0 : P ≠ ⊥) (hP'0 : P' ≠ ⊥)
    (hq : qOf K P = qOf K P') (h : idx K P = idx K P') : P = P' := by
  have hmem : P ∈ Sq K (qOf K P) := mem_Sq_qOf P hP0
  have hmem' : P' ∈ Sq K (qOf K P) := hq ▸ mem_Sq_qOf P' hP'0
  refine idxAt_inj (qOf_prime P hP0) hmem hmem' ?_
  rw [idx, idx, hq] at h
  rw [← hq] at h
  exact h

/-- Partitioning a multiset by a `Fin n`-valued function multiplies out. -/
theorem prod_fiber_prod {α : Type*} {n : ℕ} (f : α → Fin n) (g : α → ℕ) (s : Multiset α) :
    ∏ i : Fin n, ((s.filter (fun a => f a = i)).map g).prod = (s.map g).prod := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have key : ∀ i : Fin n, (((a ::ₘ t).filter (fun x => f x = i)).map g).prod
          = (if f a = i then g a else 1) * ((t.filter (fun x => f x = i)).map g).prod := by
        intro i
        by_cases h : f a = i
        · simp [Multiset.filter_cons, h]
        · simp [Multiset.filter_cons, h]
      rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib, ih,
        Multiset.map_cons, Multiset.prod_cons]
      congr 1
      simpa using Finset.prod_ite_eq Finset.univ (f a) (fun _ => g a)

variable (K)

/-- The `i`-th coordinate of the divisor tuple attached to an ideal. -/
noncomputable def Φ (I : Ideal (𝓞 K)) (i : Fin (Module.finrank ℚ K)) : ℕ :=
  open Classical in
  (((normalizedFactors I).filter (fun P => idx K P = i)).map Ideal.absNorm).prod

variable {K}

theorem prod_Φ (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    ∏ i, Φ K I i = Ideal.absNorm I := by
  classical
  have h1 : ∏ i, Φ K I i = ((normalizedFactors I).map Ideal.absNorm).prod :=
    prod_fiber_prod (idx K) Ideal.absNorm (normalizedFactors I)
  rw [h1, ← map_multiset_prod, associated_iff_eq.mp (prod_normalizedFactors hI)]

/-- Every element of `normalizedFactors I` is a nonzero prime ideal. -/
theorem mem_normalizedFactors_prime {I P : Ideal (𝓞 K)} (hI : I ≠ 0)
    (hP : P ∈ normalizedFactors I) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp : Prime P := prime_of_normalized_factor P hP
  refine ⟨Ideal.isPrime_of_prime hp, ?_⟩
  intro h
  apply zero_notMem_normalizedFactors I
  have h0 : (0 : Ideal (𝓞 K)) = P := by rw [h]; rfl
  rwa [h0]

theorem Φ_pos (I : Ideal (𝓞 K)) (hI : I ≠ 0) (i : Fin (Module.finrank ℚ K)) : 0 < Φ K I i := by
  classical
  rw [Φ]
  refine Multiset.prod_pos ?_
  intro a ha
  obtain ⟨P, hPmem, rfl⟩ := Multiset.mem_map.mp ha
  have hP := Multiset.mem_of_mem_filter hPmem
  have := mem_normalizedFactors_prime hI hP
  exact Nat.pos_of_ne_zero (fun h => this.2 (Ideal.absNorm_eq_zero_iff.mp h))

/-- The local weight of a prime at a rational prime `q`. -/
noncomputable def w (q : ℕ) (P : Ideal (𝓞 K)) : ℕ := if qOf K P = q then fOf K P else 0

theorem factorization_prod_map (q : ℕ) (hq : q.Prime) :
    ∀ (s : Multiset (Ideal (𝓞 K))), (∀ P ∈ s, P.IsPrime ∧ P ≠ ⊥) →
      ((s.map Ideal.absNorm).prod).factorization q = (s.map (w q)).sum := by
  classical
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons P t ih =>
      intro hs
      have hP := hs P (Multiset.mem_cons_self P t)
      haveI : P.IsPrime := hP.1
      have ht : ∀ P' ∈ t, P'.IsPrime ∧ P' ≠ ⊥ := fun P' hP' => hs P' (Multiset.mem_cons_of_mem hP')
      have hne1 : Ideal.absNorm P ≠ 0 := fun h => hP.2 (Ideal.absNorm_eq_zero_iff.mp h)
      have hne2 : ((t.map Ideal.absNorm).prod) ≠ 0 := by
        refine Nat.pos_iff_ne_zero.mp (Multiset.prod_pos ?_)
        intro a ha
        obtain ⟨P', hP'mem, rfl⟩ := Multiset.mem_map.mp ha
        exact Nat.pos_of_ne_zero
          (fun h => (ht P' hP'mem).2 (Ideal.absNorm_eq_zero_iff.mp h))
      rw [Multiset.map_cons, Multiset.prod_cons, Nat.factorization_mul hne1 hne2]
      simp only [Finsupp.add_apply]
      rw [ih ht, Multiset.map_cons, Multiset.sum_cons]
      congr 1
      -- the local factorization of `absNorm P`
      rw [absNorm_eq_qOf_pow P hP.2, Nat.factorization_pow]
      have hqP : (qOf K P).Prime := qOf_prime P hP.2
      rw [hqP.factorization]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, w]
      by_cases h : qOf K P = q
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]

theorem sum_w_eq (P : Ideal (𝓞 K)) :
    ∀ (s : Multiset (Ideal (𝓞 K))), (∀ P' ∈ s, qOf K P' = qOf K P → P' = P) →
      (s.map (w (qOf K P))).sum = Multiset.count P s * fOf K P := by
  classical
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons P' t ih =>
      intro hs
      have ht : ∀ P'' ∈ t, qOf K P'' = qOf K P → P'' = P :=
        fun P'' hP'' => hs P'' (Multiset.mem_cons_of_mem hP'')
      rw [Multiset.map_cons, Multiset.sum_cons, ih ht]
      by_cases h : P' = P
      · subst h
        rw [Multiset.count_cons_self, w, if_pos rfl]
        ring
      · have hq : qOf K P' ≠ qOf K P := fun hcon => h (hs P' (Multiset.mem_cons_self P' t) hcon)
        rw [w, if_neg hq, Multiset.count_cons_of_ne (Ne.symm h), zero_add]

open Workspace.ProofLemmas.IdealNormCount.DivisorCount in
theorem factorization_Φ (I : Ideal (𝓞 K)) (hI : I ≠ 0) (P : Ideal (𝓞 K)) [P.IsPrime]
    (hP0 : P ≠ ⊥) :
    (Φ K I (idx K P)).factorization (qOf K P)
      = Multiset.count P (normalizedFactors I) * fOf K P := by
  classical
  set s := (normalizedFactors I).filter (fun P' => idx K P' = idx K P) with hs
  have hprimes : ∀ P' ∈ s, P'.IsPrime ∧ P' ≠ ⊥ := fun P' hP' =>
    mem_normalizedFactors_prime hI (Multiset.mem_of_mem_filter hP')
  have hΦ : Φ K I (idx K P) = ((s.map Ideal.absNorm).prod) := rfl
  rw [hΦ, factorization_prod_map (qOf K P) (qOf_prime P hP0) s hprimes]
  have huniq : ∀ P' ∈ s, qOf K P' = qOf K P → P' = P := by
    intro P' hP' hq
    have h1 : idx K P' = idx K P := (Multiset.mem_filter.mp hP').2
    have h2 := hprimes P' hP'
    haveI : P'.IsPrime := h2.1
    exact idx_inj h2.2 hP0 hq h1
  rw [sum_w_eq P s huniq]
  congr 1
  rw [hs, Multiset.count_filter]
  simp

theorem Φ_inj {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) (h : Φ K I = Φ K J) : I = J := by
  classical
  have hnf : normalizedFactors I = normalizedFactors J := by
    ext P
    by_cases hPp : P.IsPrime ∧ P ≠ ⊥
    · haveI : P.IsPrime := hPp.1
      have h1 := factorization_Φ I hI P hPp.2
      have h2 := factorization_Φ J hJ P hPp.2
      rw [h] at h1
      rw [h1] at h2
      have hf : 0 < fOf K P := fOf_pos P hPp.2
      exact Nat.eq_of_mul_eq_mul_right hf h2
    · have e1 : Multiset.count P (normalizedFactors I) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        exact hPp (mem_normalizedFactors_prime hI hmem)
      have e2 : Multiset.count P (normalizedFactors J) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        exact hPp (mem_normalizedFactors_prime hJ hmem)
      rw [e1, e2]
  have hIp : (normalizedFactors I).prod = I := associated_iff_eq.mp (prod_normalizedFactors hI)
  have hJp : (normalizedFactors J).prod = J := associated_iff_eq.mp (prod_normalizedFactors hJ)
  rw [← hIp, ← hJp, hnf]

open Workspace.ProofLemmas.IdealNormCount.DivisorCount in
/-- **The ideal-to-divisor-tuple comparison.**  The number of nonzero ideals of `𝓞 K` of norm at
most `m` is at most the number of `[K:ℚ]`-tuples of positive integers with product at most `m`. -/
theorem idealCount_le_D (m : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
      ≤ (D (Module.finrank ℚ K) m).card := by
  classical
  haveI : Finite ↥(D (Module.finrank ℚ K) m) := FinsetCoe.fintype _ |>.finite
  have hmap : ∀ (I : Ideal (𝓞 K)), I ≠ 0 → Ideal.absNorm I ≤ m → Φ K I ∈ D (Module.finrank ℚ K) m := by
    intro I hI hIm
    have hprod : ∏ i, Φ K I i = Ideal.absNorm I := prod_Φ I hI
    rw [mem_D]
    have hpos : ∀ i, 1 ≤ Φ K I i := fun i => Φ_pos I hI i
    refine ⟨fun i => ⟨hpos i, ?_⟩, by rw [hprod]; exact hIm⟩
    calc Φ K I i ≤ ∏ j, Φ K I j := Finset.single_le_prod' (fun j _ => hpos j) (Finset.mem_univ i)
      _ = Ideal.absNorm I := hprod
      _ ≤ m := hIm
  set g : {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} → ↥(D (Module.finrank ℚ K) m) :=
    fun I => ⟨Φ K I.1, hmap I.1 I.2.1 I.2.2⟩ with hg
  have hginj : Function.Injective g := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ hij
    have : Φ K I = Φ K J := congrArg Subtype.val hij
    exact Subtype.ext (Φ_inj hI.1 hJ.1 this)
  calc Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
      ≤ Nat.card ↥(D (Module.finrank ℚ K) m) := Nat.card_le_card_of_injective g hginj
    _ = (D (Module.finrank ℚ K) m).card := by simp

end Workspace.ProofLemmas.IdealCountInjection
