-- Cited from: Neukirch, Algebraic Number Theory (Neu99), Ch. I §8-9: multiplicativity of the ramification index e and residue degree f in a tower of extensions; consequently complete splitting is transitive in a tower ℚ ⊆ F ⊆ E.
-- Paper label: standard ANT (tower e,f multiplicativity)
-- NL statement: Let F, E be number fields with [Algebra F E], [Algebra ℚ F], [Algebra ℚ E], [IsScalarTower ℚ F E], with E/F and F/ℚ separable and FiniteDimensional F E. For a rational prime q : ℕ: SplitsCompletelyRat q E ↔ (SplitsCompletelyRat q F ∧ ∀ v ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 F), SplitsCompletely (F := F) (M := E) v). In particular the ⇐ direction yields SplitsCompletelyRat q E from complete splitting ℚ → F together with complete splitting of every intermediate prime F → E.
--
-- PROOF: The fundamental identity ∑_P e(P)·f(P) = [E:K] (Ideal.sum_ramification_inertia) turns
-- each `ncard = finrank` count into a consequence of `e = f = 1`. Tower multiplicativity of e
-- (Ideal.ramificationIdx_algebra_tower) and f (Ideal.inertiaDeg_algebra_tower) along
-- ℤ → 𝓞 F → 𝓞 E then relates the three levels. The descent direction reuses the
-- ProofLemmas SublemmaCompleteSplittingDescends / SublemmaSplitDescendsCount.
import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.SublemmaSplitDescendsEFOne
import Workspace.ProofLemmas.SublemmaSplitDescendsCount
import Workspace.ProofLemmas.SublemmaCompleteSplittingDescends

open scoped NumberField

open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

/-- Relative fundamental-identity count: if every prime over `v` in `𝓞 E` has `e = f = 1`,
then the number of such primes is `[E : F]`. -/
theorem SublemmaSplittingTransitive_relCount
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (v : Ideal (𝓞 F)) (hv_ne : v ≠ ⊥) [v.IsMaximal]
    (hef : ∀ P ∈ Ideal.primesOver v (𝓞 E),
      Ideal.ramificationIdx v P = 1 ∧ Ideal.inertiaDeg v P = 1) :
    (Ideal.primesOver v (𝓞 E)).ncard = Module.finrank F E := by
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) F E hv_ne
  set S := IsDedekindDomain.primesOverFinset v (𝓞 E) with hS
  have hcoe : (↑S : Set (Ideal (𝓞 E))) = v.primesOver (𝓞 E) :=
    IsDedekindDomain.coe_primesOverFinset hv_ne (𝓞 E)
  have hmem : ∀ P, P ∈ S ↔ P ∈ v.primesOver (𝓞 E) := fun P => by
    rw [← Finset.mem_coe, hcoe]
  have hsumcard : ∑ P ∈ S, Ideal.ramificationIdx v P * Ideal.inertiaDeg v P = S.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro P hP
    obtain ⟨he, hf⟩ := hef P ((hmem P).mp hP)
    rw [he, hf, one_mul]
  have hScard : (S.card : ℕ) = Module.finrank F E := by rw [← hsumcard, hsum]
  have hncardeq : (Ideal.primesOver v (𝓞 E)).ncard = S.card := by
    rw [← hcoe, Set.ncard_coe_finset]
  rw [hncardeq, hScard]

/-- Tower multiplicativity of `e` and `f` along `ℤ → 𝓞 F → 𝓞 E`, for a prime `P` of `𝓞 E`
lying over a prime `v` of `𝓞 F` which lies over `(q)`. -/
theorem SublemmaSplittingTransitive_towerEF
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra ℚ F] [Algebra ℚ E] [IsScalarTower ℚ F E]
    [FiniteDimensional F E] (q : ℕ) (hq : q.Prime)
    (v : Ideal (𝓞 F)) [hvp : v.IsPrime] [v.LiesOver (Ideal.span {(q : ℤ)})]
    (P : Ideal (𝓞 E)) [hPp : P.IsPrime] [P.LiesOver v] :
    Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) v * Ideal.ramificationIdx v P ∧
    Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P
      = Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) v * Ideal.inertiaDeg v P := by
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  haveI hpP : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(q : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  have hv_ne : v ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne v
  haveI hvmax : v.IsMaximal := hvp.isMaximal hv_ne
  haveI hPloq : P.LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans P v (Ideal.span {(q : ℤ)})
  have hftower : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P
      = Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) v * Ideal.inertiaDeg v P :=
    Ideal.inertiaDeg_algebra_tower (Ideal.span {(q : ℤ)}) v P
  have hmapv_ne : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact hv_ne
  have hmapq_ne : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact hqb_ne
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (‹P.LiesOver v›).over.le
  have hetower : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) v * Ideal.ramificationIdx v P :=
    Ideal.ramificationIdx_algebra_tower hmapv_ne hmapq_ne hle
  exact ⟨hetower, hftower⟩

theorem SublemmaSplittingTransitive
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra ℚ F] [Algebra ℚ E] [IsScalarTower ℚ F E]
    [Algebra.IsSeparable F E] [Algebra.IsSeparable ℚ F]
    [FiniteDimensional F E] (q : ℕ) :
    SplitsCompletelyRat q E ↔
      (SplitsCompletelyRat q F ∧
        ∀ v ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 F),
          SplitsCompletely (F := F) (M := E) v) := by
  constructor
  · -- (⇒)
    intro hE
    obtain ⟨hqP, hncardE, hefE⟩ := hE
    refine ⟨SublemmaCompleteSplittingDescends E F q ⟨hqP, hncardE, hefE⟩, ?_⟩
    intro v hv
    obtain ⟨hvp, hvlo⟩ := hv
    haveI : v.IsPrime := hvp
    haveI : v.LiesOver (Ideal.span {(q : ℤ)}) := hvlo
    have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hqP.ne_zero
    have hv_ne : v ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne v
    haveI hvmax : v.IsMaximal := hvp.isMaximal hv_ne
    have hef : ∀ P ∈ Ideal.primesOver v (𝓞 E),
        Ideal.ramificationIdx v P = 1 ∧ Ideal.inertiaDeg v P = 1 := by
      intro P hP
      obtain ⟨hPp, hPlo⟩ := hP
      haveI : P.IsPrime := hPp
      haveI : P.LiesOver v := hPlo
      haveI : P.LiesOver (Ideal.span {(q : ℤ)}) :=
        Ideal.LiesOver.trans P v (Ideal.span {(q : ℤ)})
      have hPmem : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 E) := ⟨hPp, inferInstance⟩
      obtain ⟨heP, hfP⟩ := hefE P hPmem
      obtain ⟨het, hft⟩ := SublemmaSplittingTransitive_towerEF F E q hqP v P
      rw [heP] at het
      rw [hfP] at hft
      exact ⟨Nat.eq_one_of_mul_eq_one_left het.symm, Nat.eq_one_of_mul_eq_one_left hft.symm⟩
    exact ⟨SublemmaSplittingTransitive_relCount F E v hv_ne hef, hef⟩
  · -- (⇐)
    rintro ⟨hF, hvsplit⟩
    obtain ⟨hqP, hncardF, hefF⟩ := hF
    have hefE : ∀ P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 E),
        Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1 := by
      intro P hP
      obtain ⟨hPp, hPlo⟩ := hP
      haveI : P.IsPrime := hPp
      haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hPlo
      set v := P.under (𝓞 F) with hvdef
      haveI hvp : v.IsPrime := inferInstance
      haveI hPlov : P.LiesOver v := ⟨rfl⟩
      haveI hvlo : v.LiesOver (Ideal.span {(q : ℤ)}) := by
        refine ⟨?_⟩
        show Ideal.span {(q : ℤ)} = v.under ℤ
        rw [hvdef, Ideal.under_under]
        exact hPlo.over
      have hvmem : v ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 F) := ⟨hvp, hvlo⟩
      obtain ⟨hev, hfv⟩ := hefF v hvmem
      have hPmemv : P ∈ Ideal.primesOver v (𝓞 E) := ⟨hPp, hPlov⟩
      obtain ⟨_, hefvP⟩ := hvsplit v hvmem
      obtain ⟨hevP, hfvP⟩ := hefvP P hPmemv
      obtain ⟨het, hft⟩ := SublemmaSplittingTransitive_towerEF F E q hqP v P
      rw [hev, hevP, one_mul] at het
      rw [hfv, hfvP, one_mul] at hft
      exact ⟨het, hft⟩
    exact ⟨hqP, SublemmaSplitDescendsCount E q hqP hefE, hefE⟩
