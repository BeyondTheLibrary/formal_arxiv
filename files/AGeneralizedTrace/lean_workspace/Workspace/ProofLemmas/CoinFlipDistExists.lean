import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist

open Workspace.Types.ProbVec Workspace.Types.BinVec Workspace.Types.CoinFlipDist

namespace CoinFlipDistExistsProof

/-- Per-coordinate Bernoulli factor for `S.p i`, expressed as `ENNReal`. -/
private noncomputable def factor {n : ℕ} (S : ProbVec n) (i : Fin n) (b : Bool) : ENNReal :=
  ENNReal.ofReal (if b then S.p i else 1 - S.p i)

private lemma factor_sum_eq_one {n : ℕ} (S : ProbVec n) (i : Fin n) :
    ∑ b : Bool, factor S i b = 1 := by
  have hp_nn : (0 : ℝ) ≤ S.p i := S.nonneg i
  have hp_le : S.p i ≤ 1 := S.le_one i
  have hone_minus : (0 : ℝ) ≤ 1 - S.p i := by linarith
  -- Sum over Bool: factor true + factor false
  rw [Fintype.sum_bool]
  -- Goal: factor S i true + factor S i false = 1
  unfold factor
  -- Goal: ofReal (if true then ...) + ofReal (if false then ...) = 1
  -- Reduce the if's via rfl-substitution using `show`
  show ENNReal.ofReal (S.p i) + ENNReal.ofReal (1 - S.p i) = 1
  rw [← ENNReal.ofReal_add hp_nn hone_minus]
  have hadd : S.p i + (1 - S.p i) = 1 := by ring
  rw [hadd]
  exact ENNReal.ofReal_one

/-- The product-of-Bernoulli mass function value at `b : BinVec n`. -/
private noncomputable def prodMass {n : ℕ} (S : ProbVec n) (b : BinVec n) : ENNReal :=
  ∏ i : Fin n, factor S i (b.bit i)

private lemma sum_prodMass_eq_one {n : ℕ} (S : ProbVec n) :
    ∑ b : BinVec n, prodMass S b = 1 := by
  unfold prodMass
  -- Reindex sum over BinVec to sum over (Fin n → Bool) via the equiv
  have hreindex : ∑ b : BinVec n, ∏ i : Fin n, factor S i (b.bit i)
      = ∑ f : Fin n → Bool, ∏ i : Fin n, factor S i (f i) := by
    apply Fintype.sum_equiv equivFun
    intro b
    rfl
  rw [hreindex]
  -- Use Finset.prod_univ_sum to convert ∑_f ∏_i factor i (f i) → ∏_i ∑_b factor i b
  -- Statement: ∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ Fintype.piFinset t, ∏ i, f i (x i)
  -- We want LHS in form: ∑ x ∈ Fintype.piFinset (fun _ => univ), ∏ i, factor S i (x i)
  have hsum_eq : (∑ f : Fin n → Bool, ∏ i : Fin n, factor S i (f i))
      = ∑ x ∈ Fintype.piFinset (fun (_ : Fin n) => (Finset.univ : Finset Bool)),
          ∏ i : Fin n, factor S i (x i) := by
    rfl
  rw [hsum_eq, ← Finset.prod_univ_sum]
  -- Goal: ∏ i, ∑ b ∈ Finset.univ, factor S i b = 1
  -- which equals ∏ i, ∑ b : Bool, factor S i b = 1 (defeq)
  have hone_per : ∀ i : Fin n, ∑ b ∈ (Finset.univ : Finset Bool), factor S i b = 1 := by
    intro i
    have := factor_sum_eq_one S i
    -- ∑ b : Bool, factor S i b = ∑ b ∈ Finset.univ, factor S i b (defeq)
    exact this
  simp only [hone_per, Finset.prod_const_one]

/-- The product-Bernoulli PMF on `BinVec n` for parameter `S`. -/
private noncomputable def productPMF {n : ℕ} (S : ProbVec n) : PMF (BinVec n) :=
  PMF.ofFintype (prodMass S) (sum_prodMass_eq_one S)

private lemma productPMF_apply {n : ℕ} (S : ProbVec n) (b : BinVec n) :
    productPMF S b = ∏ i : Fin n, ENNReal.ofReal (if b.bit i then S.p i else 1 - S.p i) := by
  unfold productPMF
  rw [PMF.ofFintype_apply]
  rfl

end CoinFlipDistExistsProof

theorem CoinFlipDistExists :
    ∀ {n : ℕ} (S : Workspace.Types.ProbVec.ProbVec n),
      Nonempty (Workspace.Types.CoinFlipDist.CoinFlipDist n S) := by
  intro n S
  refine ⟨{
    toPMF := CoinFlipDistExistsProof.productPMF S
    prod_factorisation := ?_
  }⟩
  intro b
  exact CoinFlipDistExistsProof.productPMF_apply S b
