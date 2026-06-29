import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.Path4FullQ
import Workspace.ProofLemmas.Path4CentralCDF
import Workspace.ProofLemmas.QFactorBounds
import Workspace.ProofLemmas.CentralBinomialLowerTailWide

/-!
# Path4WindowQ — windowed residual product vs. full residual product

`signedInner`'s per-offset `Q_e(r)`/`Q_o(r)` factors are products of `1 - α·B`
over the *window* of `n/2` consecutive global indices `{(n/4)+r, …, (n/4)+r+n/2-1}`
(filtered by parity).  `Path4FullQ.fullQeven`/`fullQodd` are the same product over
*all* indices `{0,…,n}` of one parity.  Because the window lies inside `[0,n]` and
each factor lies in `[0,1]`, the windowed product is a SUPER-set bound of the full
product, and the gap is controlled by the binomial mass that lies OUTSIDE the window,
which is a left+right tail bounded by `central_binomial_left_cdf_le`.

Main results: `windowQe_sub_fullQeven_le` and `windowQo_sub_fullQodd_le`.
-/

set_option maxHeartbeats 4000000

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression

namespace Workspace.ProofLemmas.Path4WindowQ

/-- Windowed residual product over even global indices, byte-for-byte matching
`signedInner`'s `Q_e`. -/
noncomputable def windowQe (n : ℕ) (α : ℝ) (r : ℤ) : ℝ :=
  ∏ j ∈ (Finset.univ.filter (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 0)),
    (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))

/-- Windowed residual product over odd global indices, byte-for-byte matching
`signedInner`'s `Q_o`. -/
noncomputable def windowQo (n : ℕ) (α : ℝ) (r : ℤ) : ℝ :=
  ∏ j ∈ (Finset.univ.filter (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 1)),
    (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))

/-! ## The single global factor function -/

/-- The single binomial residual factor at global index `idx`. -/
noncomputable def F (n : ℕ) (α : ℝ) (idx : ℕ) : ℝ :=
  1 - α * ((Nat.choose n idx : ℝ) * (2 ^ n : ℝ)⁻¹)

/-! ## Generic `1 - ∏(1-x) ≤ ∑ x` helper -/

/-- For `x i ∈ [0,1]`, `1 - ∏(1 - x i) ≤ ∑ x i`. -/
lemma one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∏ i ∈ s, (1 - x i) ≤ ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hx0' : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
      have hx1' : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
      have ihs := ih hx0' hx1'
      have hpa0 : (0:ℝ) ≤ ∏ i ∈ s, (1 - x i) :=
        Finset.prod_nonneg (fun i hi => by have := hx1 i (Finset.mem_insert_of_mem hi); linarith)
      have hpa1 : ∏ i ∈ s, (1 - x i) ≤ 1 :=
        Finset.prod_le_one
          (fun i hi => by have := hx1 i (Finset.mem_insert_of_mem hi); linarith)
          (fun i hi => by have := hx0 i (Finset.mem_insert_of_mem hi); linarith)
      have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
      -- 1 - (1 - x a)·P = x a + (1 - x a)·(1 - P) ≤ x a + (1 - P) ≤ x a + ∑
      nlinarith [ihs, hpa0, hpa1, hxa0, mul_nonneg hxa0 hpa0]

/-! ## Window arithmetic (n % 8 = 1, |r| ≤ n/8) -/

/-- The window low endpoint as a natural number. -/
noncomputable def lo (n : ℕ) (r : ℤ) : ℕ := ((n / 4 : ℤ) + r).toNat

/-- Under `n%8=1` and `|r| ≤ n/8`, the window `[lo, lo+n/2)` lies inside `[0,n+1)`,
and `lo ≥ 3n/8 - (something)`.  We package the facts we need. -/
lemma window_facts (n : ℕ) (hn : (10^12:ℕ) ≤ n) (hmod : n % 8 = 1) (r : ℤ)
    (hr : -((n:ℤ)/8) ≤ r) (hr' : r ≤ (n:ℤ)/8) :
    0 ≤ (n/4 : ℤ) + r ∧
    (lo n r : ℤ) = (n/4 : ℤ) + r ∧
    lo n r + n / 2 ≤ n + 1 ∧
    lo n r ≤ 3 * n / 8 + 1 ∧
    n ≤ lo n r + n / 2 + (3 * n / 8 + 1) := by
  have hn1 : 1 ≤ n := by omega
  -- integer divisions
  have hdiv8 : (n:ℤ)/8 = ((n/8 : ℕ) : ℤ) := by
    exact_mod_cast (Int.natCast_ediv n 8).symm
  have h0le : 0 ≤ (n/4 : ℤ) + r := by
    have : (n:ℤ)/4 = ((n/4 : ℕ) : ℤ) := by exact_mod_cast (Int.natCast_ediv n 4).symm
    rw [this, hdiv8] at *
    have hquot : (n/8 : ℕ) ≤ n/4 := by omega
    have : -(((n/8:ℕ)):ℤ) ≤ r := by rw [← hdiv8]; exact hr
    have h1 : (((n/8:ℕ)):ℤ) ≤ (((n/4:ℕ)):ℤ) := by exact_mod_cast hquot
    linarith
  refine ⟨h0le, ?_, ?_, ?_, ?_⟩
  · -- lo = (n/4)+r
    unfold lo
    exact Int.toNat_of_nonneg h0le
  · -- lo + n/2 ≤ n+1, i.e. (n/4)+r+n/2 ≤ n+1
    have hloeq : (lo n r : ℤ) = (n/4 : ℤ) + r := by unfold lo; exact Int.toNat_of_nonneg h0le
    have hn4 : (n:ℤ)/4 = ((n/4 : ℕ) : ℤ) := by exact_mod_cast (Int.natCast_ediv n 4).symm
    have hn2 : (n:ℤ)/2 = ((n/2 : ℕ) : ℤ) := by exact_mod_cast (Int.natCast_ediv n 2).symm
    have : (lo n r : ℤ) + ((n/2:ℕ):ℤ) ≤ (n:ℤ) + 1 := by
      rw [hloeq, ← hn2]
      rw [hn4, hdiv8] at *
      -- (n/4)+r+(n/2) ≤ n+1 with r ≤ n/8
      have hr2 : r ≤ (((n/8:ℕ)):ℤ) := by rw [← hdiv8]; exact hr'
      have : (((n/4:ℕ)):ℤ) + (((n/8:ℕ)):ℤ) + (((n/2:ℕ)):ℤ) ≤ (n:ℤ) + 1 := by
        have h := Nat.div_add_mod n 4
        have h2 := Nat.div_add_mod n 2
        have h8 := Nat.div_add_mod n 8
        push_cast
        omega
      rw [hn4] at this
      linarith
    have hcast : (lo n r : ℤ) + ((n/2:ℕ):ℤ) = ((lo n r + n/2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at this
    have : (lo n r + n/2 : ℕ) ≤ n + 1 := by exact_mod_cast this
    exact this
  · -- lo ≤ 3n/8 + 1
    have hloeq : (lo n r : ℤ) = (n/4 : ℤ) + r := by unfold lo; exact Int.toNat_of_nonneg h0le
    have hn4 : (n:ℤ)/4 = ((n/4 : ℕ) : ℤ) := by exact_mod_cast (Int.natCast_ediv n 4).symm
    have hr2 : r ≤ (((n/8:ℕ)):ℤ) := by rw [← hdiv8]; exact hr'
    have hb : (lo n r : ℤ) ≤ (((3*n/8 : ℕ)):ℤ) + 1 := by
      rw [hloeq, hn4]
      have h4 := Nat.div_add_mod n 4
      have h8 := Nat.div_add_mod n 8
      have h38 := Nat.div_add_mod (3*n) 8
      push_cast at hr2 ⊢
      omega
    have : lo n r ≤ 3*n/8 + 1 := by exact_mod_cast hb
    exact this
  · -- n+1 ≤ lo + n/2 + (3n/8+1)
    have hloeq : (lo n r : ℤ) = (n/4 : ℤ) + r := by unfold lo; exact Int.toNat_of_nonneg h0le
    have hn4 : (n:ℤ)/4 = ((n/4 : ℕ) : ℤ) := by exact_mod_cast (Int.natCast_ediv n 4).symm
    have hn2 : (n:ℤ)/2 = ((n/2 : ℕ) : ℤ) := by exact_mod_cast (Int.natCast_ediv n 2).symm
    have hr1 : -(((n/8:ℕ)):ℤ) ≤ r := by rw [← hdiv8]; exact hr
    have h3n8 : (3*(n:ℤ))/8 = ((3*n/8 : ℕ):ℤ) := by
      have : ((3*n : ℕ):ℤ)/8 = ((3*n/8 : ℕ):ℤ) := by exact_mod_cast (Int.natCast_ediv (3*n) 8).symm
      rw [← this]; push_cast; ring_nf
    have hm : (n:ℤ) % 8 = 1 := by exact_mod_cast hmod
    have hb : (n:ℤ) ≤ (lo n r : ℤ) + (((n/2:ℕ)):ℤ) + ((((3*n/8 : ℕ)):ℤ) + 1) := by
      rw [hloeq, ← hn2, ← h3n8]
      push_cast at hr1 ⊢
      omega
    have hcast : (lo n r : ℤ) + (((n/2:ℕ)):ℤ) + ((((3*n/8 : ℕ)):ℤ) + 1)
        = ((lo n r + n/2 + (3*n/8+1) : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at hb
    have : n ≤ lo n r + n/2 + (3*n/8+1) := by exact_mod_cast hb
    exact this

/-! ## Per-element index/parity translation -/

/-- For `j : Fin (n/2)` under `0 ≤ (n/4)+r`, the global index toNat is `lo + j`. -/
lemma g_toNat (n : ℕ) (r : ℤ) (h0 : 0 ≤ (n/4 : ℤ) + r) (j : ℕ) :
    ((n / 4 : ℤ) + r + (j : ℕ)).toNat = lo n r + j := by
  unfold lo
  omega

/-- Parity of the global index as a ℤ statement matches parity of `lo + j` as ℕ. -/
lemma g_parity (n : ℕ) (r : ℤ) (h0 : 0 ≤ (n/4 : ℤ) + r) (j : ℕ) (b : ℕ) :
    (((n / 4 : ℤ) + r + (j : ℕ)) % 2 = (b : ℤ)) ↔ ((lo n r + j) % 2 = b) := by
  have hlo : (lo n r : ℤ) = (n/4 : ℤ) + r := by unfold lo; exact Int.toNat_of_nonneg h0
  have key : ((n / 4 : ℤ) + r + (j : ℕ)) = ((lo n r + j : ℕ) : ℤ) := by
    rw [Nat.cast_add, hlo]
  rw [key]
  have : ((lo n r + j : ℕ) : ℤ) % 2 = (((lo n r + j) % 2 : ℕ) : ℤ) := by
    rw [Int.natCast_emod]; norm_num
  rw [this]
  exact_mod_cast Iff.rfl

/-! ## Reindexing the window product onto global indices -/

/-- The set of global indices in the window `[lo, lo+n/2)` of parity `b`. -/
noncomputable def windowSet (n : ℕ) (r : ℤ) (b : ℕ) : Finset ℕ :=
  (Finset.Ico (lo n r) (lo n r + n/2)).filter (fun idx => idx % 2 = b)

/-- The windowed `b`-parity product equals the product of `F` over the `b`-parity
global window set. -/
lemma windowQ_eq_prod (n : ℕ) (α : ℝ) (r : ℤ) (h0 : 0 ≤ (n/4 : ℤ) + r) (b : ℕ) :
    (∏ j ∈ (Finset.univ.filter (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = (b:ℤ))),
        (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)))
      = ∏ idx ∈ windowSet n r b, F n α idx := by
  classical
  unfold windowSet F
  refine Finset.prod_bij (fun (j : Fin (n/2)) _ => lo n r + (j : ℕ)) ?_ ?_ ?_ ?_
  · -- maps into windowSet
    intro j hj
    simp only [Finset.mem_filter] at hj
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨Nat.le_add_right _ _, by have := j.isLt; omega⟩, ?_⟩
    exact (g_parity n r h0 (j:ℕ) b).mp hj.2
  · -- injective
    intro j1 hj1 j2 hj2 heq
    simp only at heq
    have : (j1 : ℕ) = (j2 : ℕ) := by omega
    exact Fin.ext this
  · -- surjective
    intro idx hidx
    rw [Finset.mem_filter, Finset.mem_Ico] at hidx
    obtain ⟨⟨hlo, hhi⟩, hpar⟩ := hidx
    refine ⟨⟨idx - lo n r, by omega⟩, ?_, by simp; omega⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [g_parity n r h0 _ b]
    have : lo n r + (idx - lo n r) = idx := by omega
    rw [this]; exact hpar
  · -- factor equality
    intro j hj
    rw [g_toNat n r h0 (j:ℕ)]

/-- The full `b`-parity index set `{0,…,n}`. -/
noncomputable def fullSet (n : ℕ) (b : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter (fun idx => idx % 2 = b)

/-- The full `b`-parity residual product as a product of `F`. -/
noncomputable def fullQ (n : ℕ) (α : ℝ) (b : ℕ) : ℝ := ∏ idx ∈ fullSet n b, F n α idx

/-- `windowSet ⊆ fullSet` (window inside `[0,n]`). -/
lemma windowSet_subset (n : ℕ) (hn : (10^12:ℕ) ≤ n) (hmod : n % 8 = 1) (r : ℤ)
    (hr : -((n:ℤ)/8) ≤ r) (hr' : r ≤ (n:ℤ)/8) (b : ℕ) :
    windowSet n r b ⊆ fullSet n b := by
  obtain ⟨_, _, hwin, _, _⟩ := window_facts n hn hmod r hr hr'
  intro idx hidx
  simp only [windowSet, fullSet, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hidx ⊢
  refine ⟨by omega, hidx.2⟩

/-- `fullQeven` rewrites to `fullQ … 0`. -/
lemma fullQeven_eq (n : ℕ) (α : ℝ) :
    Workspace.ProofLemmas.Path4FullQ.fullQeven n α = fullQ n α 0 := by
  unfold Workspace.ProofLemmas.Path4FullQ.fullQeven fullQ fullSet F
  apply Finset.prod_congr rfl
  intro j hj
  exact Workspace.ProofLemmas.Path4FullQ.factor_eq_on_range n α j (Finset.mem_of_mem_filter j hj)

/-- `fullQodd` rewrites to `fullQ … 1`. -/
lemma fullQodd_eq (n : ℕ) (α : ℝ) :
    Workspace.ProofLemmas.Path4FullQ.fullQodd n α = fullQ n α 1 := by
  unfold Workspace.ProofLemmas.Path4FullQ.fullQodd fullQ fullSet F
  apply Finset.prod_congr rfl
  intro j hj
  exact Workspace.ProofLemmas.Path4FullQ.factor_eq_on_range n α j (Finset.mem_of_mem_filter j hj)

/-- `windowQe` rewrites to the product of `F` over the even window set. -/
lemma windowQe_eq (n : ℕ) (α : ℝ) (r : ℤ) (h0 : 0 ≤ (n/4 : ℤ) + r) :
    windowQe n α r = ∏ idx ∈ windowSet n r 0, F n α idx := by
  unfold windowQe
  have := windowQ_eq_prod n α r h0 0
  simpa using this

/-- `windowQo` rewrites to the product of `F` over the odd window set. -/
lemma windowQo_eq (n : ℕ) (α : ℝ) (r : ℤ) (h0 : 0 ≤ (n/4 : ℤ) + r) :
    windowQo n α r = ∏ idx ∈ windowSet n r 1, F n α idx := by
  unfold windowQo
  have := windowQ_eq_prod n α r h0 1
  simpa using this

/-! ## Wide left-CDF: up to `3n/8 + 1` (one index past `central_binomial_left_cdf_le`).

The right window tail, reflected by `idx ↦ n - idx`, lands in `[0, 3n/8+1]` (one
index wider than the left tail, due to the oddness of `n`).  We re-run the exact
Chernoff reduction of `Path4CentralCDF.central_binomial_left_cdf_le`, this time
extending `range (3n/8+2)` (which for `n%8=1` is `range (3*(n/8)+2) ⊆ range (3q+3)`)
to `range (3q+3)`, so the SAME numeric bound applies. -/
lemma central_binomial_left_cdf_wide (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1) :
    ∑ k ∈ Finset.range (3 * n / 8 + 2),
        Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k
      ≤ Real.exp (-((n : ℝ) / 128)) := by
  have hn_pos : 0 < n := by
    have h0 : (0 : ℕ) < 10 ^ 12 := by norm_num
    omega
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set q : ℕ := n / 8 with hq_def
  have h8q_le : 8 * q ≤ n := by rw [hq_def]; exact Nat.mul_div_le n 8
  have hq_real_ge : (n : ℝ)/8 - 1 ≤ (q : ℝ) := by
    have h : 8 * (n / 8) + 8 > n := by
      have := Nat.div_add_mod n 8
      have hmod' : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
      omega
    have h_real : 8 * ((n / 8 : ℕ) : ℝ) + 8 > (n : ℝ) := by exact_mod_cast h
    rw [hq_def]; linarith
  -- Step 0: 3*n/8 + 2 ≤ 3*q + 3 (uses n % 8 = 1).
  have h_range_le : 3 * n / 8 + 2 ≤ 3 * q + 3 := by
    rw [hq_def]
    have := Nat.div_add_mod n 8
    have h38 := Nat.div_add_mod (3*n) 8
    omega
  -- Step 1: extend the sum to range (3q+3).
  have h_step_bound :
      (∑ k ∈ Finset.range (3 * n / 8 + 2),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
        ≤ (∑ k ∈ Finset.range (3 * q + 3),
            Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_range] at *
      exact lt_of_lt_of_le hx h_range_le
    · intros k _ _
      exact CentralBinomialLowerTailWideProof.binPMF_nonneg n k (1/2) (by norm_num) (by norm_num)
  -- Step 2: Chernoff.
  have h_chernoff : (∑ k ∈ Finset.range (3 * q + 3),
                      Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
                    ≤ (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n :=
    CentralBinomialLowerTailWideProof.chernoff_optimal_bound n (3 * q + 3)
  -- Step 3a: (9/7)^{3q+3} · (8/9)^n ≤ (9/7)^3 · ((9/7)^3 · (8/9)^8)^q.
  have h_step3a : (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n
                ≤ (9/7:ℝ)^3 * ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q := by
    have hk_split : (9/7:ℝ)^(3*q+3) = (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) := by
      rw [← pow_add]; congr 1; ring
    rw [hk_split]
    have h_n_split : (8/9:ℝ)^n = (8/9:ℝ)^(8*q) * (8/9:ℝ)^(n - 8*q) := by
      rw [← pow_add]; congr 1; omega
    rw [h_n_split]
    have h_89_le1 : (8/9:ℝ)^(n - 8*q) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have h_97q_nn : (0:ℝ) ≤ (9/7:ℝ)^(3*q) := pow_nonneg (by norm_num) _
    have h_89_8q_nn : (0:ℝ) ≤ (8/9:ℝ)^(8*q) := pow_nonneg (by norm_num) _
    have h_97_three_nn : (0:ℝ) ≤ (9/7:ℝ)^3 := pow_nonneg (by norm_num) _
    have hrhs_eq : ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q = (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) := by
      rw [mul_pow]
      have e1 : ((9/7:ℝ)^3)^q = (9/7:ℝ)^(3*q) := by rw [← pow_mul]
      have e2 : ((8/9:ℝ)^8)^q = (8/9:ℝ)^(8*q) := by rw [← pow_mul]
      rw [e1, e2]
    rw [hrhs_eq]
    have hbase : (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * ((8/9:ℝ)^(8*q) * (8/9:ℝ)^(n - 8*q))
              = (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) * (8/9:ℝ)^(n - 8*q) := by ring
    rw [hbase]
    have hbase2 : (9/7:ℝ)^3 * ((9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q))
                = (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) := by ring
    rw [hbase2]
    have hcoef_nn : (0:ℝ) ≤ (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) := by
      apply mul_nonneg
      apply mul_nonneg h_97_three_nn h_97q_nn
      exact h_89_8q_nn
    have := mul_le_mul_of_nonneg_left h_89_le1 hcoef_nn
    linarith
  -- Step 3b: ((9/7)^3 · (8/9)^8)^q ≤ exp(-q/8).
  have h_step3b : ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q ≤ Real.exp (-((q:ℝ) / 8)) := by
    have h_base_nn : (0:ℝ) ≤ (9/7:ℝ)^3 * (8/9:ℝ)^8 := by positivity
    have h_pow := pow_le_pow_left₀ h_base_nn
      Workspace.ProofLemmas.Path4CentralCDF.base_le_exp_neg_eighth q
    rw [← Real.exp_nat_mul] at h_pow
    rw [show ((q:ℝ) * -(1/8)) = -((q:ℝ) / 8) from by ring] at h_pow
    exact h_pow
  have h_97_three_le_6 : (9/7:ℝ)^3 ≤ 6 := by norm_num
  have h_combined : (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n
                ≤ 6 * Real.exp (-((q:ℝ) / 8)) := by
    calc (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n
        ≤ (9/7:ℝ)^3 * ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q := h_step3a
      _ ≤ 6 * ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q := by
          apply mul_le_mul_of_nonneg_right h_97_three_le_6
          exact pow_nonneg (by positivity) _
      _ ≤ 6 * Real.exp (-((q:ℝ) / 8)) := by
          apply mul_le_mul_of_nonneg_left h_step3b (by norm_num : (0:ℝ) ≤ 6)
  have h_log6_le : Real.log 6 ≤ 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)
    linarith
  have h_6_le_exp : (6 : ℝ) ≤ Real.exp 5 := by
    have h := Real.exp_le_exp.mpr h_log6_le
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 6)] at h
  have h_step4 : 6 * Real.exp (-((q:ℝ) / 8)) ≤ Real.exp (-((n:ℝ)/128)) := by
    have h_exp_combined : Real.exp 5 * Real.exp (-((q:ℝ) / 8))
                        = Real.exp (5 - (q:ℝ) / 8) := by
      rw [← Real.exp_add]; ring_nf
    have h_lhs_le : 6 * Real.exp (-((q:ℝ) / 8))
                  ≤ Real.exp 5 * Real.exp (-((q:ℝ) / 8)) := by
      apply mul_le_mul_of_nonneg_right h_6_le_exp
      exact (Real.exp_pos _).le
    rw [h_exp_combined] at h_lhs_le
    refine le_trans h_lhs_le ?_
    apply Real.exp_le_exp.mpr
    have h_n_large : (n : ℝ) ≥ 10^12 := hn_real_ge
    nlinarith [hq_real_ge, h_n_large]
  calc (∑ k ∈ Finset.range (3 * n / 8 + 2),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
      ≤ (∑ k ∈ Finset.range (3 * q + 3),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := h_step_bound
    _ ≤ (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n := h_chernoff
    _ ≤ 6 * Real.exp (-((q:ℝ) / 8)) := h_combined
    _ ≤ Real.exp (-((n:ℝ)/128)) := h_step4

/-- The binomial mass over the indices OUTSIDE the window (within `[0,n]`, parity `b`)
is at most `2·exp(-n/128)`: the left tail `< lo ≤ 3n/8` and the right tail
`≥ lo+n/2 ≥ 5n/8` (reflected onto `[0,3n/8+1]`). -/
lemma outside_binPMF_sum_le (n : ℕ) (hn : (10^12:ℕ) ≤ n) (hmod : n % 8 = 1) (r : ℤ)
    (hr : -((n:ℤ)/8) ≤ r) (hr' : r ≤ (n:ℤ)/8) (b : ℕ) :
    ∑ idx ∈ (fullSet n b \ windowSet n r b),
        Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx
      ≤ 2 * Real.exp (-((n:ℝ)/128)) := by
  classical
  obtain ⟨h0, hloeq, hwin, hloub, hrefl⟩ := window_facts n hn hmod r hr hr'
  -- split the outside set into left (idx < lo) and right (idx ≥ lo + n/2)
  set D := fullSet n b \ windowSet n r b with hD
  have hbin_nn : ∀ k, 0 ≤ Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k :=
    fun k => CentralBinomialLowerTailWideProof.binPMF_nonneg n k (1/2) (by norm_num) (by norm_num)
  -- L: idx < lo;   R: idx ≥ lo + n/2
  set L := D.filter (fun idx => idx < lo n r) with hL
  set R := D.filter (fun idx => ¬ idx < lo n r) with hR
  have hsplit : ∑ idx ∈ D, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx
      = (∑ idx ∈ L, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx)
        + ∑ idx ∈ R, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx := by
    rw [hL, hR, Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  -- left tail bound
  have hLbound : ∑ idx ∈ L, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx
      ≤ Real.exp (-((n:ℝ)/128)) := by
    refine le_trans ?_ (Workspace.ProofLemmas.Path4CentralCDF.central_binomial_left_cdf_le n hn)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro idx hidx
      simp only [hL, hD, Finset.mem_filter, Finset.mem_sdiff, fullSet, Finset.mem_range,
        windowSet] at hidx
      rw [Finset.mem_range]
      obtain ⟨⟨_, hlt⟩, _⟩ := hidx
      omega
    · intro idx _ _; exact hbin_nn idx
  -- right tail bound, via reflection idx ↦ n - idx
  have hRbound : ∑ idx ∈ R, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx
      ≤ Real.exp (-((n:ℝ)/128)) := by
    have hRsub : R ⊆ Finset.Icc (lo n r + n/2) n := by
      intro idx hidx
      simp only [hR, hD, Finset.mem_filter, Finset.mem_sdiff, fullSet, Finset.mem_range,
        windowSet, Finset.mem_Ico, Finset.mem_Icc] at hidx ⊢
      obtain ⟨⟨⟨hle, _⟩, hnotwin⟩, hnotlt⟩ := hidx
      refine ⟨by omega, by omega⟩
    -- reflect Icc(lo+n/2, n) into Icc(0, n - lo - n/2) ⊆ range(3n/8+2)
    refine le_trans ?_
      (Workspace.ProofLemmas.Path4WindowQ.central_binomial_left_cdf_wide n hn hmod)
    -- ∑_{R} bin = ∑_{R} bin(n - idx)  ≤ ∑_{range(3n/8+2)} bin
    calc ∑ idx ∈ R, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx
        ≤ ∑ idx ∈ Finset.Icc (lo n r + n/2) n,
            Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hRsub
          intro idx _ _; exact hbin_nn idx
      _ = ∑ m ∈ Finset.Icc 0 (n - (lo n r + n/2)),
            Workspace.Types.AlternatingSumExpression.binPMF n (1/2) m := by
          apply Finset.sum_nbij' (fun idx => n - idx) (fun m => n - m)
          · intro idx hidx
            rw [Finset.mem_Icc] at hidx ⊢; omega
          · intro m hm
            rw [Finset.mem_Icc] at hm ⊢; omega
          · intro idx hidx
            rw [Finset.mem_Icc] at hidx; omega
          · intro m hm
            rw [Finset.mem_Icc] at hm; omega
          · intro idx hidx
            rw [Finset.mem_Icc] at hidx
            -- f idx = bin idx,  g (i idx) = bin (n - idx);  binomial symmetry
            exact Workspace.ProofLemmas.Path4FullQ.binPMF_half_symm n idx hidx.2
      _ ≤ ∑ idx ∈ Finset.range (3*n/8+2),
            Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            rw [Finset.mem_Icc] at hm
            rw [Finset.mem_range]
            omega
          · intro idx _ _; exact hbin_nn idx
  linarith


/-! ## `2α ≤ √n` arithmetic -/

lemma two_alpha_le_sqrt (n : ℕ) (hn1 : 1 ≤ n) :
    2 * ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) ≤ Real.sqrt n := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt2pi : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt; nlinarith [Real.pi_gt_d2]
  have hexp : (1 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have hsqrtn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hden : (1 : ℝ) ≤ 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
    nlinarith [hexp, hsqrt2pi, Real.exp_pos 2]
  -- 2·(1/(4e²√(2π)))·√n = √n / (2e²√(2π)) ≤ √n since denom ≥ 1
  have hdpos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
    have : (0:ℝ) < Real.sqrt (2*Real.pi) := by linarith
    positivity
  rw [show 2 * ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
      = (2 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n from by ring]
  have hfrac : (2 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) ≤ 1 := by
    rw [div_le_one hdpos]; nlinarith [hexp, hsqrt2pi, Real.exp_pos 2]
  nlinarith [hfrac, hsqrtn]

/-! ## Core windowed-vs-full bound for a single parity -/

/-- The factor `F` rewrites to `1 - α·binPMF` for indices `≤ n`. -/
lemma F_eq_one_sub (n : ℕ) (α : ℝ) (idx : ℕ) (hidx : idx ≤ n) :
    F n α idx = 1 - α * Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx := by
  unfold F
  rw [Workspace.ProofLemmas.Path4FullQ.binPMF_half_eq_choose n idx hidx]

/-- **Core bound.**  For parity `b`, `|∏_window F - ∏_full F| ≤ √n · exp(-n/128)`. -/
lemma windowQ_sub_fullQ_le_core (n : ℕ) (hn : (10^12:ℕ) ≤ n) (hmod : n % 8 = 1) (r : ℤ)
    (hr : -((n:ℤ)/8) ≤ r) (hr' : r ≤ (n:ℤ)/8) (b : ℕ)
    (α : ℝ) (hα : α = (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n) :
    |(∏ idx ∈ windowSet n r b, F n α idx) - (∏ idx ∈ fullSet n b, F n α idx)|
      ≤ Real.sqrt n * Real.exp (-(n:ℝ)/128) := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h0, _, hwin, _, _⟩ := window_facts n hn hmod r hr hr'
  have hsub : windowSet n r b ⊆ fullSet n b := windowSet_subset n hn hmod r hr hr' b
  set W := windowSet n r b with hW
  set E := fullSet n b with hE
  set D := E \ W with hDdef
  -- each F idx ∈ [0,1]
  have hFmem : ∀ idx, 0 ≤ F n α idx ∧ F n α idx ≤ 1 := by
    intro idx
    unfold F
    exact Workspace.ProofLemmas.QFactorBounds.factor_mem hn1 α hα idx
  -- windowQ ∈ [0,1]
  have hWQ0 : 0 ≤ ∏ idx ∈ W, F n α idx := Finset.prod_nonneg (fun idx _ => (hFmem idx).1)
  have hWQ1 : ∏ idx ∈ W, F n α idx ≤ 1 :=
    Finset.prod_le_one (fun idx _ => (hFmem idx).1) (fun idx _ => (hFmem idx).2)
  -- out := ∏ D F ∈ [0,1]
  have hout0 : 0 ≤ ∏ idx ∈ D, F n α idx := Finset.prod_nonneg (fun idx _ => (hFmem idx).1)
  have hout1 : ∏ idx ∈ D, F n α idx ≤ 1 :=
    Finset.prod_le_one (fun idx _ => (hFmem idx).1) (fun idx _ => (hFmem idx).2)
  -- full = window · out
  have hfact : (∏ idx ∈ W, F n α idx) * (∏ idx ∈ D, F n α idx) = ∏ idx ∈ E, F n α idx := by
    rw [hDdef, mul_comm]
    exact Finset.prod_sdiff hsub
  -- 1 - out ≤ ∑_D α·binPMF
  have hbinmem : ∀ idx ∈ D, idx ≤ n := by
    intro idx hidx
    rw [hDdef, hE] at hidx
    simp only [fullSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hidx
    omega
  have hone_sub : 1 - (∏ idx ∈ D, F n α idx)
      ≤ ∑ idx ∈ D, α * Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx := by
    have hrw : (∏ idx ∈ D, F n α idx)
        = ∏ idx ∈ D, (1 - α * Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx) := by
      apply Finset.prod_congr rfl
      intro idx hidx
      exact F_eq_one_sub n α idx (hbinmem idx hidx)
    rw [hrw]
    apply one_sub_prod_one_sub_le_sum
    · intro idx hidx
      rw [hα]
      have := (hFmem idx).2  -- not directly; use positivity of α·binPMF
      have hbnn : 0 ≤ Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx :=
        CentralBinomialLowerTailWideProof.binPMF_nonneg n idx (1/2) (by norm_num) (by norm_num)
      have hαnn : 0 ≤ (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n := by positivity
      exact mul_nonneg hαnn hbnn
    · intro idx hidx
      -- α·binPMF idx ≤ 1 from F idx = 1 - α·binPMF ≥ 0
      have hF := (hFmem idx).1
      rw [F_eq_one_sub n α idx (hbinmem idx hidx)] at hF
      linarith
  -- ∑_D α·binPMF = α·∑_D binPMF ≤ α·(2·exp) ≤ √n·exp
  have hαnn : 0 ≤ α := by rw [hα]; positivity
  have hsumD : ∑ idx ∈ D, α * Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx
      = α * ∑ idx ∈ D, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx := by
    rw [Finset.mul_sum]
  have hDsum_le : ∑ idx ∈ D, Workspace.Types.AlternatingSumExpression.binPMF n (1/2) idx
      ≤ 2 * Real.exp (-((n:ℝ)/128)) := by
    rw [hDdef, hW, hE]; exact outside_binPMF_sum_le n hn hmod r hr hr' b
  have hone_sub' : 1 - (∏ idx ∈ D, F n α idx) ≤ α * (2 * Real.exp (-((n:ℝ)/128))) := by
    refine le_trans hone_sub ?_
    rw [hsumD]
    exact mul_le_mul_of_nonneg_left hDsum_le hαnn
  -- |window - full| = window·(1 - out) ≤ 1·(1-out) ≤ √n·exp
  have hdiff : (∏ idx ∈ W, F n α idx) - (∏ idx ∈ E, F n α idx)
      = (∏ idx ∈ W, F n α idx) * (1 - (∏ idx ∈ D, F n α idx)) := by
    rw [← hfact]; ring
  have h1subout_nn : 0 ≤ 1 - (∏ idx ∈ D, F n α idx) := by linarith
  have h2αexp : α * (2 * Real.exp (-((n:ℝ)/128))) ≤ Real.sqrt n * Real.exp (-(n:ℝ)/128) := by
    have hexp_nn : 0 ≤ Real.exp (-((n:ℝ)/128)) := (Real.exp_pos _).le
    have h2α : 2 * α ≤ Real.sqrt n := by rw [hα]; exact two_alpha_le_sqrt n hn1
    have : α * (2 * Real.exp (-((n:ℝ)/128))) = (2*α) * Real.exp (-((n:ℝ)/128)) := by ring
    rw [this]
    have heq : Real.exp (-(n:ℝ)/128) = Real.exp (-((n:ℝ)/128)) := by congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right h2α hexp_nn
  rw [hdiff, abs_of_nonneg (by positivity)]
  calc (∏ idx ∈ W, F n α idx) * (1 - (∏ idx ∈ D, F n α idx))
      ≤ 1 * (1 - (∏ idx ∈ D, F n α idx)) :=
        mul_le_mul_of_nonneg_right hWQ1 h1subout_nn
    _ = 1 - (∏ idx ∈ D, F n α idx) := by ring
    _ ≤ α * (2 * Real.exp (-((n:ℝ)/128))) := hone_sub'
    _ ≤ Real.sqrt n * Real.exp (-(n:ℝ)/128) := h2αexp

/-! ## Public bounds -/

/-- **Windowed-vs-full even bound.** -/
theorem windowQe_sub_fullQeven_le (n : ℕ) (hn : (10^12:ℕ) ≤ n) (hmod : n % 8 = 1) (r : ℤ)
    (hr : -((n:ℤ)/8) ≤ r) (hr' : r ≤ (n:ℤ)/8) :
    let α := (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n
    |windowQe n α r - Workspace.ProofLemmas.Path4FullQ.fullQeven n α|
      ≤ Real.sqrt n * Real.exp (-(n:ℝ)/128) := by
  intro α
  obtain ⟨h0, _, _, _, _⟩ := window_facts n hn hmod r hr hr'
  rw [windowQe_eq n α r h0, fullQeven_eq n α]
  unfold fullQ
  exact windowQ_sub_fullQ_le_core n hn hmod r hr hr' 0 α rfl

/-- **Windowed-vs-full odd bound.** -/
theorem windowQo_sub_fullQodd_le (n : ℕ) (hn : (10^12:ℕ) ≤ n) (hmod : n % 8 = 1) (r : ℤ)
    (hr : -((n:ℤ)/8) ≤ r) (hr' : r ≤ (n:ℤ)/8) :
    let α := (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n
    |windowQo n α r - Workspace.ProofLemmas.Path4FullQ.fullQodd n α|
      ≤ Real.sqrt n * Real.exp (-(n:ℝ)/128) := by
  intro α
  obtain ⟨h0, _, _, _, _⟩ := window_facts n hn hmod r hr hr'
  rw [windowQo_eq n α r h0, fullQodd_eq n α]
  unfold fullQ
  exact windowQ_sub_fullQ_le_core n hn hmod r hr hr' 1 α rfl

end Workspace.ProofLemmas.Path4WindowQ
