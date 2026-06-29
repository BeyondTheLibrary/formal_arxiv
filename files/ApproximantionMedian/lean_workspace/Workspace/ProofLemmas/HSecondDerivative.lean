import Mathlib

namespace Workspace.ProofLemmas.HSecondDerivative

noncomputable def h_q (q lambda delta x : ℝ) : ℝ :=
  lambda * (delta * (1 - x) ^ ((1 : ℝ) / q) - x ^ ((1 : ℝ) / q))

end Workspace.ProofLemmas.HSecondDerivative

open Workspace.ProofLemmas.HSecondDerivative in
theorem HSecondDerivative
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam : 0 < lambda)
    (delta : ℝ) (hdelta : 1 ≤ delta) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv 2 (fun x => h_q q lambda delta x) x =
      (lambda * (q - 1) / q^2) *
        (x ^ ((1 - 2*q) / q) - delta * (1 - x) ^ ((1 - 2*q) / q)) := by
  -- q ≠ 0
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  -- First derivative formula at any point y with 0 < y < 1
  have firstDeriv : ∀ y, 0 < y → y < 1 →
      HasDerivAt (fun z => h_q q lambda delta z)
        (lambda * (-(delta * ((1/q) * (1 - y) ^ ((1:ℝ)/q - 1))) - (1/q) * y ^ ((1:ℝ)/q - 1))) y := by
    intro y hy0 hy1
    have hy_ne : y ≠ 0 := ne_of_gt hy0
    have h1my_ne : (1 - y) ≠ 0 := by linarith
    -- HasDerivAt for y ↦ y^(1/q)
    have h_y_pow : HasDerivAt (fun z : ℝ => z ^ ((1:ℝ)/q)) ((1/q) * y ^ ((1:ℝ)/q - 1)) y := by
      have h := (hasDerivAt_id y).rpow_const (p := (1:ℝ)/q) (Or.inl hy_ne)
      simpa using h
    -- HasDerivAt for y ↦ (1 - y)^(1/q)
    have h_oneminus_y : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have h_1my_pow : HasDerivAt (fun z : ℝ => (1 - z) ^ ((1:ℝ)/q))
        (-1 * (1/q) * (1 - y) ^ ((1:ℝ)/q - 1)) y := by
      have h := h_oneminus_y.rpow_const (p := (1:ℝ)/q) (Or.inl h1my_ne)
      convert h using 1
    -- HasDerivAt for delta * (1 - y)^(1/q)
    have h_d_1my_pow : HasDerivAt (fun z : ℝ => delta * (1 - z) ^ ((1:ℝ)/q))
        (delta * (-1 * (1/q) * (1 - y) ^ ((1:ℝ)/q - 1))) y :=
      h_1my_pow.const_mul delta
    -- HasDerivAt for (delta * (1 - y)^(1/q) - y^(1/q))
    have h_diff : HasDerivAt (fun z : ℝ => delta * (1 - z) ^ ((1:ℝ)/q) - z ^ ((1:ℝ)/q))
        (delta * (-1 * (1/q) * (1 - y) ^ ((1:ℝ)/q - 1)) - (1/q) * y ^ ((1:ℝ)/q - 1)) y :=
      h_d_1my_pow.sub h_y_pow
    -- Multiply by lambda
    have h_full : HasDerivAt (fun z : ℝ => lambda * (delta * (1 - z) ^ ((1:ℝ)/q) - z ^ ((1:ℝ)/q)))
        (lambda * (delta * (-1 * (1/q) * (1 - y) ^ ((1:ℝ)/q - 1)) - (1/q) * y ^ ((1:ℝ)/q - 1))) y :=
      h_diff.const_mul lambda
    have h_eq : (fun z => h_q q lambda delta z) =
        (fun z : ℝ => lambda * (delta * (1 - z) ^ ((1:ℝ)/q) - z ^ ((1:ℝ)/q))) := by
      funext z; rfl
    rw [h_eq]
    convert h_full using 1
    ring
  -- The first derivative function (in a neighborhood of x):
  let f' : ℝ → ℝ := fun y =>
    lambda * (-(delta * ((1/q) * (1 - y) ^ ((1:ℝ)/q - 1))) - (1/q) * y ^ ((1:ℝ)/q - 1))
  -- Equivalent simpler form for differentiation
  let g' : ℝ → ℝ := fun y =>
    -(lambda * (1/q)) * (delta * (1 - y) ^ ((1:ℝ)/q - 1) + y ^ ((1:ℝ)/q - 1))
  have hf'_eq_g' : f' = g' := by
    funext y; simp only [f', g']; ring
  -- deriv equals f' on a neighborhood of x (in fact, on (0,1))
  have hderiv_on_nbhd : ∀ᶠ y in nhds x, deriv (fun z => h_q q lambda delta z) y = f' y := by
    have h_open : IsOpen (Set.Ioo (0:ℝ) 1) := isOpen_Ioo
    have hx_mem : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx0, hx1⟩
    filter_upwards [h_open.mem_nhds hx_mem] with y hy
    exact (firstDeriv y hy.1 hy.2).deriv
  -- Now compute the derivative of f' at x using HasDerivAt
  -- Use the fact that f' = g' to do differentiation on g'
  have hx_ne : x ≠ 0 := ne_of_gt hx0
  have h1mx_ne : (1 - x) ≠ 0 := by linarith
  -- HasDerivAt for y ↦ y^((1/q) - 1)
  have h_y_pow' : HasDerivAt (fun z : ℝ => z ^ ((1:ℝ)/q - 1))
      (((1:ℝ)/q - 1) * x ^ ((1:ℝ)/q - 1 - 1)) x := by
    have h := (hasDerivAt_id x).rpow_const (p := (1:ℝ)/q - 1) (Or.inl hx_ne)
    simpa using h
  -- HasDerivAt for y ↦ (1 - y)^((1/q) - 1)
  have h_oneminus_x : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have h_1mx_pow' : HasDerivAt (fun z : ℝ => (1 - z) ^ ((1:ℝ)/q - 1))
      (-1 * ((1:ℝ)/q - 1) * (1 - x) ^ ((1:ℝ)/q - 1 - 1)) x := by
    have h := h_oneminus_x.rpow_const (p := (1:ℝ)/q - 1) (Or.inl h1mx_ne)
    convert h using 1
  -- delta * (1 - y) ^ ((1/q) - 1)
  have h_d_1mx_pow' : HasDerivAt (fun z : ℝ => delta * (1 - z) ^ ((1:ℝ)/q - 1))
      (delta * (-1 * ((1:ℝ)/q - 1) * (1 - x) ^ ((1:ℝ)/q - 1 - 1))) x :=
    h_1mx_pow'.const_mul delta
  -- Sum: delta * (1 - y) ^ ((1/q) - 1) + y ^ ((1/q) - 1)
  have h_sum : HasDerivAt
      (fun z : ℝ => delta * (1 - z) ^ ((1:ℝ)/q - 1) + z ^ ((1:ℝ)/q - 1))
      (delta * (-1 * ((1:ℝ)/q - 1) * (1 - x) ^ ((1:ℝ)/q - 1 - 1))
        + ((1:ℝ)/q - 1) * x ^ ((1:ℝ)/q - 1 - 1)) x :=
    h_d_1mx_pow'.add h_y_pow'
  -- Multiply by -(lambda/q)
  have h_g' : HasDerivAt g'
      (-(lambda * (1/q)) *
        (delta * (-1 * ((1:ℝ)/q - 1) * (1 - x) ^ ((1:ℝ)/q - 1 - 1))
          + ((1:ℝ)/q - 1) * x ^ ((1:ℝ)/q - 1 - 1))) x :=
    h_sum.const_mul _
  -- Iterated deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- Goal: deriv (deriv (fun x => h_q q lambda delta x)) x = ...
  -- Replace deriv of inner function via EventuallyEq
  rw [Filter.EventuallyEq.deriv_eq hderiv_on_nbhd]
  rw [hf'_eq_g']
  rw [h_g'.deriv]
  -- Now we need to show the algebraic identity
  -- Simplify the exponents: (1/q) - 1 = (1 - q)/q  and  (1/q) - 1 - 1 = (1 - 2q)/q
  have hexp1 : (1:ℝ)/q - 1 - 1 = (1 - 2*q) / q := by
    field_simp
    ring
  have hexp2 : (1:ℝ)/q - 1 = (1 - q) / q := by
    field_simp
  -- Substitute exponents
  rw [hexp1]
  -- coefficient simplification
  -- LHS = -(lambda * (1/q)) * (delta * (-1 * ((1/q) - 1) * (1-x)^((1-2q)/q)) + ((1/q) - 1) * x^((1-2q)/q))
  -- We want: (lambda * (q - 1) / q^2) * (x^((1-2q)/q) - delta * (1-x)^((1-2q)/q))
  have hcoef : -(lambda * (1/q)) * ((1:ℝ)/q - 1) = lambda * (q - 1) / q^2 := by
    field_simp
    ring
  -- Rewrite goal
  have lhs_simp :
      -(lambda * (1/q)) *
        (delta * (-1 * ((1:ℝ)/q - 1) * (1 - x) ^ ((1 - 2*q)/q))
          + ((1:ℝ)/q - 1) * x ^ ((1 - 2*q)/q))
      = (-(lambda * (1/q)) * ((1:ℝ)/q - 1)) *
        (x ^ ((1 - 2*q)/q) - delta * (1 - x) ^ ((1 - 2*q)/q)) := by
    ring
  rw [lhs_simp, hcoef]

