import Mathlib

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas

open Polynomial

/-- If `f` is continuous and never vanishes on `[a, b]`, then `f` is everywhere
positive or everywhere negative there. -/
private lemma psw_const_sign_of_no_zero
    (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ)
    (h_no_zero : ∀ x : ℝ, a ≤ x → x ≤ b → f x ≠ 0) :
    (∀ x : ℝ, a ≤ x → x ≤ b → 0 < f x) ∨
      (∀ x : ℝ, a ≤ x → x ≤ b → f x < 0) := by
  by_cases hab : a ≤ b
  · have hfa : f a ≠ 0 := h_no_zero a le_rfl hab
    rcases lt_or_gt_of_ne hfa with hneg | hpos
    · right
      intro x hx1 hx2
      by_contra hxpos
      push_neg at hxpos
      have hcont : ContinuousOn f (Set.Icc a x) := hf.continuousOn
      have h_in : (0 : ℝ) ∈ Set.Icc (f a) (f x) := ⟨le_of_lt hneg, hxpos⟩
      obtain ⟨z, hz_mem, hz_eq⟩ := intermediate_value_Icc hx1 hcont h_in
      exact h_no_zero z hz_mem.1 (le_trans hz_mem.2 hx2) hz_eq
    · left
      intro x hx1 hx2
      by_contra hxneg
      push_neg at hxneg
      have hcont : ContinuousOn f (Set.Icc a x) := hf.continuousOn
      have h_in : (0 : ℝ) ∈ Set.Icc (f x) (f a) := ⟨hxneg, le_of_lt hpos⟩
      obtain ⟨z, hz_mem, hz_eq⟩ := intermediate_value_Icc' hx1 hcont h_in
      exact h_no_zero z hz_mem.1 (le_trans hz_mem.2 hx2) hz_eq
  · left
    intro x hx1 hx2
    push_neg at hab
    exact absurd (le_trans hx1 hx2) (not_le.mpr hab)

/-- `h` is sign-constant on an open gap with no zeros: if `m, x ∈ (lo, hi]`,
both are zero-free (no zeros strictly between `lo` and `hi`), then `h m` and `h x`
have the same sign, i.e. `0 ≤ h m * h x` is too weak; we phrase it as: `h x` has
the same sign as `h m` (their product is positive). -/
private lemma psw_same_sign_on_gap
    (h : ℝ → ℝ) (hcont : Continuous h) {m x : ℝ}
    (h_no_zero_between : ∀ y : ℝ, h y = 0 → y ∉ Set.Ioo (min m x) (max m x))
    (hmne : h m ≠ 0) (hxne : h x ≠ 0) :
    0 < h m * h x := by
  -- consider the closed interval between m and x
  rcases le_total m x with hmx | hxm
  · -- m ≤ x; interval [m, x]
    have hsub : ∀ y : ℝ, m ≤ y → y ≤ x → h y ≠ 0 := by
      intro y hy1 hy2 hyz
      rcases eq_or_lt_of_le hy1 with h1 | h1
      · rw [← h1] at hyz; exact hmne hyz
      rcases eq_or_lt_of_le hy2 with h2 | h2
      · rw [h2] at hyz; exact hxne hyz
      · exact h_no_zero_between y hyz (by rw [min_eq_left hmx, max_eq_right hmx]; exact ⟨h1, h2⟩)
    rcases psw_const_sign_of_no_zero h hcont m x hsub with hpos | hneg
    · have hm0 := hpos m le_rfl hmx; have hx0 := hpos x hmx le_rfl; exact mul_pos hm0 hx0
    · have h1 := hneg m le_rfl hmx; have h2 := hneg x hmx le_rfl; nlinarith [h1, h2]
  · -- x ≤ m; interval [x, m]
    have hsub : ∀ y : ℝ, x ≤ y → y ≤ m → h y ≠ 0 := by
      intro y hy1 hy2 hyz
      rcases eq_or_lt_of_le hy1 with h1 | h1
      · rw [← h1] at hyz; exact hxne hyz
      rcases eq_or_lt_of_le hy2 with h2 | h2
      · rw [h2] at hyz; exact hmne hyz
      · exact h_no_zero_between y hyz (by rw [min_eq_right hxm, max_eq_left hxm]; exact ⟨h1, h2⟩)
    rcases psw_const_sign_of_no_zero h hcont x m hsub with hpos | hneg
    · have hx0 := hpos x le_rfl hxm; have hm0 := hpos m hxm le_rfl; exact mul_pos hm0 hx0
    · have h1 := hneg x le_rfl hxm; have h2 := hneg m hxm le_rfl; nlinarith [h1, h2]

/-- The product `∏_{z ∈ xs}(x - z)` over `xs` whose every element is `> x`
equals `(-1)^|xs|` times a positive number. Concretely, when `x < z` for all
`z ∈ xs`, the product has sign `(-1)^xs.length`; we only need: for two points
`x₁, x₂` both strictly below all of `xs`, the products have the same sign. -/
private lemma psw_prod_pos_below
    (xs : List ℝ) {x₁ x₂ : ℝ}
    (h1 : ∀ z ∈ xs, x₁ < z) (h2 : ∀ z ∈ xs, x₂ < z) :
    0 < (xs.map (fun z => x₁ - z)).prod * (xs.map (fun z => x₂ - z)).prod := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have ha1 : x₁ < a := h1 a List.mem_cons_self
    have ha2 : x₂ < a := h2 a List.mem_cons_self
    have hr1 : ∀ z ∈ rest, x₁ < z := fun z hz => h1 z (List.mem_cons_of_mem _ hz)
    have hr2 : ∀ z ∈ rest, x₂ < z := fun z hz => h2 z (List.mem_cons_of_mem _ hz)
    have ihr := ih hr1 hr2
    simp only [List.map_cons, List.prod_cons]
    have hfac : 0 < (x₁ - a) * (x₂ - a) := by
      have : 0 < (a - x₁) * (a - x₂) := by
        apply mul_pos <;> linarith
      nlinarith [this]
    nlinarith [hfac, ihr]

/-- Core recursion for the piecewise sign witness.

We cover the region `[lo, R]`.  `lo` is a point with `h lo ≠ 0` (the right edge of
the last processed gap, or `-R` initially).  `zs` is the sorted complete list of
zeros of `h` strictly to the right of `lo` (in `(lo, R]`).  We build a sub-list
`xs ⊆` sign-change points and produce a global sign `σ ∈ {±1}` with
`0 ≤ σ · (∏_{xs}(· - z)) · h` on `[lo, R]`, where `σ` is pinned by the sign of `h`
on the leftmost gap (at `lo`).

The key local fact: on the gap from `lo` to the next zero (or `R`), `h` is
sign-constant (IVT), so its sign is the sign of `h lo`. -/
private lemma psw_core
    (h : ℝ → ℝ) (hcont : Continuous h) (R : ℝ) (hR : 0 < R) :
    ∀ (n : ℕ) (zs : List ℝ) (lo : ℝ),
      zs.length = n →
      -R ≤ lo → lo < R →
      zs.Pairwise (· < ·) →
      (∀ z ∈ zs, lo < z ∧ z ≤ R) →
      (∀ z ∈ zs, h z = 0) →
      (∀ y : ℝ, lo < y → y ≤ R → h y = 0 → y ∈ zs) →
      ∃ (xs : List ℝ) (σ : ℝ),
        xs.Pairwise (· < ·) ∧
        xs.length ≤ zs.length ∧
        (∀ z ∈ xs, lo < z ∧ z ≤ R) ∧
        (∀ z ∈ xs, h z = 0) ∧
        (σ = 1 ∨ σ = -1) ∧
        ∀ x : ℝ, lo < x → x ≤ R →
          0 ≤ σ * (xs.map (fun z => x - z)).prod * h x := by
  intro n
  induction n with
  | zero =>
    -- zs = []. h has no zeros in (lo, R]. xs = []. σ = sign of h on the gap.
    intro zs lo hlen hlo_ge hlo_lt _ _ _ hcomplete
    rw [List.length_eq_zero_iff] at hlen; subst hlen
    -- midpoint witness
    set m : ℝ := (lo + R) / 2 with hm_def
    have hm1 : lo < m := by rw [hm_def]; linarith
    have hm2 : m ≤ R := by rw [hm_def]; linarith
    have h_no_zero : ∀ y : ℝ, lo < y → y ≤ R → h y = 0 → False := by
      intro y hy1 hy2 hyz
      have := hcomplete y hy1 hy2 hyz; simp at this
    have hm_ne : h m ≠ 0 := fun hz => h_no_zero m hm1 hm2 hz
    have hsame : ∀ x : ℝ, lo < x → x ≤ R → 0 < h m * h x := by
      intro x hx1 hx2
      have hxne : h x ≠ 0 := fun hz => h_no_zero x hx1 hx2 hz
      apply psw_same_sign_on_gap h hcont _ hm_ne hxne
      intro y hyz hymem
      rw [Set.mem_Ioo] at hymem
      have hy1 : lo < y := lt_of_lt_of_le (lt_min hm1 hx1) (le_of_lt hymem.1)
      have hy2 : y ≤ R := le_of_lt (lt_of_lt_of_le hymem.2 (max_le hm2 hx2))
      exact h_no_zero y hy1 hy2 hyz
    rcases lt_or_gt_of_ne hm_ne with hmneg | hmpos
    · refine ⟨[], -1, List.Pairwise.nil, by simp, by simp, by simp, Or.inr rfl, ?_⟩
      intro x hx1 hx2
      simp only [List.map_nil, List.prod_nil, mul_one]
      have hss := hsame x hx1 hx2
      nlinarith [hss, hmneg]
    · refine ⟨[], 1, List.Pairwise.nil, by simp, by simp, by simp, Or.inl rfl, ?_⟩
      intro x hx1 hx2
      simp only [List.map_nil, List.prod_nil, mul_one]
      have hss := hsame x hx1 hx2
      nlinarith [hss, hmpos]
  | succ k ih =>
    intro zs lo hlen hlo_ge hlo_lt hsorted hzbd hzzero hcomplete
    match zs, hlen, hsorted, hzbd, hzzero, hcomplete with
    | [], hlen, _, _, _, _ => exfalso; simp at hlen
    | z₀ :: rest, hlen, hsorted, hzbd, hzzero, hcomplete =>
      have hrestlen : rest.length = k := by simpa using hlen
      have hz0_mem : z₀ ∈ z₀ :: rest := List.mem_cons_self
      have hz0_bd : lo < z₀ ∧ z₀ ≤ R := hzbd z₀ hz0_mem
      have hz0_zero : h z₀ = 0 := hzzero z₀ hz0_mem
      have hrest_lt : ∀ y ∈ rest, z₀ < y := fun y hy => (List.pairwise_cons.mp hsorted).1 y hy
      have hrest_sorted : rest.Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
      have hrest_bd : ∀ z ∈ rest, z₀ < z ∧ z ≤ R := by
        intro z hz; exact ⟨hrest_lt z hz, (hzbd z (List.mem_cons_of_mem _ hz)).2⟩
      have hrest_zero : ∀ z ∈ rest, h z = 0 := fun z hz => hzzero z (List.mem_cons_of_mem _ hz)
      have hrest_complete : ∀ y : ℝ, z₀ < y → y ≤ R → h y = 0 → y ∈ rest := by
        intro y hy1 hy2 hyz
        have hin : y ∈ z₀ :: rest := hcomplete y (lt_trans hz0_bd.1 hy1) hy2 hyz
        rcases List.mem_cons.mp hin with h | h
        · exact absurd h.symm (ne_of_lt hy1)
        · exact h
      -- The leftmost OPEN gap (lo, z₀) is zero-free.
      have hgap_no_zero : ∀ y : ℝ, lo < y → y < z₀ → h y = 0 → False := by
        intro y hy1 hy2 hyz
        have hin : y ∈ z₀ :: rest := hcomplete y hy1 (le_trans (le_of_lt hy2) hz0_bd.2) hyz
        rcases List.mem_cons.mp hin with h | h
        · exact absurd h (ne_of_lt hy2)
        · exact absurd (hrest_lt y h) (not_lt.mpr (le_of_lt hy2))
      -- midpoint of (lo, z₀): the left-gap witness.
      set m₀ : ℝ := (lo + z₀) / 2 with hm0_def
      have hm0_1 : lo < m₀ := by rw [hm0_def]; linarith [hz0_bd.1]
      have hm0_2 : m₀ < z₀ := by rw [hm0_def]; linarith [hz0_bd.1]
      have hm0_R : m₀ ≤ R := le_trans (le_of_lt hm0_2) hz0_bd.2
      have hm0_ne : h m₀ ≠ 0 := fun hz => hgap_no_zero m₀ hm0_1 hm0_2 hz
      -- left-gap sign-constancy: h same sign on all of (lo, z₀)
      have h_leftgap_same : ∀ x : ℝ, lo < x → x < z₀ → 0 < h m₀ * h x := by
        intro x hx1 hx2
        have hxne : h x ≠ 0 := fun hz => hgap_no_zero x hx1 hx2 hz
        apply psw_same_sign_on_gap h hcont _ hm0_ne hxne
        intro y hyz hymem
        rw [Set.mem_Ioo] at hymem
        have hy1 : lo < y := lt_of_lt_of_le (lt_min hm0_1 hx1) (le_of_lt hymem.1)
        have hy2 : y < z₀ := lt_of_lt_of_le hymem.2 (max_le (le_of_lt hm0_2) (le_of_lt hx2))
        exact hgap_no_zero y hy1 hy2 hyz
      -- Right gap upper endpoint g₁ = head of rest (or R if rest = []).
      -- Pick m₁ ∈ (z₀, g₁) as the right-gap witness, below all of rest hence below xs'.
      rcases eq_or_lt_of_le hz0_bd.2 with hz0R | hz0R
      · -- z₀ = R: then rest = [] (rest elements are > z₀ = R but ≤ R).
        have hrest_nil : rest = [] := by
          rcases List.eq_nil_or_concat rest with h | ⟨l, a, hla⟩
          · exact h
          · exfalso
            have ha_mem : a ∈ rest := by rw [hla]; simp
            have hbd := hrest_bd a ha_mem
            have hgt := hbd.1; have hle := hbd.2
            rw [← hz0R] at hle; linarith
        subst hrest_nil
        -- zs = [z₀]; witness with xs = [], σ = left-gap sign, R-endpoint zero handled.
        rcases lt_or_gt_of_ne hm0_ne with hmneg | hmpos
        · refine ⟨[], -1, List.Pairwise.nil, by simp, by simp, by simp, Or.inr rfl, ?_⟩
          intro x hx1 hx2
          simp only [List.map_nil, List.prod_nil, mul_one]
          rcases lt_or_eq_of_le hx2 with hxlt | hxeq
          · have hxz0 : x < z₀ := by rw [hz0R]; exact hxlt
            have hss := h_leftgap_same x hx1 hxz0
            nlinarith [hss, hmneg]
          · -- x = R = z₀, h x = 0
            have hhx : h x = 0 := by rw [hxeq, ← hz0R]; exact hz0_zero
            rw [hhx]; simp
        · refine ⟨[], 1, List.Pairwise.nil, by simp, by simp, by simp, Or.inl rfl, ?_⟩
          intro x hx1 hx2
          simp only [List.map_nil, List.prod_nil, mul_one]
          rcases lt_or_eq_of_le hx2 with hxlt | hxeq
          · have hxz0 : x < z₀ := by rw [hz0R]; exact hxlt
            have hss := h_leftgap_same x hx1 hxz0
            nlinarith [hss, hmpos]
          · have hhx : h x = 0 := by rw [hxeq, ← hz0R]; exact hz0_zero
            rw [hhx]; simp
      · -- z₀ < R: recurse on rest over (z₀, R].
        obtain ⟨xs', σ', hxs'_sorted, hxs'_len, hxs'_bd, hxs'_zero, hσ', hwit'⟩ :=
          ih rest z₀ hrestlen (le_trans hlo_ge (le_of_lt hz0_bd.1)) hz0R
            hrest_sorted hrest_bd hrest_zero hrest_complete
        -- Right-gap upper bound g₁: smallest of rest's head and R.
        -- Define m₁ in (z₀, R], below all of rest (hence below all of xs').
        -- g₁ = if rest = [] then R else rest.head; m₁ = (z₀ + g₁)/2.
        set g₁ : ℝ := match rest with | [] => R | z :: _ => z with hg1_def
        have hz0_lt_g1 : z₀ < g₁ := by
          cases rest with
          | nil => simpa [hg1_def] using hz0R
          | cons z tl => simpa [hg1_def] using hrest_lt z List.mem_cons_self
        have hg1_le_R : g₁ ≤ R := by
          cases rest with
          | nil => simpa [hg1_def] using le_refl R
          | cons z tl => simpa [hg1_def] using (hrest_bd z List.mem_cons_self).2
        have hg1_lt_rest : ∀ z ∈ rest, g₁ ≤ z := by
          cases rest with
          | nil => intro z hz; simp at hz
          | cons w tl =>
            intro z hz
            simp only [hg1_def]
            rcases List.mem_cons.mp hz with h | h
            · exact le_of_eq h.symm
            · exact le_of_lt ((List.pairwise_cons.mp hrest_sorted).1 z h)
        set m₁ : ℝ := (z₀ + g₁) / 2 with hm1_def
        have hm1_1 : z₀ < m₁ := by rw [hm1_def]; linarith
        have hm1_2 : m₁ < g₁ := by rw [hm1_def]; linarith
        have hm1_R : m₁ ≤ R := le_trans (le_of_lt hm1_2) hg1_le_R
        -- m₁ is below all of xs' (xs' ⊆ rest-region, all ≥ g₁ > m₁).
        have hm1_below_xs' : ∀ z ∈ xs', m₁ < z := by
          intro z hz
          have hzrest : z₀ < z ∧ z ≤ R := hxs'_bd z hz
          -- z is a zero of h in (z₀, R], so z ∈ rest; hence g₁ ≤ z.
          have hzz : h z = 0 := hxs'_zero z hz
          have hzin_rest : z ∈ rest := hrest_complete z hzrest.1 hzrest.2 hzz
          exact lt_of_lt_of_le hm1_2 (hg1_lt_rest z hzin_rest)
        -- x below all xs' (for x < z₀): every xs' element > z₀.
        have hxs'_gt_z0 : ∀ z ∈ xs', z₀ < z := fun z hz => (hxs'_bd z hz).1
        -- m₁ is a non-zero point of h (it's in the open right gap (z₀, g₁)).
        have hm1_ne : h m₁ ≠ 0 := by
          intro hz
          -- m₁ ∈ (z₀, R], h m₁ = 0 ⇒ m₁ ∈ rest ⇒ g₁ ≤ m₁, contradiction with m₁ < g₁.
          have hm1_rest : m₁ ∈ rest := hrest_complete m₁ hm1_1 hm1_R hz
          exact absurd (hg1_lt_rest m₁ hm1_rest) (not_le.mpr hm1_2)
        -- recursion witness at m₁ is strictly positive.
        have hwit_m1 : 0 < σ' * (xs'.map (fun z => m₁ - z)).prod * h m₁ := by
          have hnn := hwit' m₁ hm1_1 hm1_R
          -- nonneg; show nonzero: σ' ≠ 0, prod ≠ 0 (m₁ ∉ xs'), h m₁ ≠ 0.
          rcases eq_or_lt_of_le hnn with heq | hlt
          · exfalso
            -- product is zero ⇒ some factor zero ⇒ m₁ ∈ xs', contradiction
            have hσ'_ne : σ' ≠ 0 := by rcases hσ' with rfl | rfl <;> norm_num
            have hprod_ne : (xs'.map (fun z => m₁ - z)).prod ≠ 0 := by
              rw [Ne, List.prod_eq_zero_iff]
              intro hmem
              simp only [List.mem_map] at hmem
              obtain ⟨z, hz, hz_eq⟩ := hmem
              have hlt : m₁ < z := hm1_below_xs' z hz
              have : m₁ - z = 0 := hz_eq
              linarith [sub_eq_zero.mp this]
            have : σ' * (xs'.map (fun z => m₁ - z)).prod * h m₁ ≠ 0 := by
              apply mul_ne_zero (mul_ne_zero hσ'_ne hprod_ne) hm1_ne
            exact this heq.symm
          · exact hlt
        -- p' abbreviation
        set p' : ℝ → ℝ := fun x => (xs'.map (fun z => x - z)).prod with hp'_def
        -- Witness on (z₀, R]: 0 ≤ σ' * p'(x) * h(x).
        -- Classify z₀ as a sign-change via h m₀ * h m₁.
        have hprod_mm : h m₀ * h m₁ ≠ 0 := mul_ne_zero hm0_ne hm1_ne
        rcases lt_or_gt_of_ne hprod_mm with hflip | hnoflip
        · -- SIGN CHANGE at z₀: include z₀, σ = σ'.
          refine ⟨z₀ :: xs', σ', ?_, ?_, ?_, ?_, hσ', ?_⟩
          · -- sorted: z₀ < all xs'
            rw [List.pairwise_cons]; exact ⟨fun z hz => hxs'_gt_z0 z hz, hxs'_sorted⟩
          · simp only [List.length_cons]; omega
          · intro z hz
            rcases List.mem_cons.mp hz with h | h
            · subst h; exact hz0_bd
            · exact ⟨lt_trans hz0_bd.1 (hxs'_gt_z0 z h), (hxs'_bd z h).2⟩
          · intro z hz
            rcases List.mem_cons.mp hz with h | h
            · subst h; exact hz0_zero
            · exact hxs'_zero z h
          · intro x hx1 hx2
            -- p₀(x) = (x - z₀) * p'(x)
            have hp0_eq : ((z₀ :: xs').map (fun z => x - z)).prod = (x - z₀) * p' x := by
              simp [hp'_def, List.map_cons, List.prod_cons]
            rw [hp0_eq]
            rcases lt_trichotomy x z₀ with hxlt | hxeq | hxgt
            · -- x ∈ (lo, z₀): left-gap argument
              have hsame_h : 0 < h m₀ * h x := h_leftgap_same x hx1 hxlt
              have hprod_pos : 0 < p' x * p' m₁ :=
                psw_prod_pos_below xs'
                  (fun z hz => lt_of_lt_of_le hxlt (le_of_lt (hxs'_gt_z0 z hz)))
                  (fun z hz => hm1_below_xs' z hz)
              have hxz0_neg : x - z₀ < 0 := by linarith
              -- h x and h m₁ have opposite signs.
              have hm0sq : 0 < h m₀ * h m₀ := mul_self_pos.mpr hm0_ne
              have hxm1 : h x * h m₁ < 0 := by nlinarith [hsame_h, hflip, hm0sq]
              -- σ'² = 1
              have hσ'sq : σ' * σ' = 1 := by rcases hσ' with rfl | rfl <;> norm_num
              -- target · (σ' p'm₁ h m₁) = σ'² (x-z₀)(p'x p'm₁)(h x h m₁) > 0
              have hkey : 0 < (σ' * (x - z₀) * p' x * h x) * (σ' * p' m₁ * h m₁) := by
                have hexpand : (σ' * (x - z₀) * p' x * h x) * (σ' * p' m₁ * h m₁)
                    = (σ' * σ') * ((x - z₀) * ((p' x * p' m₁) * (h x * h m₁))) := by ring
                rw [hexpand, hσ'sq, one_mul]
                have h1 : 0 < (p' x * p' m₁) * (-(h x * h m₁)) :=
                  mul_pos hprod_pos (by linarith)
                nlinarith [h1, hxz0_neg]
              -- conclude target ≥ 0 from target·(positive) > 0
              rcases mul_pos_iff.mp hkey with ⟨ht, _⟩ | ⟨_, hb⟩
              · linarith
              · linarith [hwit_m1]
            · -- x = z₀ : h x = 0
              rw [hxeq, hz0_zero]; simp
            · -- x ∈ (z₀, R]: recursion witness, extra positive factor (x - z₀)
              have hwit_x := hwit' x hxgt hx2
              have hxz0_pos : 0 < x - z₀ := by linarith
              -- σ' * ((x - z₀) * p'(x)) * h(x) = (x - z₀) * (σ' * p'(x) * h(x)) ≥ 0
              have : σ' * ((x - z₀) * p' x) * h x = (x - z₀) * (σ' * p' x * h x) := by ring
              rw [this]; exact mul_nonneg (le_of_lt hxz0_pos) hwit_x
        · -- NO SIGN CHANGE at z₀: exclude z₀, σ = σ'.
          refine ⟨xs', σ', hxs'_sorted, by omega, ?_, hxs'_zero, hσ', ?_⟩
          · intro z hz; exact ⟨lt_trans hz0_bd.1 (hxs'_gt_z0 z hz), (hxs'_bd z hz).2⟩
          · intro x hx1 hx2
            rcases lt_trichotomy x z₀ with hxlt | hxeq | hxgt
            · -- x ∈ (lo, z₀): left-gap, no extra factor; signs align (no flip)
              have hsame_h : 0 < h m₀ * h x := h_leftgap_same x hx1 hxlt
              have hprod_pos : 0 < p' x * p' m₁ :=
                psw_prod_pos_below xs'
                  (fun z hz => lt_of_lt_of_le hxlt (le_of_lt (hxs'_gt_z0 z hz)))
                  (fun z hz => hm1_below_xs' z hz)
              show 0 ≤ σ' * p' x * h x
              -- h x and h m₁ have the same sign.
              have hm0sq : 0 < h m₀ * h m₀ := mul_self_pos.mpr hm0_ne
              have hxm1 : 0 < h x * h m₁ := by nlinarith [hsame_h, hnoflip, hm0sq]
              have hσ'sq : σ' * σ' = 1 := by rcases hσ' with rfl | rfl <;> norm_num
              have hkey : 0 < (σ' * p' x * h x) * (σ' * p' m₁ * h m₁) := by
                have hexpand : (σ' * p' x * h x) * (σ' * p' m₁ * h m₁)
                    = (σ' * σ') * ((p' x * p' m₁) * (h x * h m₁)) := by ring
                rw [hexpand, hσ'sq, one_mul]
                exact mul_pos hprod_pos hxm1
              rcases mul_pos_iff.mp hkey with ⟨ht, _⟩ | ⟨_, hb⟩
              · linarith
              · linarith [hwit_m1]
            · rw [hxeq]; show 0 ≤ σ' * p' z₀ * h z₀; rw [hz0_zero]; simp
            · exact hwit' x hxgt hx2

/-- The map `x ↦ ∏_{z ∈ l}(x - z)` is continuous. -/
private lemma psw_prod_continuous (l : List ℝ) :
    Continuous (fun x : ℝ => (l.map (fun z => x - z)).prod) := by
  induction l with
  | nil => simpa using continuous_const
  | cons a rest ih =>
    have heq : (fun x : ℝ => ((a :: rest).map (fun z => x - z)).prod)
        = (fun x : ℝ => (x - a) * (rest.map (fun z => x - z)).prod) := by
      funext x; simp [List.map_cons, List.prod_cons]
    rw [heq]
    exact (continuous_id.sub continuous_const).mul ih

/-- **Piecewise sign witness.**

Given a continuous `h : ℝ → ℝ`, `R > 0`, and the COMPLETE sorted list `zsAll` of
zeros of `h` on `[-R, R]` (length ≤ 6), there is a sub-list `xs` of "sign-change"
points and a global sign `σ ∈ {±1}` such that the product polynomial
`p₀ = ∏_{z ∈ xs}(x - z)` satisfies `0 ≤ σ · p₀(x) · h(x)` for all `x ∈ [-R, R]`.

No simple-zero / derivative hypothesis is needed: tangent (even-order) zeros of
`h` lie inside a sign-constant gap and are simply omitted from `xs`. -/
theorem PiecewiseSignWitness
    (h : ℝ → ℝ) (hcont : Continuous h) (R : ℝ) (hR : 0 < R)
    (zsAll : List ℝ)
    (hsorted : zsAll.Pairwise (· < ·))
    (hzin : ∀ z ∈ zsAll, -R ≤ z ∧ z ≤ R)
    (hzzero : ∀ z ∈ zsAll, h z = 0)
    (hzcomplete : ∀ y : ℝ, -R ≤ y → y ≤ R → h y = 0 → y ∈ zsAll)
    (hzlen : zsAll.length ≤ 6) :
    ∃ (xs : List ℝ) (σ : ℝ),
      xs.Pairwise (· < ·) ∧
      xs.length ≤ 6 ∧
      (∀ z ∈ xs, -R ≤ z ∧ z ≤ R) ∧
      (∀ z ∈ xs, h z = 0) ∧
      (σ = 1 ∨ σ = -1) ∧
      ∀ x : ℝ, |x| ≤ R →
        0 ≤ σ * (xs.map (fun z => x - z)).prod * h x := by
  -- zeros strictly inside (-R, R]
  set zs : List ℝ := zsAll.filter (fun z => decide (-R < z)) with hzs_def
  have hmem_iff : ∀ z, z ∈ zs ↔ z ∈ zsAll ∧ -R < z := by
    intro z; rw [hzs_def, List.mem_filter, decide_eq_true_eq]
  have hzs_sorted : zs.Pairwise (· < ·) := hsorted.filter _
  have hzs_bd : ∀ z ∈ zs, -R < z ∧ z ≤ R := by
    intro z hz; rw [hmem_iff] at hz; exact ⟨hz.2, (hzin z hz.1).2⟩
  have hzs_zero : ∀ z ∈ zs, h z = 0 := by
    intro z hz; rw [hmem_iff] at hz; exact hzzero z hz.1
  have hzs_complete : ∀ y : ℝ, -R < y → y ≤ R → h y = 0 → y ∈ zs := by
    intro y hy1 hy2 hyz
    rw [hmem_iff]
    exact ⟨hzcomplete y (le_of_lt hy1) hy2 hyz, hy1⟩
  have hzs_len : zs.length ≤ 6 := le_trans (List.length_filter_le _ _) hzlen
  -- apply the core on (-R, R]
  obtain ⟨xs, σ, hxs_sorted, hxs_len, hxs_bd, hxs_zero, hσ, hwit⟩ :=
    psw_core h hcont R hR zs.length zs (-R) rfl (le_refl _) (by linarith)
      hzs_sorted hzs_bd hzs_zero hzs_complete
  refine ⟨xs, σ, hxs_sorted, le_trans hxs_len hzs_len, ?_, hxs_zero, hσ, ?_⟩
  · intro z hz; exact ⟨le_of_lt (hxs_bd z hz).1, (hxs_bd z hz).2⟩
  · -- extend witness to all of [-R, R].
    -- Define g(x) = σ * ∏(x - z) * h x, continuous, ≥ 0 on (-R, R], hence ≥ 0 at -R.
    set g : ℝ → ℝ := fun x => σ * (xs.map (fun z => x - z)).prod * h x with hg_def
    have hg_cont : Continuous g := by
      rw [hg_def]
      exact (continuous_const.mul (psw_prod_continuous xs)).mul hcont
    intro x hxR
    rw [abs_le] at hxR
    obtain ⟨hx1, hx2⟩ := hxR
    rcases lt_or_eq_of_le hx1 with hxgt | hxeq
    · -- x ∈ (-R, R]
      exact hwit x hxgt hx2
    · -- x = -R : use continuity / limit from the right
      -- g ≥ 0 on (-R, R], -R ∈ closure, g continuous ⇒ g(-R) ≥ 0.
      have hg_nonneg_right : ∀ y ∈ Set.Ioc (-R) R, 0 ≤ g y := by
        intro y hy; exact hwit y hy.1 hy.2
      have h_clos : (-R : ℝ) ∈ closure (Set.Ioc (-R) R) := by
        rw [closure_Ioc (by linarith : (-R : ℝ) ≠ R)]
        exact ⟨le_refl _, by linarith⟩
      have : (0 : ℝ) ≤ g (-R) := by
        have hle : ∀ y ∈ closure (Set.Ioc (-R) R), 0 ≤ g y := by
          apply (isClosed_le continuous_const hg_cont).closure_subset_iff.mpr
          intro y hy; exact hg_nonneg_right y hy
        exact hle (-R) h_clos
      rw [← hxeq]; exact this

end Workspace.ProofLemmas
