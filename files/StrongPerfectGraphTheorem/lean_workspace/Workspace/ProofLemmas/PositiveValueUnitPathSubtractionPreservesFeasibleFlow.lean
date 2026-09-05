import Workspace.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs

private theorem sum_count_by_eq_map_count
    {A V : Type*} [Fintype A] [DecidableEq A] [DecidableEq V]
    (u : A → V) (ρ : List A) (z : V) :
    (∑ a : A, if u a = z then ρ.count a else 0) = (ρ.map u).count z := by
  classical
  calc
    (∑ a : A, if u a = z then ρ.count a else 0) =
        ∑ a ∈ Finset.univ.filter (fun a => u a = z), ρ.count a := by
          rw [Finset.sum_filter]
    _ = ∑ a ∈ ρ.toFinset.filter (fun a => u a = z), ρ.count a := by
          symm
          apply Finset.sum_subset
          · intro a ha
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩
          · intro a ha ha'
            apply List.count_eq_zero.mpr
            intro haρ
            apply ha'
            exact Finset.mem_filter.mpr
              ⟨List.mem_toFinset.mpr haρ, (Finset.mem_filter.mp ha).2⟩
    _ = ρ.countP (fun a : A => u a = z) := by
          simpa using
            (Finset.sum_filter_count_eq_countP (fun a : A => u a = z) ρ)
    _ = (ρ.map u).count z := by
          simp only [List.count, List.countP_map]
          congr 1

private theorem tail_map_append_eq_cons_head_map
    {A V : Type*} (tail head : A → V) :
    ∀ (ρ : List A) (s t : V),
      ρ ≠ [] →
      (∃ a, ρ.head? = some a ∧ tail a = s) →
      (∃ a, ρ.getLast? = some a ∧ head a = t) →
      (∀ ab ∈ ρ.zip ρ.tail, head ab.1 = tail ab.2) →
      ρ.map tail ++ [t] = s :: ρ.map head := by
  intro ρ
  induction ρ using List.twoStepInduction with
  | nil =>
      intro s t hρne _ _ _
      exact (hρne rfl).elim
  | singleton a =>
      intro s t _ hρhead hρlast _
      rcases hρhead with ⟨a', ha', htail⟩
      rcases hρlast with ⟨a'', ha'', hhead⟩
      have ha : a = a' := Option.some.inj (by simpa using ha')
      subst a'
      have ha : a = a'' := Option.some.inj (by simpa using ha'')
      subst a''
      simp [htail, hhead]
  | cons_cons a b xs ihxs ihb =>
      intro s t _ hρhead hρlast hρlink
      rcases hρhead with ⟨a', ha', htail⟩
      have ha : a = a' := Option.some.inj (by simpa using ha')
      subst a'
      have hab : head a = tail b := hρlink (a, b) (by simp)
      have hρhead' : ∃ c, (b :: xs).head? = some c ∧ tail c = head a := by
        exact ⟨b, by simp, hab.symm⟩
      have hρlast' : ∃ c, (b :: xs).getLast? = some c ∧ head c = t := by
        simpa only [List.getLast?_cons_cons] using hρlast
      have hρlink' : ∀ ab ∈ (b :: xs).zip (b :: xs).tail,
          head ab.1 = tail ab.2 := by
        intro ab hab'
        apply hρlink ab
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
        right
        simpa only [List.tail_cons] using hab'
      have hrec := ihb b (head a) t (by simp) hρhead' hρlast' hρlink'
      simpa only [List.map_cons, List.cons_append, htail] using
        congrArg (fun q : List V => tail a :: q) hrec

theorem PositiveValueUnitPathSubtractionPreservesFeasibleFlow
    {V A : Type*}
    [Fintype V] [Fintype A] [DecidableEq A]
    (tail head : A → V) (cap f : A → ℕ) (s t : V) (k : ℕ)
    (hst : s ≠ t)
    (hk : 0 < k)
    (hflow : IsFeasibleIntegralFlow tail head cap f s t k)
    (ρ : List A)
    (hρne : ρ ≠ [])
    (hρhead : ∃ a, ρ.head? = some a ∧ tail a = s)
    (hρlast : ∃ a, ρ.getLast? = some a ∧ head a = t)
    (hρlink : ∀ ab ∈ ρ.zip ρ.tail, head ab.1 = tail ab.2)
    (hρnodup : (s :: ρ.map head).Nodup)
    (hρload : ∀ a, ρ.count a ≤ f a) :
    IsFeasibleIntegralFlow tail head cap
      (fun a => f a - ρ.count a) s t (k - 1) := by
  classical
  rcases hflow with ⟨hcap, hcons, hsource, hsink⟩
  let g : A → ℕ := fun a => f a - ρ.count a
  have hpoint (a : A) : f a = g a + ρ.count a := by
    dsimp [g]
    exact (Nat.sub_add_cancel (hρload a)).symm
  have hpath : ρ.map tail ++ [t] = s :: ρ.map head :=
    tail_map_append_eq_cons_head_map tail head ρ s t hρne hρhead hρlast hρlink
  have hcounts (z : V) :
      (ρ.map tail).count z + (if t = z then 1 else 0) =
        (ρ.map head).count z + (if s = z then 1 else 0) := by
    have h := congrArg (fun q : List V => q.count z) hpath
    simpa [List.count_append, List.count_cons, List.count_nil, beq_iff_eq] using h
  have htailcount (z : V) :
      flowOut tail (fun a => ρ.count a) z = (ρ.map tail).count z := by
    simpa [flowOut] using (sum_count_by_eq_map_count tail ρ z)
  have hheadcount (z : V) :
      flowIn head (fun a => ρ.count a) z = (ρ.map head).count z := by
    simpa [flowIn] using (sum_count_by_eq_map_count head ρ z)
  have houtdecomp (z : V) :
      flowOut tail f z = flowOut tail g z +
        flowOut tail (fun a => ρ.count a) z := by
    simp only [flowOut]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : tail a = z
    · simp [ha, hpoint a]
    · simp [ha]
  have hindecomp (z : V) :
      flowIn head f z = flowIn head g z +
        flowIn head (fun a => ρ.count a) z := by
    simp only [flowIn]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : head a = z
    · simp [ha, hpoint a]
    · simp [ha]
  change IsFeasibleIntegralFlow tail head cap g s t (k - 1)
  unfold IsFeasibleIntegralFlow
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact (Nat.sub_le _ _).trans (hcap a)
  · intro z hzs hzt
    have hsz : s ≠ z := Ne.symm hzs
    have htz : t ≠ z := Ne.symm hzt
    have hpathz : flowOut tail (fun a => ρ.count a) z =
        flowIn head (fun a => ρ.count a) z := by
      rw [htailcount, hheadcount]
      have hzcount := hcounts z
      simp [hsz, htz] at hzcount
      exact hzcount
    have hsum : flowOut tail g z + flowOut tail (fun a => ρ.count a) z =
        flowIn head g z + flowIn head (fun a => ρ.count a) z := by
      rw [← houtdecomp, ← hindecomp]
      exact hcons z hzs hzt
    omega
  · have hts : t ≠ s := Ne.symm hst
    have hpathsource : flowOut tail (fun a => ρ.count a) s =
        flowIn head (fun a => ρ.count a) s + 1 := by
      rw [htailcount, hheadcount]
      have hscount := hcounts s
      simp [hts] at hscount
      omega
    have hsum : flowOut tail g s + flowOut tail (fun a => ρ.count a) s =
        (flowIn head g s + flowIn head (fun a => ρ.count a) s) + k := by
      rw [← houtdecomp, ← hindecomp]
      exact hsource
    have hk' : k = (k - 1) + 1 := by omega
    omega
  · have hpathtarget : flowIn head (fun a => ρ.count a) t =
        flowOut tail (fun a => ρ.count a) t + 1 := by
      rw [htailcount, hheadcount]
      have htcount := hcounts t
      simp [hst] at htcount
      omega
    have hsum : flowIn head g t + flowIn head (fun a => ρ.count a) t =
        (flowOut tail g t + flowOut tail (fun a => ρ.count a) t) + k := by
      rw [← hindecomp, ← houtdecomp]
      exact hsink
    have hk' : k = (k - 1) + 1 := by omega
    omega

end Workspace.ProofLemmas
