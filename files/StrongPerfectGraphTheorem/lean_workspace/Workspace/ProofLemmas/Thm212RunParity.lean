import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# Counting `Y`-complete edges along a **path**

The last paragraph of 21.2 (printed p. 135) counts `Y`-complete edges on three paths and
compares parities:

> *"... so by 2.2 and 2.3, an odd number of its edges are `Y`-complete.  Since `p_j` is not
> `Y`-complete, an odd number of edges of `p_j-⋯-p_k` are `Y`-complete.  The path
> `z-x_{t+1}-p₁-⋯-p_k` (`= P` say) is even, ... it follows that an even number of its edges are
> `Y`-complete, by 2.3.  We deduce that an odd number of edges of `z-x_{t+1}-p₁-⋯-p_j` are
> `Y`-complete.  There is therefore a `Y`-segment `P'` of this path that has odd length."*

`Workspace/ProofLemmas/SegmentBasics.lean` does this bookkeeping for a **hole**; this file is
the path-side counterpart.  It has two halves.

* An index count.  `pEdges G Y q n` is the number of `i < n` whose edge `q_i q_{i+1}` is
  `Y`-complete, and `ncard_yEdges_eq_pEdges` identifies it with the `Set (Sym2 V)` form of
  *"the number of `Y`-complete edges"* used by the statements of 2.2, 2.3 and 2.10.
* A purely combinatorial run lemma, `exists_odd_run`: if a predicate `f` has an odd number of
  consecutive pairs below `n` and fails at `n`, then some maximal run of `f` has an even number
  of members — this is the paper's *"there is therefore a `Y`-segment of odd length"*.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm212RunParity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open scoped Classical

/-! ### Maximal runs of a predicate on `ℕ` -/

section Runs

variable (f : ℕ → Prop)

/-- The number of members of the maximal run of `f` that ends at `n` (zero if `f n` fails). -/
noncomputable def curRun : ℕ → ℕ
  | 0 => if f 0 then 1 else 0
  | n + 1 => if f (n + 1) then curRun n + 1 else 0

/-- The number of `i < n` such that `f i` and `f (i+1)` both hold. -/
noncomputable def runEdges (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => f i ∧ f (i + 1))).card

theorem runEdges_zero : runEdges f 0 = 0 := by simp [runEdges]

theorem runEdges_succ (n : ℕ) :
    runEdges f (n + 1) = runEdges f n + (if f n ∧ f (n + 1) then 1 else 0) := by
  classical
  simp only [runEdges, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem curRun_eq_zero_iff (n : ℕ) : curRun f n = 0 ↔ ¬ f n := by
  cases n with
  | zero => by_cases h : f 0 <;> simp [curRun, h]
  | succ m => by_cases h : f (m + 1) <;> simp [curRun, h]

theorem curRun_le (n : ℕ) : curRun f n ≤ n + 1 := by
  induction n with
  | zero => by_cases h : f 0 <;> simp [curRun, h]
  | succ m ih =>
    by_cases h : f (m + 1)
    · simp only [curRun, if_pos h]; omega
    · simp only [curRun, if_neg h]; omega

/-- Every index of the run ending at `n` satisfies `f`. -/
theorem curRun_mem {n : ℕ} : ∀ j, n + 1 - curRun f n ≤ j → j ≤ n → f j := by
  induction n with
  | zero =>
    intro j h1 h2
    interval_cases j
    by_cases h : f 0
    · exact h
    · simp only [curRun, if_neg h] at h1; omega
  | succ m ih =>
    intro j h1 h2
    by_cases h : f (m + 1)
    · simp only [curRun, if_pos h] at h1
      rcases Nat.lt_or_ge j (m + 1) with hj | hj
      · exact ih j (by omega) (by omega)
      · have : j = m + 1 := by omega
        exact this ▸ h
    · simp only [curRun, if_neg h] at h1; omega

/-- The run ending at `n` is maximal on the left. -/
theorem curRun_bd (n : ℕ) : curRun f n = n + 1 ∨ ¬ f (n - curRun f n) := by
  induction n with
  | zero =>
    by_cases h : f 0
    · exact Or.inl (by simp [curRun, h])
    · exact Or.inr (by simp [curRun, h])
  | succ m ih =>
    by_cases h : f (m + 1)
    · simp only [curRun, if_pos h]
      rcases ih with hi | hi
      · exact Or.inl (by omega)
      · rcases Nat.eq_or_lt_of_le (curRun_le f m) with he | hlt
        · exact Or.inl (by omega)
        · refine Or.inr ?_
          rw [show m + 1 - (curRun f m + 1) = m - curRun f m by omega]
          exact hi
    · exact Or.inr (by simp only [curRun, if_neg h, Nat.sub_zero]; exact h)

/-- **Parity bookkeeping.**  If no maximal run below `n` has an even number of members, then
the number of consecutive `f`-pairs below `n` has the parity of `curRun f n - 1`. -/
theorem runEdges_mod_two (n : ℕ)
    (hno : ∀ l r, l < r → r < n → (∀ j, l ≤ j → j ≤ r → f j) → ¬ f (r + 1) →
      (l = 0 ∨ ¬ f (l - 1)) → Even (r - l)) :
    runEdges f n % 2 = (curRun f n - 1) % 2 := by
  induction n with
  | zero =>
    rw [runEdges_zero]
    by_cases h : f 0 <;> simp [curRun, h]
  | succ m ih =>
    have ihm := ih (fun l r h1 h2 => hno l r h1 (by omega))
    rw [runEdges_succ]
    by_cases h1 : f (m + 1)
    · have hcur : curRun f (m + 1) = curRun f m + 1 := by simp only [curRun, if_pos h1]
      rw [hcur]
      by_cases h0 : f m
      · rw [if_pos (show f m ∧ f (m + 1) from ⟨h0, h1⟩)]
        have hpos : 1 ≤ curRun f m := by
          rcases Nat.eq_zero_or_pos (curRun f m) with he | hp
          · exact absurd ((curRun_eq_zero_iff f m).mp he) (not_not.mpr h0)
          · omega
        omega
      · rw [if_neg (show ¬ (f m ∧ f (m + 1)) from fun hc => h0 hc.1)]
        have he : curRun f m = 0 := (curRun_eq_zero_iff f m).mpr h0
        rw [he] at ihm ⊢
        simpa using ihm
    · have hcur : curRun f (m + 1) = 0 := by simp only [curRun, if_neg h1]
      rw [hcur, if_neg (show ¬ (f m ∧ f (m + 1)) from fun hc => h1 hc.2)]
      by_cases h0 : f m
      · have hpos : 1 ≤ curRun f m := by
          rcases Nat.eq_zero_or_pos (curRun f m) with he | hp
          · exact absurd ((curRun_eq_zero_iff f m).mp he) (not_not.mpr h0)
          · omega
        have hle : curRun f m ≤ m + 1 := curRun_le f m
        have hkodd : curRun f m % 2 = 1 := by
          rcases Nat.lt_or_ge (curRun f m) 2 with hk1 | hk2
          · omega
          · have hrun : Even (m - (m + 1 - curRun f m)) := by
              refine hno (m + 1 - curRun f m) m (by omega) (by omega)
                (fun j hj1 hj2 => curRun_mem f j (by omega) hj2) h1 ?_
              rcases curRun_bd f m with hb | hb
              · exact Or.inl (by omega)
              · refine Or.inr ?_
                rw [show m + 1 - curRun f m - 1 = m - curRun f m by omega]
                exact hb
            obtain ⟨d, hd⟩ := hrun
            omega
        omega
      · have he : curRun f m = 0 := (curRun_eq_zero_iff f m).mpr h0
        rw [he] at ihm
        simpa using ihm

/-- **The run extraction of the last paragraph of 21.2.**  If `f` fails at `n` and there is an
odd number of consecutive `f`-pairs below `n`, then some maximal run of `f` inside `[0, n)` has
an even number of members, that is, `Odd (r - l)`. -/
theorem exists_odd_run {f : ℕ → Prop} {n : ℕ} (hn : ¬ f n) (hodd : Odd (runEdges f n)) :
    ∃ l r : ℕ, l < r ∧ r < n ∧ Odd (r - l) ∧ (∀ j, l ≤ j → j ≤ r → f j) ∧
      ¬ f (r + 1) ∧ (l = 0 ∨ ¬ f (l - 1)) := by
  by_contra hcon
  have hno : ∀ l r, l < r → r < n → (∀ j, l ≤ j → j ≤ r → f j) → ¬ f (r + 1) →
      (l = 0 ∨ ¬ f (l - 1)) → Even (r - l) := by
    intro l r h1 h2 h3 h4 h5
    exact Nat.not_odd_iff_even.mp (fun h6 => hcon ⟨l, r, h1, h2, h6, h3, h4, h5⟩)
  have hkey := runEdges_mod_two f n hno
  rw [(curRun_eq_zero_iff f n).mpr hn] at hkey
  simp only [Nat.zero_sub] at hkey
  rw [Nat.odd_iff] at hodd
  omega

/-- Re-indexing a stretch of the count.  Used to identify the `Y`-complete edges of the
subpath `p_j-⋯-p_k` with those of the corresponding stretch of `z-x_{t+1}-p₁-⋯-p_k`. -/
theorem card_Ico_filter_shift (f g : ℕ → Prop) (a b c : ℕ)
    (hfg : ∀ i, a ≤ i → i < b → ((f (i + c) ∧ f (i + c + 1)) ↔ (g i ∧ g (i + 1)))) :
    ((Finset.Ico (a + c) (b + c)).filter (fun i => f i ∧ f (i + 1))).card
      = ((Finset.Ico a b).filter (fun i => g i ∧ g (i + 1))).card := by
  classical
  rw [← Finset.map_add_right_Ico a b c, Finset.filter_map, Finset.card_map]
  congr 1
  refine Finset.filter_congr ?_
  intro i hi
  rw [Finset.mem_Ico] at hi
  simpa using hfg i hi.1 hi.2

end Runs

/-! ### The `Y`-complete edges of a path -/

section Path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {Y : Set V} {q : List V}

/-- *"`q_i` is `Y`-complete"*, in a form total in `i`. -/
def VC (G : SimpleGraph V) (Y : Set V) (q : List V) (i : ℕ) : Prop :=
  ∃ u : V, q[i]? = some u ∧ VertexComplete G u Y

theorem vc_iff_getElem {i : ℕ} (hi : i < q.length) :
    VC G Y q i ↔ VertexComplete G (q[i]'hi) Y := by
  constructor
  · rintro ⟨u, hu, hc⟩
    rw [List.getElem?_eq_getElem hi] at hu
    exact (Option.some.inj hu) ▸ hc
  · intro hc
    exact ⟨q[i]'hi, List.getElem?_eq_getElem hi, hc⟩

theorem not_vc_of_length_le {i : ℕ} (hi : q.length ≤ i) : ¬ VC G Y q i := by
  rintro ⟨u, hu, -⟩
  rw [List.getElem?_eq_none hi] at hu
  simp at hu

/-- The number of `i < n` whose edge `q_i q_{i+1}` is `Y`-complete. -/
noncomputable def pEdges (G : SimpleGraph V) (Y : Set V) (q : List V) (n : ℕ) : ℕ :=
  runEdges (VC G Y q) n

/-- On a path, *"the edge `q_i q_{i+1}` is `Y`-complete"* is exactly *"both `q_i` and `q_{i+1}`
are `Y`-complete"*: consecutive vertices of a path are adjacent. -/
theorem edgeComplete_iff_vc (hq : IsPathList G q) {i : ℕ} (hi : i + 1 < q.length) :
    EdgeComplete G Y (q[i]'(by omega)) (q[i + 1]'hi) ↔ (VC G Y q i ∧ VC G Y q (i + 1)) := by
  rw [vc_iff_getElem (by omega), vc_iff_getElem hi]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨PathBasics.path_adj_succ hq hi, h.1, h.2⟩⟩

/-- **The paper's count of `Y`-complete edges of a path, as an index count.** -/
theorem ncard_yEdges_eq_pEdges (hq : IsPathList G q) :
    {e : Sym2 V | ∃ u ∈ q, ∃ v ∈ q, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard
      = pEdges G Y q (q.length - 1) := by
  classical
  have hne : q ≠ [] := hq.1
  have hpos : 0 < q.length := List.length_pos_of_ne_nil hne
  set d : V := q.head hne with hd
  set S : Finset ℕ :=
    (Finset.range (q.length - 1)).filter (fun i => VC G Y q i ∧ VC G Y q (i + 1)) with hS
  have hmemS : ∀ i, i ∈ S ↔ (i + 1 < q.length ∧ VC G Y q i ∧ VC G Y q (i + 1)) := by
    intro i
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  have hgetD : ∀ (i : ℕ) (hi : i < q.length), q.getD i d = q[i]'hi := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
  have hkey : {e : Sym2 V | ∃ u ∈ q, ∃ v ∈ q, e = s(u, v) ∧ EdgeComplete G Y u v}
      = ↑(S.image (fun i => s(q.getD i d, q.getD (i + 1) d))) := by
    ext e
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hE⟩
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hv
      rcases (PathBasics.path_adj_iff hq ha hb).mp hE.1 with hab | hab
      · refine ⟨a, (hmemS a).mpr ⟨by omega, ?_⟩, ?_⟩
        · rw [← edgeComplete_iff_vc hq (by omega)]
          have : (q[b]'hb) = q[a + 1]'(by omega) := by
            subst hab; rfl
          rw [this] at hE; exact hE
        · rw [hgetD a ha, hgetD (a + 1) (by omega)]
          subst hab; rfl
      · refine ⟨b, (hmemS b).mpr ⟨by omega, ?_⟩, ?_⟩
        · rw [← edgeComplete_iff_vc hq (by omega)]
          have : (q[a]'ha) = q[b + 1]'(by omega) := by
            subst hab; rfl
          rw [this] at hE
          exact ⟨hE.1.symm, hE.2.2, hE.2.1⟩
        · rw [hgetD b hb, hgetD (b + 1) (by omega)]
          subst hab
          exact Sym2.eq_swap
    · rintro ⟨i, hi, rfl⟩
      rw [hmemS i] at hi
      obtain ⟨hlt, hvc⟩ := hi
      rw [hgetD i (by omega), hgetD (i + 1) hlt]
      exact ⟨_, List.getElem_mem _, _, List.getElem_mem _, rfl,
        (edgeComplete_iff_vc hq hlt).mpr hvc⟩
  have hinj : Set.InjOn (fun i => s(q.getD i d, q.getD (i + 1) d)) ↑S := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hmemS] at ha hb
    simp only at hab
    rw [hgetD a (by omega), hgetD (a + 1) ha.1, hgetD b (by omega), hgetD (b + 1) hb.1] at hab
    have hnd : q.Nodup := PathBasics.path_nodup hq
    rcases Sym2.eq_iff.mp hab with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hnd.getElem_inj_iff.mp h1
    · have i1 := hnd.getElem_inj_iff.mp h1
      have i2 := hnd.getElem_inj_iff.mp h2
      omega
  rw [hkey, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]
  rfl

/-- Splitting the count at an intermediate index. -/
theorem runEdges_split (f : ℕ → Prop) {a b : ℕ} (hab : a ≤ b) :
    runEdges f b = runEdges f a + ((Finset.Ico a b).filter (fun i => f i ∧ f (i + 1))).card := by
  classical
  simp only [runEdges, Finset.range_eq_Ico]
  rw [show Finset.Ico 0 b = Finset.Ico 0 a ∪ Finset.Ico a b from
      (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hab).symm,
    Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 0 a b))]

end Path

end Workspace.ProofLemmas.Thm212RunParity
