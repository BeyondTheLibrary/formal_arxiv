import Workspace.ProofLemmas.Thm95OffspringFacts

/-!
# The second bullet of 9.5(1): twists against `S₀`, or a strip that absorbs `F`

PAPER (9.5(1), printed p. 52): *"• for all `i` with `1 ≤ i ≤ m`, there exists `j` with
`1 ≤ j ≤ n` such that `S₀, Sᵢ` disagree on one of the offspring of `Tⱼ`, and there exists `j`
such that `S₀, Sᵢ` agree on one of the offspring of `Tⱼ`.  For if the first were false, say,
then each of the `Tⱼ`'s has only one offspring, and we could add `f₁` to `Aᵢ`, `{f₂,…,f_{k-1}}`
to `Cᵢ`, and `f_k` to `Bᵢ`, contradicting the maximality of the striation; while if the second
were false we could do the same with `f₁, f_k` exchanged."*

"`S₀, Sᵢ` agree on one offspring and disagree on another" is exactly "`(S₀, Sᵢ, O, O')` is a
twist" for those two offspring, so the bullet is the dichotomy proved here.  No maximality
hypothesis is available, so the escape clause is returned rather than refuted: it says that
`f₁, f_k` have, on every antistrip, the same neighbours as the two ends of `Sᵢ`, which is what
makes adding them to `Sᵢ` a striation (`Thm95OffspringMerge.merge_striation`).

The argument.  If some `Tⱼ` has two offspring `M, N`, they alone make the twist: `S₀` is
parallel with `M` and co-parallel with `N`, while `Sᵢ` keeps one and the same relation to both.
Otherwise every `Tⱼ` has a single offspring, which is `Tⱼ` itself.  If `S₀` and `Sᵢ` agree on
one of them and disagree on another, those two make the twist.  If they agree on all of them,
then reading off the neighbours of the ends (`adjA_par` and friends) shows that `f₁` copies the
end of `Sᵢ` in `Aᵢ` and `f_k` the end in `Bᵢ`; if they disagree on all of them, the same holds
with the two ends exchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95OffspringGapTwist

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs

variable {V : Type*} {G : SimpleGraph V}

/-! ### The neighbours of an end of a strip on an antistrip -/

/-- If `S` and `T` are parallel, the end of `S` in `A` sees exactly `X ∪ Z`. -/
theorem adjA_par {Sx Tx : Set V × Set V × Set V} (h : ParallelStripAntistrip G Sx Tx)
    {a : V} (ha : a ∈ Sx.1) {w : V} (hw : w ∈ stripVertices Tx) :
    (G.Adj a w ↔ (w ∈ Tx.1 ∨ w ∈ Tx.2.1)) := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  refine ⟨fun hadj => ?_, fun hmem => h.1.1 a ha w hmem⟩
  rcases hw with (hw | hw) | hw
  · exact Or.inl hw
  · exact absurd hadj.symm (h.2.2 w hw a (Or.inl ha))
  · exact Or.inr hw

/-- If `S` and `T` are parallel, the end of `S` in `B` sees exactly `Y ∪ Z`. -/
theorem adjB_par {Sx Tx : Set V × Set V × Set V} (h : ParallelStripAntistrip G Sx Tx)
    {b : V} (hb : b ∈ Sx.2.2) {w : V} (hw : w ∈ stripVertices Tx) :
    (G.Adj b w ↔ (w ∈ Tx.2.2 ∨ w ∈ Tx.2.1)) := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  refine ⟨fun hadj => ?_, fun hmem => h.1.2 b hb w hmem⟩
  rcases hw with (hw | hw) | hw
  · exact absurd hadj.symm (h.2.1 w hw b (Or.inl hb))
  · exact Or.inl hw
  · exact Or.inr hw

/-- If `S` and `T` are co-parallel, the end of `S` in `A` sees exactly `Y ∪ Z`. -/
theorem adjA_cop {Sx Tx : Set V × Set V × Set V} (h : CoParallel G Sx Tx)
    {a : V} (ha : a ∈ Sx.1) {w : V} (hw : w ∈ stripVertices Tx) :
    (G.Adj a w ↔ (w ∈ Tx.2.2 ∨ w ∈ Tx.2.1)) := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  refine ⟨fun hadj => ?_, fun hmem => h.1.1 a ha w hmem⟩
  rcases hw with (hw | hw) | hw
  · exact absurd hadj.symm (h.2.2 w hw a (Or.inl ha))
  · exact Or.inl hw
  · exact Or.inr hw

/-- If `S` and `T` are co-parallel, the end of `S` in `B` sees exactly `X ∪ Z`. -/
theorem adjB_cop {Sx Tx : Set V × Set V × Set V} (h : CoParallel G Sx Tx)
    {b : V} (hb : b ∈ Sx.2.2) {w : V} (hw : w ∈ stripVertices Tx) :
    (G.Adj b w ↔ (w ∈ Tx.1 ∨ w ∈ Tx.2.1)) := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨X, Z, Y⟩ := Tx
  refine ⟨fun hadj => ?_, fun hmem => h.1.2 b hb w hmem⟩
  rcases hw with (hw | hw) | hw
  · exact Or.inl hw
  · exact absurd hadj.symm (h.2.1 w hw b (Or.inl hb))
  · exact Or.inr hw

/-! ### The offspring of an antistrip with only one offspring -/

/-- **PAPER (9.5(1), p. 52):** *"If one of `Mⱼ, Nⱼ` is empty, then the other equals `V(Tⱼ)`, and
so the only offspring of `Tⱼ` is `Tⱼ` itself."* -/
theorem offspring_eq_self (Tx : Set V × Set V × Set V) (Wset : Set V)
    (h : offVerts G Tx Wset = stripVertices Tx) : offspring G Tx Wset = Tx := by
  obtain ⟨X, Z, Y⟩ := Tx
  have h1 : offVerts G (X, Z, Y) Wset ∩ X = X :=
    Set.inter_eq_right.mpr (fun z hz => h ▸ Or.inl (Or.inl hz))
  have h2 : offVerts G (X, Z, Y) Wset ∩ Z = Z :=
    Set.inter_eq_right.mpr (fun z hz => h ▸ Or.inr hz)
  have h3 : offVerts G (X, Z, Y) Wset ∩ Y = Y :=
    Set.inter_eq_right.mpr (fun z hz => h ▸ Or.inl (Or.inr hz))
  show (offVerts G (X, Z, Y) Wset ∩ X, offVerts G (X, Z, Y) Wset ∩ Z,
    offVerts G (X, Z, Y) Wset ∩ Y) = (X, Z, Y)
  rw [h1, h2, h3]


/-! ### Nonemptiness bookkeeping -/

theorem fst_nonempty {Tx : Set V × Set V × Set V} (h : IsStrip G Tx) : (Tx.1).Nonempty := by
  obtain ⟨A, C, B⟩ := Tx; exact h.2.2.2.1

theorem thd_nonempty {Tx : Set V × Set V × Set V} (h : IsStrip G Tx) : (Tx.2.2).Nonempty := by
  obtain ⟨A, C, B⟩ := Tx; exact h.2.2.2.2.1

theorem stripVertices_nonempty {Tx : Set V × Set V × Set V} (h : IsStrip G Tx) :
    (stripVertices Tx).Nonempty := by
  obtain ⟨A, C, B⟩ := Tx
  obtain ⟨a, ha⟩ := h.2.2.2.1
  exact ⟨a, Or.inl (Or.inl ha)⟩

/-! ### The dichotomy -/

/-- **PAPER (9.5(1), p. 52, second bullet).**  Either every `Sᵢ` is in a twist with `S₀` on two
of the offspring, or some `Sᵢ` has ends whose neighbours on every antistrip are exactly those of
`f₁` and of `f_k`, in one order or the other. -/
theorem twist_or_merge_aux {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) {R : List V} {r s : V} (W : Bool → Set V)
    (hS0par : ∀ j : Fin n,
      ParallelStripAntistrip G (newStrip R r s) (offspring G (T j) (W true)))
    (hS0cop : ∀ j : Fin n, CoParallel G (newStrip R r s) (offspring G (T j) (W false)))
    (hcov : ∀ j : Fin n,
      offVerts G (T j) (W true) ∪ offVerts G (T j) (W false) = stripVertices (T j)) :
    (∀ i : Fin m, ∃ p q : Fin n × Bool, p ≠ q ∧
        (offVerts G (T p.1) (W p.2)).Nonempty ∧
        (offVerts G (T q.1) (W q.2)).Nonempty ∧
        IsTwist G (newStrip R r s) (S i)
          (offspring G (T p.1) (W p.2)) (offspring G (T q.1) (W q.2))) ∨
      (∃ (i : Fin m) (a b : V),
        ((a ∈ (S i).1 ∧ b ∈ (S i).2.2) ∨ (a ∈ (S i).2.2 ∧ b ∈ (S i).1)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj r w ↔ G.Adj a w)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj s w ↔ G.Adj b w))) := by
  classical
  have hSipc : ∀ (i : Fin m) (j : Fin n),
      ParallelStripAntistrip G (S i) (T j) ∨ CoParallel G (S i) (T j) :=
    hL.2.2.2.2.2.2.2.2.2.2.2.1
  -- One antistrip with two offspring already provides the twist.
  have htwoOff : ∀ (i : Fin m) (j : Fin n),
      IsTwist G (newStrip R r s) (S i) (offspring G (T j) (W true))
        (offspring G (T j) (W false)) := by
    intro i j
    rcases hSipc i j with hp | hp
    · exact Or.inl ⟨Or.inl ⟨hS0par j,
        parallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)⟩,
        Or.inr ⟨hS0cop j,
          parallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)⟩⟩
    · exact Or.inr ⟨Or.inr ⟨hS0cop j,
        coParallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)⟩,
        Or.inl ⟨hS0par j,
          coParallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)⟩⟩
  by_cases hboth : ∃ j : Fin n,
      (offVerts G (T j) (W true)).Nonempty ∧ (offVerts G (T j) (W false)).Nonempty
  · obtain ⟨j, h1, h2⟩ := hboth
    exact Or.inl (fun i => ⟨(j, true), (j, false), by simp, h1, h2, htwoOff i j⟩)
  -- Otherwise each antistrip has a single offspring, which is the antistrip itself.
  have hone : ∀ j : Fin n, ∃ b : Bool, offVerts G (T j) (W b) = stripVertices (T j) := by
    intro j
    rcases Set.eq_empty_or_nonempty (offVerts G (T j) (W true)) with he | hne
    · exact ⟨false, by rw [← hcov j, he, Set.empty_union]⟩
    · have hemp : offVerts G (T j) (W false) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp (fun hne2 => hboth ⟨j, hne, hne2⟩)
      exact ⟨true, by rw [← hcov j, hemp, Set.union_empty]⟩
  choose bb hbb using hone
  have heq : ∀ j, offspring G (T j) (W (bb j)) = T j := fun j => offspring_eq_self _ _ (hbb j)
  have hS0Tpar : ∀ j, bb j = true → ParallelStripAntistrip G (newStrip R r s) (T j) := by
    intro j hb
    have h : ParallelStripAntistrip G (newStrip R r s) (offspring G (T j) (W (bb j))) := by
      rw [hb]; exact hS0par j
    rw [heq j] at h; exact h
  have hS0Tcop : ∀ j, bb j = false → CoParallel G (newStrip R r s) (T j) := by
    intro j hb
    have h : CoParallel G (newStrip R r s) (offspring G (T j) (W (bb j))) := by
      rw [hb]; exact hS0cop j
    rw [heq j] at h; exact h
  have hr0 : r ∈ (newStrip R r s).1 := rfl
  have hs0 : s ∈ (newStrip R r s).2.2 := rfl
  -- `S₀` and `Sᵢ` agree on the single offspring of `Tⱼ`.
  have hAgr : Fin m → Fin n → Prop :=
    fun i j => (bb j = true) ↔ ParallelStripAntistrip G (S i) (T j)
  -- If they agree on every antistrip, `f₁` copies the end of `Sᵢ` in `Aᵢ`.
  have hmergeAgree : ∀ i : Fin m,
      (∀ j : Fin n, (bb j = true ↔ ParallelStripAntistrip G (S i) (T j))) →
      ∃ a b : V, ((a ∈ (S i).1 ∧ b ∈ (S i).2.2) ∨ (a ∈ (S i).2.2 ∧ b ∈ (S i).1)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj r w ↔ G.Adj a w)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj s w ↔ G.Adj b w)) := by
    intro i hag
    obtain ⟨a, ha⟩ := fst_nonempty (hL.1 i)
    obtain ⟨b, hb⟩ := thd_nonempty (hL.1 i)
    have hstep : ∀ j : Fin n,
        (ParallelStripAntistrip G (newStrip R r s) (T j) ∧
          ParallelStripAntistrip G (S i) (T j)) ∨
        (CoParallel G (newStrip R r s) (T j) ∧ CoParallel G (S i) (T j)) := by
      intro j
      rcases Bool.eq_false_or_eq_true (bb j) with hbj | hbj
      · exact Or.inl ⟨hS0Tpar j hbj, (hag j).mp hbj⟩
      · have hnp : ¬ ParallelStripAntistrip G (S i) (T j) := by
          intro h
          have h' := (hag j).mpr h
          rw [hbj] at h'
          exact Bool.noConfusion h'
        exact Or.inr ⟨hS0Tcop j hbj, (hSipc i j).resolve_left hnp⟩
    refine ⟨a, b, Or.inl ⟨ha, hb⟩, ?_, ?_⟩
    · intro j w hw
      rcases hstep j with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [adjA_par h1 hr0 hw, adjA_par h2 ha hw]
      · rw [adjA_cop h1 hr0 hw, adjA_cop h2 ha hw]
    · intro j w hw
      rcases hstep j with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [adjB_par h1 hs0 hw, adjB_par h2 hb hw]
      · rw [adjB_cop h1 hs0 hw, adjB_cop h2 hb hw]
  -- If they disagree on every antistrip, `f₁` copies the end of `Sᵢ` in `Bᵢ` instead.
  have hmergeDis : ∀ i : Fin m,
      (∀ j : Fin n, ¬ (bb j = true ↔ ParallelStripAntistrip G (S i) (T j))) →
      ∃ a b : V, ((a ∈ (S i).1 ∧ b ∈ (S i).2.2) ∨ (a ∈ (S i).2.2 ∧ b ∈ (S i).1)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj r w ↔ G.Adj a w)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj s w ↔ G.Adj b w)) := by
    intro i hd
    obtain ⟨a, ha⟩ := fst_nonempty (hL.1 i)
    obtain ⟨b, hb⟩ := thd_nonempty (hL.1 i)
    have hstep : ∀ j : Fin n,
        (ParallelStripAntistrip G (newStrip R r s) (T j) ∧ CoParallel G (S i) (T j)) ∨
        (CoParallel G (newStrip R r s) (T j) ∧ ParallelStripAntistrip G (S i) (T j)) := by
      intro j
      rcases Bool.eq_false_or_eq_true (bb j) with hbj | hbj
      · have hnp : ¬ ParallelStripAntistrip G (S i) (T j) :=
          fun h => hd j ⟨fun _ => h, fun _ => hbj⟩
        exact Or.inl ⟨hS0Tpar j hbj, (hSipc i j).resolve_left hnp⟩
      · have hp : ParallelStripAntistrip G (S i) (T j) := by
          by_contra hcon
          exact hd j ⟨fun h => absurd (hbj.symm.trans h) (by simp), fun h => absurd h hcon⟩
        exact Or.inr ⟨hS0Tcop j hbj, hp⟩
    refine ⟨b, a, Or.inr ⟨hb, ha⟩, ?_, ?_⟩
    · intro j w hw
      rcases hstep j with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [adjA_par h1 hr0 hw, adjB_cop h2 hb hw]
      · rw [adjA_cop h1 hr0 hw, adjB_par h2 hb hw]
    · intro j w hw
      rcases hstep j with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [adjB_par h1 hs0 hw, adjA_cop h2 ha hw]
      · rw [adjB_cop h1 hs0 hw, adjA_par h2 ha hw]
  by_cases hm : ∃ (i : Fin m) (a b : V),
      ((a ∈ (S i).1 ∧ b ∈ (S i).2.2) ∨ (a ∈ (S i).2.2 ∧ b ∈ (S i).1)) ∧
      (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj r w ↔ G.Adj a w)) ∧
      (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj s w ↔ G.Adj b w))
  · exact Or.inr hm
  refine Or.inl (fun i => ?_)
  have hnotall : ¬ (∀ j : Fin n, (bb j = true ↔ ParallelStripAntistrip G (S i) (T j))) := by
    intro hall
    obtain ⟨a, b, h⟩ := hmergeAgree i hall
    exact hm ⟨i, a, b, h⟩
  have hnotnone : ¬ (∀ j : Fin n, ¬ (bb j = true ↔ ParallelStripAntistrip G (S i) (T j))) := by
    intro hall
    obtain ⟨a, b, h⟩ := hmergeDis i hall
    exact hm ⟨i, a, b, h⟩
  obtain ⟨j₂, hj₂⟩ := not_forall.mp hnotall
  obtain ⟨j₁, hj₁'⟩ := not_forall.mp hnotnone
  have hj₁ : (bb j₁ = true ↔ ParallelStripAntistrip G (S i) (T j₁)) := not_not.mp hj₁'
  have hjne : j₁ ≠ j₂ := by rintro rfl; exact hj₂ hj₁
  refine ⟨(j₁, bb j₁), (j₂, bb j₂), fun h => hjne (congrArg Prod.fst h), ?_, ?_, ?_⟩
  · rw [hbb j₁]; exact stripVertices_nonempty (G := Gᶜ) (hL.2.1 j₁)
  · rw [hbb j₂]; exact stripVertices_nonempty (G := Gᶜ) (hL.2.1 j₂)
  · show IsTwist G (newStrip R r s) (S i) (offspring G (T j₁) (W (bb j₁)))
      (offspring G (T j₂) (W (bb j₂)))
    rw [heq j₁, heq j₂]
    have hag : AgreeOn G (newStrip R r s) (S i) (T j₁) := by
      rcases Bool.eq_false_or_eq_true (bb j₁) with hbj | hbj
      · exact Or.inl ⟨hS0Tpar j₁ hbj, hj₁.mp hbj⟩
      · have hnp : ¬ ParallelStripAntistrip G (S i) (T j₁) := by
          intro h
          have h' := hj₁.mpr h
          rw [hbj] at h'
          exact Bool.noConfusion h'
        exact Or.inr ⟨hS0Tcop j₁ hbj, (hSipc i j₁).resolve_left hnp⟩
    have hdis : (ParallelStripAntistrip G (newStrip R r s) (T j₂) ∧
        CoParallel G (S i) (T j₂)) ∨
        (CoParallel G (newStrip R r s) (T j₂) ∧ ParallelStripAntistrip G (S i) (T j₂)) := by
      rcases Bool.eq_false_or_eq_true (bb j₂) with hbj | hbj
      · have hnp : ¬ ParallelStripAntistrip G (S i) (T j₂) :=
          fun h => hj₂ ⟨fun _ => h, fun _ => hbj⟩
        exact Or.inl ⟨hS0Tpar j₂ hbj, (hSipc i j₂).resolve_left hnp⟩
      · have hp : ParallelStripAntistrip G (S i) (T j₂) := by
          by_contra hcon
          exact hj₂ ⟨fun h => absurd (hbj.symm.trans h) (by simp), fun h => absurd h hcon⟩
        exact Or.inr ⟨hS0Tcop j₂ hbj, hp⟩
    exact Or.inl ⟨hag, hdis⟩

end Workspace.ProofLemmas.Thm95OffspringGapTwist
