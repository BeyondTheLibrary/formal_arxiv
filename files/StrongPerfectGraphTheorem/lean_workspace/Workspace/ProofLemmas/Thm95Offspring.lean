import Workspace.ProofLemmas.Thm95Claim1Propagate
import Workspace.ProofLemmas.Thm95OffspringGaps
import Workspace.ProofLemmas.Thm95OffspringParallel
import Workspace.ProofLemmas.Thm95OffspringMerge

/-!
# The offspring of the antistrips, and the new striation of 9.5(1)

PAPER (9.5(1), printed pp. 52–53).  After the five consequences of 9.3.3 the proof builds a
strictly larger striation and contradicts maximality.  This file records the consequences in
the form the construction uses, states the construction itself, and assembles the two.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95Offspring

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95GapBasics
open Workspace.ProofLemmas.Thm95OffspringDefs
open Workspace.ProofLemmas.Thm95OffspringFacts
open Workspace.ProofLemmas.Thm95OffspringParallel
open Workspace.ProofLemmas.Thm95OffspringGaps

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The offspring of `T p.1` belonging to the side `p.2` (`true` = the neighbours of `f₁`,
`false` = the neighbours of `f_k`).  This is the indexing the paper's *"the set of offspring of
`T₁, …, T_n`"* needs: a parent together with a side. -/
def offAt (Gx : SimpleGraph V) {n : ℕ} (T : Fin n → Set V × Set V × Set V) (r s : V)
    (p : Fin n × Bool) : Set V × Set V × Set V :=
  offspring Gx (T p.1) (side Gx r s p.2)

/-- The vertex set of `offAt Gx T r s p`, that is the paper's `Mⱼ` or `Nⱼ`. -/
def offVertsAt (Gx : SimpleGraph V) {n : ℕ} (T : Fin n → Set V × Set V × Set V) (r s : V)
    (p : Fin n × Bool) : Set V :=
  offVerts Gx (T p.1) (side Gx r s p.2)

/-- The new family of strips: the paper's `S₀, S₁, …, S_m`. -/
def stripsWithNew {m : ℕ} (S : Fin m → Set V × Set V × Set V) (R : List V) (r s : V) :
    Option (Fin m) → Set V × Set V × Set V
  | none => newStrip R r s
  | some i => S i

/-- **Labelled gap: the offspring construction of 9.5(1).**

PAPER (printed pp. 52–53): *"For the moment fix `j` with `1 ≤ j ≤ n`.  Every `Tⱼ`-antirung has
one end in `U` and the other in `V`; let `Mⱼ` be the union of the vertex sets of all
`Tⱼ`-antirungs `xⱼ-Qⱼ-yⱼ` such that `xⱼ ∈ U`, and `Nⱼ` the union of all those with `xⱼ ∈ V`.
Since there is no `Tⱼ`-antirung with both ends in `Mⱼ` or both ends in `Nⱼ`, it follows that
`Mⱼ ∩ Nⱼ = ∅`, and there are no nonedges between `Mⱼ` and `Nⱼ` except possibly between
`Mⱼ ∩ Xⱼ` and `Nⱼ ∩ Xⱼ`, or between `Mⱼ ∩ Yⱼ` and `Nⱼ ∩ Yⱼ`.  Suppose there is such a nonedge;
and choose `Tⱼ`-antirungs `xⱼ-Qⱼ-yⱼ`, `x'ⱼ-Q'ⱼ-y'ⱼ` where `xⱼ ∈ U` is nonadjacent to
`x'ⱼ ∈ V`, say.  Now `xⱼ, x'ⱼ` have a common neighbour `d₁ ∈ A₁ ∪ B₁`, and then
`d₁-xⱼ-f₁-⋯-f_k-x'ⱼ-d₁` is an odd hole.  This proves that `Mⱼ` is complete to `Nⱼ`.  Now if
`Mⱼ` is nonempty, then `(Mⱼ ∩ Xⱼ, Mⱼ ∩ Zⱼ, Mⱼ ∩ Yⱼ)` is an antistrip, and similarly if `Nⱼ` is
nonempty it also induces an antistrip.  We call these the offspring of `Tⱼ`. …  Also, there is
a new strip `S₀ = ({f₁}, {f₂,…,f_{k-1}}, {f_k})`. … It follows from these observations that the
set of strips `S₀, …, S_m`, together with the set of offspring of `T₁, …, T_n`, forms a new
striation."*

The hypotheses below are exactly the five consequences the paragraph is allowed to use:
`hcover` is the second (*"every vertex of `Tⱼ` is in `X`"*), `hint` the third, `hZ` the fourth,
`hXY` the fifth, and `hnoS` is the standing assumption of claim (1) that `F` has no neighbour
on any strip.  `U` is `{z | Gx.Adj r z}` and `V` is `{z | Gx.Adj s z}`; `hcover` and `hXY`
together are the paper's *"every vertex in `X₁ ∪ Y₁ ⋯ ∪ X_n ∪ Y_n` is adjacent to exactly one
of `f₁, f_k`"*.

What remains unproved here is the construction itself: the offspring, the new strip, the three
bullets about twists, and the verification that the resulting family is a striation. -/
theorem offspring_striation {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx) (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ)
    {R : List V} {r s : V}
    (hR : IsPathFrom Gx R r s) (hodd : Odd (pathLength R)) (hRset : {v : V | v ∈ R} = F)
    (hrs : r ≠ s)
    (hnoS : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    (hcover : ∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) → (Gx.Adj r z ∨ Gx.Adj s z))
    (hZ : ∀ (k : Fin n) (z : V), z ∈ (T k).2.1 → (Gx.Adj r z ∧ Gx.Adj s z))
    (hXY : ∀ (k : Fin n) (z : V), z ∈ (T k).1 ∪ (T k).2.2 → ¬ (Gx.Adj r z ∧ Gx.Adj s z))
    (hint : ∀ k : Fin n,
      Anticomplete Gx {v : V | v ∈ SPGT.interior R} (stripVertices (T k))) :
    ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
      (T' : Fin n' → Set V × Set V × Set V), IsStriation Gx S' T' ∧
      striationVertices S' T' = striationVertices S T ∪ F := by
  classical
  -- Componentwise membership in the vertex set of an antistrip.
  have hXsub : ∀ Tx : Set V × Set V × Set V, Tx.1 ⊆ stripVertices Tx := by
    rintro ⟨X, Z, Y⟩ z hz; exact Or.inl (Or.inl hz)
  have hYsub : ∀ Tx : Set V × Set V × Set V, Tx.2.2 ⊆ stripVertices Tx := by
    rintro ⟨X, Z, Y⟩ z hz; exact Or.inl (Or.inr hz)
  have hTanti : ∀ j, IsAntistrip Gx (T j) := hL.2.1
  have hSsub : ∀ (i : Fin m) (v : V), v ∈ stripVertices (S i) → v ∈ striationVertices S T :=
    fun i _ hv => StriationCompl.stripVertices_S_subset S T i hv
  have hTsub : ∀ (j : Fin n) (v : V), v ∈ stripVertices (T j) → v ∈ striationVertices S T :=
    fun j _ hv => StriationCompl.stripVertices_T_subset S T j hv
  have hVnew : stripVertices (newStrip R r s) = F := (stripVertices_newStrip hR).trans hRset
  have hOVsub : ∀ p : Fin n × Bool, offVertsAt Gx T r s p ⊆ stripVertices (T p.1) :=
    fun p => offVerts_subset _ _
  have hOVeq : ∀ p : Fin n × Bool, stripVertices (offAt Gx T r s p) = offVertsAt Gx T r s p :=
    fun p => stripVertices_offspring _ _
  -- PAPER: "Every Tⱼ-antirung has one end in U and the other in V."
  have hsplit : ∀ (j : Fin n) (Q : List V) (x y : V), IsSRung Gxᶜ (T j) Q →
      IsPathFrom Gxᶜ Q x y → (Gx.Adj r x ∧ Gx.Adj s y) ∨ (Gx.Adj s x ∧ Gx.Adj r y) :=
    fun j Q x y hQ hp => Thm95OffspringGaps.antirung_ends_split hG hL hFsub hR hodd hRset hrs
      hnoS hcover hZ hXY hint j hQ hp
  -- The two offspring of `T j` cover `V(T j)`.
  have hcov : ∀ j : Fin n,
      offVertsAt Gx T r s (j, true) ∪ offVertsAt Gx T r s (j, false) = stripVertices (T j) := by
    intro j
    exact offVerts_cover (hTanti j) (fun z hz => hcover j z (hXsub (T j) hz))
  -- Every antistrip has at least one nonempty offspring.
  have hsome : ∀ j : Fin n, ∃ b : Bool, (offVertsAt Gx T r s (j, b)).Nonempty := by
    intro j
    obtain ⟨Q, hQ⟩ := Thm95GapBasics.exists_rung (hTanti j)
    obtain ⟨a, b, hpath, ha, -, -, -, -⟩ := id hQ
    rcases hcover j a (hXsub (T j) ha) with h | h
    · exact ⟨true, a, Q, hQ, PathBasics.head_mem hpath.2.1, a, hpath.2.1, h⟩
    · exact ⟨false, a, Q, hQ, PathBasics.head_mem hpath.2.1, a, hpath.2.1, h⟩
  -- PAPER, first bullet: S₀ is parallel with the U-offspring and co-parallel with the
  -- V-offspring.
  have hS0par : ∀ j : Fin n,
      ParallelStripAntistrip Gx (newStrip R r s) (offAt Gx T r s (j, true)) :=
    fun j => parallel_newStrip (hTanti j) (hsplit j) (hZ j) (hXY j) (hint j)
  have hS0cop : ∀ j : Fin n, CoParallel Gx (newStrip R r s) (offAt Gx T r s (j, false)) :=
    fun j => coParallel_newStrip (hTanti j) (hsplit j) (hZ j) (hXY j) (hint j)
  have hS0pc : ∀ p : Fin n × Bool,
      ParallelStripAntistrip Gx (newStrip R r s) (offAt Gx T r s p) ∨
        CoParallel Gx (newStrip R r s) (offAt Gx T r s p) := by
    rintro ⟨j, b⟩
    cases b
    · exact Or.inr (hS0cop j)
    · exact Or.inl (hS0par j)
  -- Each old strip keeps its relation to every offspring.
  have hSipc : ∀ (i : Fin m) (p : Fin n × Bool),
      ParallelStripAntistrip Gx (S i) (offAt Gx T r s p) ∨
        CoParallel Gx (S i) (offAt Gx T r s p) :=
    fun i p => parallel_offspring _ (hL.2.2.2.2.2.2.2.2.2.2.2.1 i p.1)
  rcases Thm95OffspringGaps.twist_or_merge hG hL hFsub hR hodd hRset hrs hnoS hcover hZ hXY
      hint with hbullet | hmerge
  · -- The offspring construction.
    obtain ⟨hm2, hn2⟩ : 2 ≤ m ∧ 2 ≤ n := ⟨hL.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.1⟩
    let i₀ : Fin m := ⟨0, by omega⟩
    let j₀ : Fin n := ⟨0, by omega⟩
    let j₁ : Fin n := ⟨1, by omega⟩
    have hj₀₁ : j₀ ≠ j₁ := by
      intro h
      exact absurd (congrArg Fin.val h) (by simp [j₀, j₁])
    obtain ⟨b₀, hb₀⟩ := hsome j₀
    obtain ⟨b₁, hb₁⟩ := hsome j₁
    -- Completeness between offspring of different parents.
    have hcompl_diff : ∀ p q : Fin n × Bool, p.1 ≠ q.1 →
        Complete Gx (offVertsAt Gx T r s p) (offVertsAt Gx T r s q) := by
      intro p q hpq
      have key : ∀ (j j' : Fin n) (c c' : Bool), j < j' →
          Complete Gx (offVertsAt Gx T r s (j, c)) (offVertsAt Gx T r s (j', c')) := by
        intro j j' c c' h x hx y hy
        exact hL.2.2.2.2.2.2.2.2.2.2.1 j j' h x (hOVsub _ hx) y (hOVsub _ hy)
      rcases lt_or_gt_of_ne hpq with h | h
      · simpa using key p.1 q.1 p.2 q.2 h
      · exact Thm95OffspringGeneric.complete_symm (by simpa using key q.1 p.1 q.2 p.2 h)
    -- Disjointness of the two offspring of one parent, and of offspring of different parents.
    have hdisj_off : ∀ p q : Fin n × Bool, p ≠ q →
        Disjoint (offVertsAt Gx T r s p) (offVertsAt Gx T r s q) := by
      rintro ⟨j, b⟩ ⟨j', b'⟩ hpq
      by_cases hjj : j = j'
      · subst j'
        have hbb : b ≠ b' := by
          intro h; exact hpq (by rw [h])
        have hgap := Thm95OffspringGaps.offVerts_disjoint hG hL hFsub hR hodd hRset hrs hnoS
          hcover hZ hXY hint j
        cases b <;> cases b'
        · exact absurd rfl hbb
        · exact hgap.symm
        · exact hgap
        · exact absurd rfl hbb
      · exact Set.disjoint_of_subset (hOVsub (j, b)) (hOVsub (j', b'))
          (hL.2.2.2.1 j j' hjj)
    -- Assemble the two families and re-index them.
    obtain ⟨m', n', S', T', hstr, heq⟩ :=
      Thm95OffspringGeneric.mk_striation (G := Gx)
        (ι := Option (Fin m)) (κ := {p : Fin n × Bool // (offVertsAt Gx T r s p).Nonempty})
        (stripsWithNew S R r s) (fun p => offAt Gx T r s p.1)
        (by
          rintro (_ | i)
          · exact newStrip_isStrip hR hrs
          · exact hL.1 i)
        (fun p => offspring_isAntistrip (hTanti p.1.1) _ p.2)
        (by
          rintro (_ | i) (_ | i') hne
          · exact absurd rfl hne
          · show Disjoint (stripVertices (newStrip R r s)) (stripVertices (S i'))
            rw [hVnew]
            exact Set.disjoint_left.mpr (fun v hv hv' => hFsub hv (hSsub i' _ hv'))
          · show Disjoint (stripVertices (S i)) (stripVertices (newStrip R r s))
            rw [hVnew]
            exact Set.disjoint_right.mpr (fun v hv hv' => hFsub hv (hSsub i _ hv'))
          · exact hL.2.2.1 i i' (fun h => hne (by rw [h])))
        (by
          intro p q hpq
          rw [hOVeq, hOVeq]
          exact hdisj_off p.1 q.1 (fun h => hpq (Subtype.ext h)))
        (by
          rintro (_ | i) p
          · show Disjoint (stripVertices (newStrip R r s)) (stripVertices (offAt Gx T r s p.1))
            rw [hVnew, hOVeq]
            exact Set.disjoint_left.mpr
              (fun v hv hv' => hFsub hv (hTsub p.1.1 _ (hOVsub p.1 hv')))
          · show Disjoint (stripVertices (S i)) (stripVertices (offAt Gx T r s p.1))
            rw [hOVeq]
            exact Set.disjoint_of_subset (fun _ h => h) (hOVsub p.1)
              (hL.2.2.2.2.1 i p.1.1))
        (by
          rintro (_ | i) q hq
          · refine odd_rungs_two hG (newStrip_isStrip hR hrs)
              (offspring_isAntistrip (hTanti j₀) _ hb₀)
              (offspring_isAntistrip (hTanti j₁) _ hb₁) ?_ ?_ ?_
              (hS0pc (j₀, b₀)) (hS0pc (j₁, b₁)) hq
            · rw [hVnew, stripVertices_offspring]
              exact Set.disjoint_left.mpr
                (fun v hv hv' => hFsub hv (hTsub j₀ _ (hOVsub (j₀, b₀) hv')))
            · rw [hVnew, stripVertices_offspring]
              exact Set.disjoint_left.mpr
                (fun v hv hv' => hFsub hv (hTsub j₁ _ (hOVsub (j₁, b₁) hv')))
            · rw [stripVertices_offspring, stripVertices_offspring]
              exact hcompl_diff (j₀, b₀) (j₁, b₁) hj₀₁
          · exact hL.2.2.2.2.2.1 i q hq)
        (fun p q hq => hL.2.2.2.2.2.2.1 p.1.1 q (srung_offspring hq))
        ⟨none, some i₀, by simp⟩
        ⟨⟨(j₀, b₀), hb₀⟩, ⟨(j₁, b₁), hb₁⟩, by
          intro h
          exact hj₀₁ (congrArg (fun x => (Subtype.val x).1) h)⟩
        (by
          rintro (_ | i) (_ | i') hne
          · exact absurd rfl hne
          · show Anticomplete Gx (stripVertices (newStrip R r s)) (stripVertices (S i'))
            rw [hVnew]; exact hnoS i'
          · show Anticomplete Gx (stripVertices (S i)) (stripVertices (newStrip R r s))
            rw [hVnew]
            exact Thm95OffspringGeneric.anticomplete_symm (hnoS i)
          · have hii : i ≠ i' := fun h => hne (by rw [h])
            rcases lt_or_gt_of_ne hii with h | h
            · exact hL.2.2.2.2.2.2.2.2.2.1 i i' h
            · exact Thm95OffspringGeneric.anticomplete_symm
                (hL.2.2.2.2.2.2.2.2.2.1 i' i h))
        (by
          intro p q hpq
          rw [hOVeq, hOVeq]
          obtain ⟨⟨j, b⟩, hpne⟩ := p
          obtain ⟨⟨j', b'⟩, hqne⟩ := q
          by_cases hjj : j = j'
          · subst j'
            have hbb : b ≠ b' := fun h => hpq (Subtype.ext (congrArg (Prod.mk j) h))
            have hgap := Thm95OffspringGaps.offVerts_complete hG hL hFsub hR hodd hRset hrs
              hnoS hcover hZ hXY hint j
            cases b <;> cases b'
            · exact absurd rfl hbb
            · exact Thm95OffspringGeneric.complete_symm hgap
            · exact hgap
            · exact absurd rfl hbb
          · exact hcompl_diff (j, b) (j', b') hjj)
        (by
          rintro (_ | i) p
          · exact hS0pc p.1
          · exact hSipc i p.1)
        (by
          rintro (_ | i) (_ | i') hne
          · exact absurd rfl hne
          · obtain ⟨p, q, hpq, hpne, hqne, htw⟩ := hbullet i'
            exact ⟨⟨p, hpne⟩, ⟨q, hqne⟩, fun h => hpq (congrArg Subtype.val h), htw⟩
          · obtain ⟨p, q, hpq, hpne, hqne, htw⟩ := hbullet i
            exact ⟨⟨p, hpne⟩, ⟨q, hqne⟩, fun h => hpq (congrArg Subtype.val h),
              Thm95OffspringGeneric.isTwist_swap_S htw⟩
          · have hii : i ≠ i' := fun h => hne (by rw [h])
            have key : ∀ k k' : Fin m, k < k' → ∃ p q : {p : Fin n × Bool //
                (offVertsAt Gx T r s p).Nonempty}, p ≠ q ∧
                IsTwist Gx (S k) (S k') (offAt Gx T r s p.1) (offAt Gx T r s q.1) := by
              intro k k' h
              obtain ⟨j, j', hjj, htw⟩ := hL.2.2.2.2.2.2.2.2.2.2.2.2.1 k k' h
              obtain ⟨c, hc⟩ := hsome j
              obtain ⟨c', hc'⟩ := hsome j'
              exact ⟨⟨(j, c), hc⟩, ⟨(j', c'), hc'⟩,
                (fun hcon => hjj (congrArg (fun x => (Subtype.val x).1) hcon)),
                isTwist_offspring _ _ htw⟩
            rcases lt_or_gt_of_ne hii with h | h
            · exact key i i' h
            · obtain ⟨p, q, hpq, htw⟩ := key i' i h
              exact ⟨p, q, hpq, Thm95OffspringGeneric.isTwist_swap_S htw⟩)
        (by
          intro p q hpq
          obtain ⟨⟨j, b⟩, hpne⟩ := p
          obtain ⟨⟨j', b'⟩, hqne⟩ := q
          by_cases hjj : j = j'
          · -- The two offspring of one parent: they disagree on `S₀`, and agree on every `Sᵢ`.
            subst j'
            have hbb : b ≠ b' := fun h => hpq (Subtype.ext (congrArg (Prod.mk j) h))
            have hone : ∀ k : Fin n,
                IsTwist Gx (newStrip R r s) (S i₀) (offAt Gx T r s (k, true))
                  (offAt Gx T r s (k, false)) := by
              intro k
              rcases hL.2.2.2.2.2.2.2.2.2.2.2.1 i₀ k with hp | hp
              · have h1 : ParallelStripAntistrip Gx (S i₀) (offAt Gx T r s (k, true)) :=
                  parallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)
                have h2 : ParallelStripAntistrip Gx (S i₀) (offAt Gx T r s (k, false)) :=
                  parallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)
                exact Or.inl ⟨Or.inl ⟨hS0par k, h1⟩, Or.inr ⟨hS0cop k, h2⟩⟩
              · have h1 : CoParallel Gx (S i₀) (offAt Gx T r s (k, true)) :=
                  coParallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)
                have h2 : CoParallel Gx (S i₀) (offAt Gx T r s (k, false)) :=
                  coParallel_mono hp (fun _ h => h.2) (fun _ h => h.2) (fun _ h => h.2)
                exact Or.inr ⟨Or.inr ⟨hS0cop k, h2⟩, Or.inl ⟨hS0par k, h1⟩⟩
            have hne0 : (none : Option (Fin m)) ≠ some i₀ := by simp
            cases b <;> cases b'
            · exact absurd rfl hbb
            · exact ⟨none, some i₀, hne0,
                Thm95OffspringGeneric.isTwist_swap_T (hone j)⟩
            · exact ⟨none, some i₀, hne0, hone j⟩
            · exact absurd rfl hbb
          · have key : ∀ k k' : Fin n, k < k' → ∀ c c' : Bool,
                ∃ o o' : Option (Fin m), o ≠ o' ∧
                  IsTwist Gx (stripsWithNew S R r s o) (stripsWithNew S R r s o')
                    (offAt Gx T r s (k, c)) (offAt Gx T r s (k', c')) := by
              intro k k' h c c'
              obtain ⟨i, i', hii, htw⟩ := hL.2.2.2.2.2.2.2.2.2.2.2.2.2 k k' h
              exact ⟨some i, some i', by simp [hii], isTwist_offspring _ _ htw⟩
            rcases lt_or_gt_of_ne hjj with h | h
            · exact key j j' h b b'
            · obtain ⟨o, o', hoo, htw⟩ := key j' j h b' b
              exact ⟨o, o', hoo, Thm95OffspringGeneric.isTwist_swap_T htw⟩)
    refine ⟨m', n', S', T', hstr, heq.trans ?_⟩
    -- The new striation lives on `V(L) ∪ F`.
    refine Set.ext (fun v => ⟨?_, ?_⟩)
    · rintro (hv | hv)
      · obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hv
        cases o with
        | none => exact Or.inr (hVnew ▸ ho)
        | some i => exact Or.inl (Or.inl (Set.mem_iUnion_of_mem i ho))
      · obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hv
        rw [hOVeq] at hp
        exact Or.inl (Or.inr (Set.mem_iUnion_of_mem p.1.1 (hOVsub p.1 hp)))
    · rintro ((hv | hv) | hv)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
        exact Or.inl (Set.mem_iUnion_of_mem (some i) hi)
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
        rw [← hcov j] at hj
        rcases hj with hj | hj
        · exact Or.inr (Set.mem_iUnion_of_mem (⟨(j, true), ⟨v, hj⟩⟩ :
            {p : Fin n × Bool // (offVertsAt Gx T r s p).Nonempty}) (by rw [hOVeq]; exact hj))
        · exact Or.inr (Set.mem_iUnion_of_mem (⟨(j, false), ⟨v, hj⟩⟩ :
            {p : Fin n × Bool // (offVertsAt Gx T r s p).Nonempty}) (by rw [hOVeq]; exact hj))
      · refine Or.inl (Set.mem_iUnion_of_mem none ?_)
        show v ∈ stripVertices (newStrip R r s)
        rw [hVnew]; exact hv
  · -- PAPER: "we could add f₁ to Aᵢ, {f₂,…,f_{k-1}} to Cᵢ, and f_k to Bᵢ".
    obtain ⟨i, a, b, hab, hra, hsb⟩ := hmerge
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Thm95OffspringMerge.merge_striation hG hL hFsub i hnoS hR hrs hRset ha hb
        hra hsb hint
    · refine Thm95OffspringMerge.merge_striation hG hL hFsub i hnoS
        (PathBasics.isPathFrom_reverse hR) (Ne.symm hrs) ?_ hb ha hsb hra ?_
      · rw [← hRset]
        exact Set.ext (fun v => by simp)
      · intro j x hx
        exact hint j x (PathBasics.mem_interior_reverse.mp hx)

/-- **PAPER (9.5(1)):** the whole of claim (1) up to the maximality contradiction: from an
antirung all of whose vertices are attachments of `F`, a striation on `V(L) ∪ F`. -/
theorem claim1_enlargement {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx)
    (hnoenl : ¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J'))
    (hnoover : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gx.induce K'),
      IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ)
    (hnoovercompl : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gxᶜ.induce K'),
      IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ)
    (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ) (hFconn : ConnectedSet Gx F)
    (hminEq : ∀ F' : Set V, F' ⊆ F → ConnectedSet Gx F' →
      ¬ LocalForStriation Gx S T (attachments Gx F' (striationVertices S T)) → F' = F)
    (hno : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    {j : Fin n} {Q : List V} (hQ : IsSRung Gxᶜ (T j) Q)
    (hQall : ∀ v ∈ Q, ∃ f ∈ F, Gx.Adj v f) :
    ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
      (T' : Fin n' → Set V × Set V × Set V), IsStriation Gx S' T' ∧
      striationVertices S' T' = striationVertices S T ∪ F := by
  obtain ⟨R, r, s, hR, hodd, hRset, hrs, hmatch, hint⟩ :=
    Thm95Claim1Propagate.claim1_facts hG hnoenl hnoover hnoovercompl hL hFsub hFconn hminEq
      hno hQ hQall
  have hZsub : ∀ (Tx : Set V × Set V × Set V) (z : V), z ∈ Tx.2.1 → z ∈ stripVertices Tx := by
    intro Tx z hz
    obtain ⟨X, Z, Y⟩ := Tx
    exact Set.mem_union_right _ hz
  have hXYsub : ∀ (Tx : Set V × Set V × Set V) (z : V), z ∈ Tx.1 ∪ Tx.2.2 →
      z ∈ stripVertices Tx := by
    intro Tx z hz
    obtain ⟨X, Z, Y⟩ := Tx
    rcases hz with hz | hz
    · exact Set.mem_union_left _ (Set.mem_union_left _ hz)
    · exact Set.mem_union_left _ (Set.mem_union_right _ hz)
  refine offspring_striation hG hL hFsub hR hodd hRset hrs hno ?_ ?_ ?_ hint
  · intro k z hz
    obtain ⟨Sx, a, b, hpar, ha, hb, h1, h2⟩ := hmatch k z hz
    rcases cover_strip hpar ha hb z hz with h | h
    · exact Or.inl (h1.mpr h)
    · exact Or.inr (h2.mpr h)
  · intro k z hz
    obtain ⟨Sx, a, b, hpar, ha, hb, h1, h2⟩ := hmatch k z (hZsub (T k) z hz)
    obtain ⟨hzz, -⟩ := end_pattern hpar ha hb
    exact ⟨h1.mpr (hzz z hz).1, h2.mpr (hzz z hz).2⟩
  · intro k z hz
    obtain ⟨Sx, a, b, hpar, ha, hb, h1, h2⟩ := hmatch k z (hXYsub (T k) z hz)
    obtain ⟨-, hxy⟩ := end_pattern hpar ha hb
    exact fun hboth => hxy z hz ⟨h1.mp hboth.1, h2.mp hboth.2⟩

end Workspace.ProofLemmas.Thm95Offspring
