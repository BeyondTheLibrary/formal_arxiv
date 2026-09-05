import Workspace.ProofLemmas.Thm175Optimal
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
The antipath data used in claims (4) and (5) of 17.5.  This interface uses
only the earlier optimal-counterexample module, so that the numbered claims
can import its proofs without an import cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm175Optimal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- The antipath blocks and first missed vertex chosen just before (4).
PAPER: "So `x₁-⋯-x_s-y₁-⋯-y_{t₀}-p₁` is an antipath."
The integer `t₀` is zero-based. -/
structure Setup (c : Counterexample G z) where
  qX : List V
  qY : List V
  x₁ : V
  yₜ : V
  hXlong : 1 < qX.length
  hYlong : 1 < qY.length
  hxhead : qX.head? = some x₁
  hylast : qY.getLast? = some yₜ
  hanti : IsAntipathFrom G (qX ++ qY) x₁ yₜ
  hXverts : ∀ x : V, x ∈ qX ↔ x ∈ c.X
  hYverts : ∀ y : V, y ∈ qY ↔ y ∈ c.Y
  t₀ : ℕ
  ht₀ : t₀ < qY.length
  hmiss : ¬ G.Adj c.core.p₁ (qY[t₀]'ht₀)
  hbefore : ∀ j (hj : j < t₀),
    G.Adj c.core.p₁ (qY[j]'(lt_trans hj ht₀))

/-- The set `W=(X\{x₁})∪{y₁,…,y_{t₀-1}}` in the printed proof. -/
def wSet (s : Setup c) : Set V :=
  (c.X \ {s.x₁}) ∪ {y : V | y ∈ s.qY.take s.t₀}

/-- The complete edges of a list, each counted once as an unordered pair. -/
def edges (G : SimpleGraph V) (A : Set V) (p : List V) : Set (Sym2 V) :=
  {e | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G A u v}

theorem x₁_mem (s : Setup c) : s.x₁ ∈ c.X :=
  (s.hXverts _).mp (List.mem_of_mem_head? s.hxhead)

theorem x₁_notMem_p (s : Setup c) : s.x₁ ∉ c.core.p :=
  fun h => c.core.houtX _ h (x₁_mem s)

theorem blocks_disjoint (s : Setup c) : Disjoint c.X c.Y := by
  have hd := (List.nodup_append.mp s.hanti.1.2.1).2.2
  refine Set.disjoint_left.mpr ?_
  intro v hvX hvY
  exact hd v ((s.hXverts v).mpr hvX) v ((s.hYverts v).mpr hvY) rfl

theorem x₁_notMem_wSet (s : Setup c) : s.x₁ ∉ wSet s := by
  rintro (hx | hy)
  · exact hx.2 rfl
  · exact Set.disjoint_left.mp (blocks_disjoint s) (x₁_mem s)
      ((s.hYverts _).mp (List.take_subset _ _ hy))

theorem wSet_subset (s : Setup c) : wSet s ⊆ c.X ∪ c.Y := by
  rintro v (hv | hv)
  · exact Or.inl hv.1
  · exact Or.inr ((s.hYverts v).mp (List.take_subset _ _ hv))

theorem p_out_wSet (s : Setup c) : ∀ v ∈ c.core.p, v ∉ wSet s := by
  intro v hv hw
  rcases wSet_subset s hw with hx | hy
  · exact c.core.houtX v hv hx
  · exact c.core.houtY v hv hy

theorem p₁_complete_wSet (s : Setup c) : VertexComplete G c.core.p₁ (wSet s) := by
  rintro v (hv | hv)
  · exact c.core.hp₁X v hv.1
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have hjt : j < s.t₀ := lt_of_lt_of_le hj (List.length_take_le _ _)
    simpa using s.hbefore j hjt

theorem z_complete_wSet (s : Setup c) : VertexComplete G z (wSet s) :=
  fun v hv => c.hzXY v (wSet_subset s hv)

/-- On `P`, adjacency to `x₁` and completeness to `W` imply completeness to `X`. -/
theorem complete_X_of_complete_wSet (s : Setup c) {v : V}
    (hv : VertexComplete G v (wSet s)) (hx : G.Adj s.x₁ v) :
    VertexComplete G v c.X := by
  intro x hxX
  by_cases he : x = s.x₁
  · simpa [he] using hx.symm
  · exact hv x (Or.inl ⟨hxX, he⟩)

theorem wSet_eq_list (s : Setup c) :
    wSet s = {v | v ∈ s.qX.tail ++ s.qY.take s.t₀} := by
  have hxshape : s.qX = s.x₁ :: s.qX.tail := by
    cases he : s.qX with
    | nil => have hh := s.hXlong; simp [he] at hh
    | cons a L =>
      have ha : a = s.x₁ := by simpa [he] using s.hxhead
      simp [ha]
  have hnd : s.qX.Nodup := (List.nodup_append.mp s.hanti.1.2.1).1
  have hxnt : s.x₁ ∉ s.qX.tail := by
    rw [hxshape] at hnd
    exact (List.nodup_cons.mp hnd).1
  ext v
  simp only [wSet, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, List.mem_append]
  apply or_congr _ Iff.rfl
  rw [← s.hXverts v]
  conv_lhs => rw [hxshape, List.mem_cons]
  constructor
  · rintro ⟨he | hv, hn⟩
    · exact (hn he).elim
    · exact hv
  · intro hv
    exact ⟨Or.inr hv, fun he => hxnt (he ▸ hv)⟩

theorem wSet_anticonnected (s : Setup c) : AnticonnectedSet G (wSet s) := by
  have hdrop : IsPathList Gᶜ ((s.qX ++ s.qY).drop 1) :=
    PathBasics.isPathList_drop s.hanti.1 (by simp; have := s.hXlong; omega)
  have heq : ((s.qX ++ s.qY).drop 1).take (s.qX.length - 1 + s.t₀) =
      s.qX.tail ++ s.qY.take s.t₀ := by
    rw [List.drop_append_of_le_length (by have := s.hXlong; omega), List.drop_one]
    rw [List.take_append]
    simp only [List.length_tail]
    rw [List.take_of_length_le (by simp)]
    congr 2
    omega
  rw [wSet_eq_list, ← heq]
  exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (PathBasics.isPathList_take hdrop (by have := s.hXlong; omega))

theorem wSet_union_Y (s : Setup c) :
    wSet s ∪ c.Y = {v | v ∈ (s.qX ++ s.qY).tail} := by
  rw [wSet_eq_list, List.tail_append_of_ne_nil (by
    intro he; have := s.hXlong; simp [he] at this)]
  ext v
  simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]
  constructor
  · rintro ((hx | hy) | hy)
    · exact Or.inl hx
    · exact Or.inr (List.take_subset _ _ hy)
    · exact Or.inr ((s.hYverts v).mpr hy)
  · rintro (hx | hy)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr ((s.hYverts v).mp hy)

theorem wSet_union_Y_anticonnected (s : Setup c) :
    AnticonnectedSet G (wSet s ∪ c.Y) := by
  rw [wSet_union_Y, ← List.drop_one]
  exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (PathBasics.isPathList_drop s.hanti.1 (by simp; have := s.hXlong; omega))

/-- PAPER: "From the optimality of `P,X,Y`, it follows that `P,W,Y` is not a
counterexample ... and so there are an odd number of `W`-complete edges in `P`."
The union loses `x₁`, so the second optimality clause suffices. -/
theorem odd_edges_wSet (s : Setup c) (hopt : IsOptimal c) :
    Odd (edges G (wSet s) c.core.p).ncard := by
  classical
  by_contra hodd
  have heven := Nat.not_odd_iff_even.mp hodd
  let d : Counterexample G z :=
    { X := wSet s
      Y := c.Y
      core :=
        { p := c.core.p
          p₁ := c.core.p₁
          pₙ := c.core.pₙ
          hp := c.core.hp
          hodd := c.core.hodd
          hlong := c.core.hlong
          houtX := p_out_wSet s
          houtY := c.core.houtY
          hp₁X := p₁_complete_wSet s
          hYuniq := c.core.hYuniq
          hzP := c.core.hzP
          hzanti := c.core.hzanti
          heven := heven }
      hXa := wSet_anticonnected s
      hYa := c.hYa
      hXYa := wSet_union_Y_anticonnected s
      hz := fun h => h.elim (fun hw => c.hz (wSet_subset s hw))
        (fun hy => c.hz (Or.inr hy))
      hzXY := fun v hv => hv.elim (z_complete_wSet s v)
        (fun hy => c.hzXY v (Or.inr hy)) }
  apply hopt.2.1 d rfl
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rintro v (hv | hv)
    · exact wSet_subset s hv
    · exact Or.inr hv
  · intro he
    have hx : s.x₁ ∈ d.X ∪ d.Y := he ▸ Or.inl (x₁_mem s)
    rcases hx with hw | hy
    · exact x₁_notMem_wSet s hw
    · exact Set.disjoint_left.mp (blocks_disjoint s) (x₁_mem s) hy

/-- The antipath prefix ending at the first vertex of `Y` missed by `p₁`. -/
def antiPrefix (s : Setup c) : List V := s.qX ++ s.qY.take (s.t₀ + 1)

theorem prefix_eq_take (s : Setup c) :
    antiPrefix s = (s.qX ++ s.qY).take (s.qX.length + s.t₀ + 1) := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  simp [antiPrefix, Nat.add_assoc]

theorem prefix_from (s : Setup c) :
    IsAntipathFrom G (antiPrefix s) s.x₁ (s.qY[s.t₀]'s.ht₀) := by
  have hX := s.hXlong
  have ht := s.ht₀
  have hk : s.qX.length + s.t₀ < (s.qX ++ s.qY).length := by simp; omega
  have hpath := PathBasics.isPathFrom_slice s.hanti.1
    (show 0 < s.qX.length + s.t₀ by omega) hk
  have h0 := PathBasics.getElem_zero_of_head? s.hanti.2.1
    (show 0 < (s.qX ++ s.qY).length by simp; omega)
  have hkval : (s.qX ++ s.qY)[s.qX.length + s.t₀]'hk =
      s.qY[s.t₀]'ht := by simp
  simpa only [List.drop_zero, Nat.sub_zero, ← prefix_eq_take s, h0, hkval]
    using hpath

theorem prefix_subset (s : Setup c) : ∀ v ∈ antiPrefix s, v ∈ c.X ∪ c.Y := by
  intro v hv
  rcases List.mem_append.mp hv with hx | hy
  · exact Or.inl ((s.hXverts v).mp hx)
  · exact Or.inr ((s.hYverts v).mp (List.take_subset _ _ hy))

/-- PAPER: "So `x₁-⋯-x_s-y₁-⋯-y_{t₀}-p₁` is an antipath." -/
theorem first_miss_antipath (s : Setup c) :
    IsAntipathFrom G (antiPrefix s ++ [c.core.p₁]) s.x₁ c.core.p₁ := by
  have hp₁ : c.core.p₁ ∈ c.core.p := PathBasics.head_mem c.core.hp.2.1
  have hout : c.core.p₁ ∉ antiPrefix s := by
    intro hp
    rcases prefix_subset s _ hp with hx | hy
    · exact c.core.houtX _ hp₁ hx
    · exact c.core.houtY _ hp₁ hy
  apply PathAttach.isPathFrom_concat (prefix_from s)
  · apply (SimpleGraph.compl_adj G _ _).mpr
    exact ⟨fun he => c.core.houtY _ hp₁ (he ▸
      ((s.hYverts _).mp (List.getElem_mem s.ht₀))), s.hmiss⟩
  · exact hout
  · intro v hv hne hvadj
    apply ((SimpleGraph.compl_adj G _ _).mp hvadj).2
    rcases List.mem_append.mp hv with hx | hy
    · exact c.core.hp₁X v ((s.hXverts v).mp hx)
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      have hjt : j < s.t₀ + 1 := lt_of_lt_of_le hj (List.length_take_le _ _)
      have hjne : j ≠ s.t₀ := by
        intro he
        apply hne
        simp only [List.getElem_take]
        subst j
        rfl
      simpa using s.hbefore j (by omega)

end Workspace.ProofLemmas.Thm175Claim4Setup
