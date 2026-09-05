import Workspace.ProofLemmas.ShortestLabelledQuiverPath

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Quiver

private def residualTail {V A : Type*} (tail head : A → V) : Bool × A → V
  | (true, a) => tail a
  | (false, a) => head a

private def residualHead {V A : Type*} (tail head : A → V) : Bool × A → V
  | (true, a) => head a
  | (false, a) => tail a

private def residualDelta {A : Type*} [DecidableEq A]
    (rho : List (Bool × A)) (a : A) : Int :=
  (rho.count (true, a) : Int) - (rho.count (false, a) : Int)

private theorem sum_if_add_single
    {V A : Type*} [Fintype A] [DecidableEq V] [DecidableEq A]
    (endpoint : A → V) (d : A → Int) (a₀ : A) (c : Int) (z : V) :
    (∑ a : A, if endpoint a = z then
        d a + (if a₀ = a then c else 0) else 0) =
      (∑ a : A, if endpoint a = z then d a else 0) +
        (if endpoint a₀ = z then c else 0) := by
  calc
    _ = ∑ a : A, ((if endpoint a = z then d a else 0) +
        (if endpoint a = z then (if a₀ = a then c else 0) else 0)) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : endpoint a = z <;> simp [h]
    _ = (∑ a : A, if endpoint a = z then d a else 0) +
        ∑ a : A, (if endpoint a = z then (if a₀ = a then c else 0) else 0) :=
          Finset.sum_add_distrib
    _ = _ := by
      congr 1
      calc
        (∑ a : A, (if endpoint a = z then (if a₀ = a then c else 0) else 0)) =
            ∑ a : A, if a = a₀ then (if endpoint a = z then c else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro a _
              by_cases ha : a = a₀
              · simp [ha]
              · simp [ha, Ne.symm ha]
        _ = _ := by simp

private theorem residualDelta_divergence
    {V A : Type*} [Fintype A] [DecidableEq V] [DecidableEq A] [Quiver V]
    (tail head : A → V) (lab : Quiver.Labelling V (Bool × A))
    (hlabTail : ∀ {x y : V} (e : x ⟶ y),
      residualTail tail head (lab e) = x)
    (hlabHead : ∀ {x y : V} (e : x ⟶ y),
      residualHead tail head (lab e) = y)
    {s t : V} (p : Quiver.Path s t) (z : V) :
    (∑ a : A, if tail a = z then
        residualDelta (ShortestLabelledQuiverPath.labels lab p) a else 0) -
      (∑ a : A, if head a = z then
        residualDelta (ShortestLabelledQuiverPath.labels lab p) a else 0) =
      (if s = z then 1 else 0) - (if t = z then 1 else 0) := by
  induction p with
  | nil => simp [residualDelta]
  | @cons u v p e ih =>
      have htail := hlabTail e
      have hhead := hlabHead e
      rcases hlabel : lab e with ⟨b, a₀⟩
      cases b
      · simp only [residualTail, residualHead] at htail hhead
        have hdelta (a : A) :
            residualDelta (ShortestLabelledQuiverPath.labels lab (p.cons e)) a =
              residualDelta (ShortestLabelledQuiverPath.labels lab p) a +
                (if a₀ = a then -1 else 0) := by
          by_cases ha : a₀ = a <;>
            simp [residualDelta, hlabel, ha] <;> omega
        simp_rw [hdelta]
        rw [sum_if_add_single, sum_if_add_single]
        rw [hlabel] at htail hhead
        subst u
        subst v
        by_cases hs : s = z <;> by_cases ha : tail a₀ = z <;>
          by_cases hb : head a₀ = z <;> simp [hs, ha, hb] at ih ⊢ <;> omega
      · simp only [residualTail, residualHead] at htail hhead
        have hdelta (a : A) :
            residualDelta (ShortestLabelledQuiverPath.labels lab (p.cons e)) a =
              residualDelta (ShortestLabelledQuiverPath.labels lab p) a +
                (if a₀ = a then 1 else 0) := by
          by_cases ha : a₀ = a <;>
            simp [residualDelta, hlabel, ha] <;> omega
        simp_rw [hdelta]
        rw [sum_if_add_single, sum_if_add_single]
        rw [hlabel] at htail hhead
        subst u
        subst v
        by_cases hs : s = z <;> by_cases ha : tail a₀ = z <;>
          by_cases hb : head a₀ = z <;> simp [hs, ha, hb] at ih ⊢ <;> omega

theorem ResidualRouteAugmentsLabelledArcIntegralFlow
    {V A : Type*} [Fintype V] [Fintype A]
    (tail head : A → V) (cap f : A → Nat) (s t : V) (k : Nat)
    (hst : s ≠ t) :
    let flowOut : (A → Nat) → V → Nat := by
      classical
      exact fun q z => ∑ a : A, if tail a = z then q a else 0
    let flowIn : (A → Nat) → V → Nat := by
      classical
      exact fun q z => ∑ a : A, if head a = z then q a else 0
    let feasible : (A → Nat) → Nat → Prop := fun q n =>
      (∀ a : A, q a ≤ cap a) ∧
      (∀ z : V, z ≠ s → z ≠ t → flowOut q z = flowIn q z) ∧
      flowOut q s = flowIn q s + n ∧
      flowIn q t = flowOut q t + n
    let residualStep : V → V → Prop := fun u v =>
      (∃ a : A, tail a = u ∧ head a = v ∧ f a < cap a) ∨
      (∃ a : A, head a = u ∧ tail a = v ∧ 0 < f a)
    let residualReachable : V → V → Prop :=
      Relation.ReflTransGen residualStep
    feasible f k →
      residualReachable s t →
      ∃ f' : A → Nat, feasible f' (k + 1) := by
  classical
  dsimp only
  intro hf hreach
  let step : V → V → Prop := fun u v =>
    (∃ a : A, tail a = u ∧ head a = v ∧ f a < cap a) ∨
    (∃ a : A, head a = u ∧ tail a = v ∧ 0 < f a)
  change Relation.ReflTransGen step s t at hreach
  letI : Quiver V :=
    ⟨fun u v => {ba : Bool × A //
      match ba.1 with
      | true => tail ba.2 = u ∧ head ba.2 = v ∧ f ba.2 < cap ba.2
      | false => head ba.2 = u ∧ tail ba.2 = v ∧ 0 < f ba.2}⟩
  have pathOfReach : ∀ {v : V}, Relation.ReflTransGen step s v →
      Nonempty (Quiver.Path s v) := by
    intro v hv
    induction hv with
    | refl => exact ⟨Quiver.Path.nil⟩
    | @tail u v huv huv' ih =>
        obtain ⟨p⟩ := ih
        rcases huv' with ⟨a, htail, hhead, hres⟩ | ⟨a, hhead, htail, hres⟩
        · exact ⟨p.cons ⟨(true, a), by simp [htail, hhead, hres]⟩⟩
        · exact ⟨p.cons ⟨(false, a), by simp [htail, hhead, hres]⟩⟩
  have hpath : Nonempty (Quiver.Path s t) := pathOfReach hreach
  letI : Nonempty (Quiver.Path s t) := hpath
  let p : Quiver.Path s t :=
    WellFounded.min (measure Quiver.Path.length).wf Set.univ Set.univ_nonempty
  have hpmin : ∀ q : Quiver.Path s t, p.length ≤ q.length := by
    intro q
    exact not_lt.mp
      (WellFounded.not_lt_min (measure Quiver.Path.length).wf Set.univ trivial)
  let lab : Quiver.Labelling V (Bool × A) := fun {_ _} e => e.1
  have htailLab : ∀ {u v : V} (e : u ⟶ v),
      residualTail tail head (lab e) = u := by
    intro u v e
    rcases e with ⟨⟨b, a⟩, he⟩
    cases b <;> simpa [lab, residualTail] using he.1
  have hheadLab : ∀ {u v : V} (e : u ⟶ v),
      residualHead tail head (lab e) = v := by
    intro u v e
    rcases e with ⟨⟨b, a⟩, he⟩
    cases b <;> simpa [lab, residualHead] using he.2.1
  have hresLab : ∀ {u v : V} (e : u ⟶ v),
      match (lab e).1 with
      | true => tail (lab e).2 = u ∧ head (lab e).2 = v ∧
          f (lab e).2 < cap (lab e).2
      | false => head (lab e).2 = u ∧ tail (lab e).2 = v ∧
          0 < f (lab e).2 := by
    intro u v e
    simpa [lab] using e.property
  have hcapLab : ∀ {u v : V} (e : u ⟶ v),
      match (lab e).1 with
      | true => f (lab e).2 < cap (lab e).2
      | false => 0 < f (lab e).2 := by
    intro u v e
    rcases e with ⟨⟨b, a⟩, he⟩
    cases b <;> simpa [lab] using he.2.2
  let rho : List (Bool × A) := ShortestLabelledQuiverPath.labels lab p
  have hpvertices : p.vertices.Nodup :=
    ShortestLabelledQuiverPath.vertices_nodup_of_length_minimal p hpmin
  have hrhoVertices :
      (s :: rho.map (residualHead tail head)).Nodup := by
    rw [ShortestLabelledQuiverPath.cons_map_head_labels_eq_vertices lab hheadLab p]
    exact hpvertices
  have hrhoNodup : rho.Nodup :=
    List.Nodup.of_map (residualHead tail head) hrhoVertices.tail
  have hrhoRes : ∀ ba ∈ rho,
      match ba.1 with
      | true => f ba.2 < cap ba.2
      | false => 0 < f ba.2 := by
    intro ba hba
    have h := ShortestLabelledQuiverPath.labels_forall
      (P := fun ba : Bool × A =>
        match ba.1 with
        | true => f ba.2 < cap ba.2
        | false => 0 < f ba.2) lab hcapLab p ba
      (by simpa [rho] using hba)
    rcases ba with ⟨b, a⟩
    cases b <;> simpa using h
  have hcount (ba : Bool × A) : rho.count ba ≤ 1 :=
    List.nodup_iff_count_le_one.mp hrhoNodup ba
  have hforward (a : A) (ha : 0 < rho.count (true, a)) : f a < cap a := by
    exact hrhoRes (true, a) (List.count_pos_iff.mp ha)
  have hbackward (a : A) (ha : 0 < rho.count (false, a)) : 0 < f a := by
    exact hrhoRes (false, a) (List.count_pos_iff.mp ha)
  let g : A → Int := fun a => (f a : Int) + residualDelta rho a
  have hgNonneg (a : A) : 0 ≤ g a := by
    have hfwd := hforward a
    have hbwd := hbackward a
    have hcf := hcount (true, a)
    have hcb := hcount (false, a)
    simp only [g, residualDelta]
    omega
  have hgCap (a : A) : g a ≤ (cap a : Int) := by
    have hfa := hf.1 a
    have hfwd := hforward a
    have hbwd := hbackward a
    have hcf := hcount (true, a)
    have hcb := hcount (false, a)
    simp only [g, residualDelta]
    omega
  let f' : A → Nat := fun a => (g a).toNat
  have hf'Cast (a : A) : (f' a : Int) = g a := by
    exact Int.toNat_of_nonneg (hgNonneg a)
  have hf'Cap (a : A) : f' a ≤ cap a := by
    have h := hgCap a
    rw [← hf'Cast a] at h
    exact_mod_cast h
  have hsumUpdate (endpoint : A → V) (z : V) :
      (∑ a : A, if endpoint a = z then (f' a : Int) else 0) =
        (∑ a : A, if endpoint a = z then (f a : Int) else 0) +
        (∑ a : A, if endpoint a = z then residualDelta rho a else 0) := by
    calc
      _ = ∑ a : A, if endpoint a = z then
          ((f a : Int) + residualDelta rho a) else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hf'Cast]
      _ = ∑ a : A, ((if endpoint a = z then (f a : Int) else 0) +
          (if endpoint a = z then residualDelta rho a else 0)) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases h : endpoint a = z <;> simp [h]
      _ = _ := Finset.sum_add_distrib
  have hcastSum (q : A → Nat) (endpoint : A → V) (z : V) :
      ((∑ a : A, if endpoint a = z then q a else 0 : Nat) : Int) =
        ∑ a : A, if endpoint a = z then (q a : Int) else 0 := by
    push_cast
    rfl
  have hflowDiff (z : V) :
      ((∑ a : A, if tail a = z then f' a else 0 : Nat) : Int) -
          ((∑ a : A, if head a = z then f' a else 0 : Nat) : Int) =
        (((∑ a : A, if tail a = z then f a else 0 : Nat) : Int) -
          ((∑ a : A, if head a = z then f a else 0 : Nat) : Int)) +
          ((if s = z then 1 else 0) - (if t = z then 1 else 0)) := by
    rw [hcastSum, hcastSum, hsumUpdate, hsumUpdate, hcastSum, hcastSum]
    have hd :
        (∑ a : A, if tail a = z then residualDelta rho a else 0) -
          (∑ a : A, if head a = z then residualDelta rho a else 0) =
          (if s = z then 1 else 0) - (if t = z then 1 else 0) := by
      simpa [rho] using
        (residualDelta_divergence tail head lab htailLab hheadLab p z)
    omega
  refine ⟨f', hf'Cap, ?_, ?_, ?_⟩
  · intro z hzs hzt
    have hbase := hf.2.1 z hzs hzt
    have hdiff := hflowDiff z
    have hzs' : s ≠ z := Ne.symm hzs
    have hzt' : t ≠ z := Ne.symm hzt
    simp only [if_neg hzs', if_neg hzt', sub_zero, add_zero] at hdiff
    omega
  · have hbase :
        (∑ a : A, if tail a = s then f a else 0) =
          (∑ a : A, if head a = s then f a else 0) + k := hf.2.2.1
    have hbaseZ :
        ((∑ a : A, if tail a = s then f a else 0 : Nat) : Int) =
          ((∑ a : A, if head a = s then f a else 0 : Nat) : Int) + k := by
      exact_mod_cast hbase
    have hdiff :
        ((∑ a : A, if tail a = s then f' a else 0 : Nat) : Int) -
            ((∑ a : A, if head a = s then f' a else 0 : Nat) : Int) =
          (((∑ a : A, if tail a = s then f a else 0 : Nat) : Int) -
            ((∑ a : A, if head a = s then f a else 0 : Nat) : Int)) + 1 := by
      simpa [hst.symm] using hflowDiff s
    omega
  · have hbase :
        (∑ a : A, if head a = t then f a else 0) =
          (∑ a : A, if tail a = t then f a else 0) + k := hf.2.2.2
    have hbaseZ :
        ((∑ a : A, if head a = t then f a else 0 : Nat) : Int) =
          ((∑ a : A, if tail a = t then f a else 0 : Nat) : Int) + k := by
      exact_mod_cast hbase
    have hdiff :
        ((∑ a : A, if tail a = t then f' a else 0 : Nat) : Int) -
            ((∑ a : A, if head a = t then f' a else 0 : Nat) : Int) =
          (((∑ a : A, if tail a = t then f a else 0 : Nat) : Int) -
            ((∑ a : A, if head a = t then f a else 0 : Nat) : Int)) - 1 := by
      simpa [hst] using hflowDiff t
    omega

end Workspace.ProofLemmas
