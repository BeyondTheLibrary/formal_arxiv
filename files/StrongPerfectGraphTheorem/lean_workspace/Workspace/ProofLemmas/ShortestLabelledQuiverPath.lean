import Mathlib

set_option autoImplicit false

namespace Workspace.ProofLemmas.ShortestLabelledQuiverPath

open Quiver

universe u v w

variable {V : Type u} {A : Type w} [Quiver.{v} V]

/-- The labels of a quiver path, in source-to-target order. -/
def labels (lab : Quiver.Labelling V A) {x y : V} : Quiver.Path x y → List A
  | .nil => []
  | .cons p e => labels lab p ++ [lab e]

@[simp]
theorem labels_nil (lab : Quiver.Labelling V A) (x : V) :
    labels lab (Quiver.Path.nil : Quiver.Path x x) = [] := rfl

@[simp]
theorem labels_cons (lab : Quiver.Labelling V A) {x y z : V}
    (p : Quiver.Path x y) (e : y ⟶ z) :
    labels lab (p.cons e) = labels lab p ++ [lab e] := rfl

theorem labels_comp (lab : Quiver.Labelling V A) {x y z : V}
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    labels lab (p.comp q) = labels lab p ++ labels lab q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, List.append_assoc]

@[simp]
theorem labels_length (lab : Quiver.Labelling V A) {x y : V}
    (p : Quiver.Path x y) : (labels lab p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

/-- A globally shortest directed path cannot repeat a vertex. -/
theorem vertices_nodup_of_length_minimal {s t : V} (p : Quiver.Path s t)
    (hmin : ∀ q : Quiver.Path s t, p.length ≤ q.length) :
    p.vertices.Nodup := by
  induction p with
  | nil => simp
  | @cons u t p e ih =>
      rw [Quiver.Path.vertices_cons, List.nodup_concat]
      constructor
      · intro ht
        obtain ⟨p₁, p₂, hp⟩ := p.exists_eq_comp_of_mem_vertices ht
        have hshort := hmin p₁
        rw [hp, Quiver.Path.length_cons, Quiver.Path.length_comp] at hshort
        omega
      · apply ih
        intro q
        have h := hmin (q.cons e)
        simpa only [Quiver.Path.length_cons, Nat.add_le_add_iff_right] using h

theorem labels_head {tail : A → V} (lab : Quiver.Labelling V A)
    (hlab : ∀ {x y : V} (e : x ⟶ y), tail (lab e) = x)
    {s t : V} (p : Quiver.Path s t) (hp : labels lab p ≠ []) :
    ∃ a, (labels lab p).head? = some a ∧ tail a = s := by
  have hlen : p.length ≠ 0 := by
    intro hzero
    have : (labels lab p).length = 0 := by simp [hzero]
    exact hp (List.length_eq_zero_iff.mp this)
  obtain ⟨u, e, q, hpq, _⟩ := (Quiver.Path.length_ne_zero_iff_eq_comp p).mp hlen
  subst p
  refine ⟨lab e, ?_, hlab e⟩
  simp [labels_comp, Quiver.Hom.toPath, labels]

theorem labels_last {head : A → V} (lab : Quiver.Labelling V A)
    (hlab : ∀ {x y : V} (e : x ⟶ y), head (lab e) = y)
    {s t : V} (p : Quiver.Path s t) (hp : labels lab p ≠ []) :
    ∃ a, (labels lab p).getLast? = some a ∧ head a = t := by
  have hlen : p.length ≠ 0 := by
    intro hzero
    have : (labels lab p).length = 0 := by simp [hzero]
    exact hp (List.length_eq_zero_iff.mp this)
  obtain ⟨u, q, e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hlen
  refine ⟨lab e, ?_, hlab e⟩
  simp

theorem labels_isChain {tail head : A → V} (lab : Quiver.Labelling V A)
    (htail : ∀ {x y : V} (e : x ⟶ y), tail (lab e) = x)
    (hhead : ∀ {x y : V} (e : x ⟶ y), head (lab e) = y)
    {s t : V} (p : Quiver.Path s t) :
    (labels lab p).IsChain (fun a b => head a = tail b) := by
  induction p with
  | nil => exact .nil
  | @cons u t p e ih =>
      by_cases hp : labels lab p = []
      · simp [hp]
      · apply ih.append (List.isChain_singleton (lab e))
        intro a ha b hb
        obtain ⟨a', ha', hha'⟩ := labels_last lab hhead p hp
        simp only [ha', Option.mem_some_iff] at ha
        simp only [List.head?_singleton, Option.mem_some_iff] at hb
        subst a
        subst b
        exact hha'.trans (htail e).symm

theorem forall_zip_tail_of_isChain {R : A → A → Prop} {l : List A}
    (hl : l.IsChain R) : ∀ ab ∈ l.zip l.tail, R ab.1 ab.2 := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b l ih ih₂ =>
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
      intro ab hab
      rcases hab with rfl | hab
      · exact (List.isChain_cons_cons.mp hl).1
      · exact ih₂ b (List.isChain_cons_cons.mp hl).2 ab hab

theorem cons_map_head_labels_eq_vertices {head : A → V}
    (lab : Quiver.Labelling V A)
    (hhead : ∀ {x y : V} (e : x ⟶ y), head (lab e) = y)
    {s t : V} (p : Quiver.Path s t) :
    s :: (labels lab p).map head = p.vertices := by
  induction p with
  | nil => rfl
  | @cons u t p e ih =>
      simpa only [labels_cons, List.map_append, List.map_singleton, hhead e,
        Quiver.Path.vertices_cons, List.concat_eq_append] using
        congrArg (fun l : List V => l ++ [t]) ih

theorem labels_forall {P : A → Prop} (lab : Quiver.Labelling V A)
    (hlab : ∀ {x y : V} (e : x ⟶ y), P (lab e))
    {s t : V} (p : Quiver.Path s t) : ∀ a ∈ labels lab p, P a := by
  induction p with
  | nil => simp
  | cons p e ih =>
      intro a ha
      simp only [labels_cons, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact ih a ha
      · exact hlab e

end Workspace.ProofLemmas.ShortestLabelledQuiverPath
