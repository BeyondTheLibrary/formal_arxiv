import Workspace.ProofLemmas.Thm93KnotTransport
import Workspace.ProofLemmas.KnotLabels

/-! A knot with short antipaths, indexed by the positions on its two paths. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Workspace.ProofLemmas.Thm93KnotModel
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

/-- Positions on the two paths, followed by `x₁,x₂,y₁,y₂`. -/
abbrev Vertex (m n : ℕ) := Fin m ⊕ (Fin n ⊕ Fin 4)

/-- The four vertices on the two short antipaths. -/
def cross {m n : ℕ} (k : Fin 4) : Vertex m n := Sum.inr (Sum.inr k)

/-- The adjacency table in the definition of a knot. -/
def Adj (m n : ℕ) : Vertex m n → Vertex m n → Prop
  | .inl i, .inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inr (.inl i), .inr (.inl j) => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inl _, .inr (.inl _) => False
  | .inr (.inl _), .inl _ => False
  | .inl i, .inr (.inr k) => (i.val = 0 ∧ k.val < 2) ∨ (i.val + 1 = m ∧ 2 ≤ k.val)
  | .inr (.inr k), .inl i => (i.val = 0 ∧ k.val < 2) ∨ (i.val + 1 = m ∧ 2 ≤ k.val)
  | .inr (.inl i), .inr (.inr k) =>
      (i.val = 0 ∧ (k.val = 0 ∨ k.val = 3)) ∨ (i.val + 1 = n ∧ (k.val = 1 ∨ k.val = 2))
  | .inr (.inr k), .inr (.inl i) =>
      (i.val = 0 ∧ (k.val = 0 ∨ k.val = 3)) ∨ (i.val + 1 = n ∧ (k.val = 1 ∨ k.val = 2))
  | .inr (.inr k), .inr (.inr j) => k.val % 2 ≠ j.val % 2

/-- The graph determined by that table. -/
def graph (m n : ℕ) : SimpleGraph (Vertex m n) where
  Adj := Adj m n
  symm := by
    rintro (i | i | i) (j | j | j) h <;> dsimp [Adj] at * <;> omega
  loopless := by
    refine ⟨?_⟩
    rintro (i | i | i) <;> dsimp [Adj] <;> omega

/-- The first path, in order. -/
def leftPath (m n : ℕ) : List (Vertex m n) := List.ofFn Sum.inl
/-- The second path, in order. -/
def rightPath (m n : ℕ) : List (Vertex m n) := List.ofFn (fun i => Sum.inr (Sum.inl i))

/-- Read indexed vertices into the actual knot. -/
def label {V : Type*} (P₁ P₂ : List V) (x₁ x₂ y₁ y₂ : V) : Vertex P₁.length P₂.length → V
  | .inl i => P₁[i.val]
  | .inr (.inl j) => P₂[j.val]
  | .inr (.inr k) => ![x₁,x₂,y₁,y₂] k

@[simp] theorem leftPath_map_label {V : Type*} (P₁ P₂ : List V) (x₁ x₂ y₁ y₂ : V) :
    (leftPath P₁.length P₂.length).map (label P₁ P₂ x₁ x₂ y₁ y₂) = P₁ := by
  simp [leftPath, List.map_ofFn, Function.comp_def, label]

@[simp] theorem rightPath_map_label {V : Type*} (P₁ P₂ : List V) (x₁ x₂ y₁ y₂ : V) :
    (rightPath P₁.length P₂.length).map (label P₁ P₂ x₁ x₂ y₁ y₂) = P₂ := by
  simp [rightPath, List.map_ofFn, Function.comp_def, label]

/-- The labels are distinct, cover the knot, and preserve all adjacency.
This makes precise the paper's identification of `K` with its two paths and four cross edges. -/
theorem label_spec {V : Type*} (G : SimpleGraph V)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hL₁ : pathLength Q₁ = 1) (hL₂ : pathLength Q₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K) :
    Function.Injective (label P₁ P₂ x₁ x₂ y₁ y₂) ∧
    K = Set.range (label P₁ P₂ x₁ x₂ y₁ y₂) ∧
    ∀ u v, G.Adj (label P₁ P₂ x₁ x₂ y₁ y₂ u) (label P₁ P₂ x₁ x₂ y₁ y₂ v) ↔
      (graph P₁.length P₂.length).Adj u v := by
  obtain rfl := KnotLabels.anti_eq_pair_of_length_one hQ₁ hL₁
  obtain rfl := KnotLabels.anti_eq_pair_of_length_one hQ₂ hL₂
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq12, l1, l2, _, _, hanti, hcomp,
    e11, e12, e21, e22, _, _, _, _⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have hx1y1 : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hQ₁ (by simp [pathLength])
  have hx2y2 : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hQ₂ (by simp [pathLength])
  have hx1x2 : x₁ ≠ x₂ := by intro h; exact dq12 x₁ (by simp) (by simp [h])
  have hx1y2 : x₁ ≠ y₂ := by intro h; exact dq12 x₁ (by simp) (by simp [h])
  have hy1x2 : y₁ ≠ x₂ := by intro h; exact dq12 y₁ (by simp) (by simp [h])
  have hy1y2 : y₁ ≠ y₂ := by intro h; exact dq12 y₁ (by simp) (by simp [h])
  have hcInj : Function.Injective (![x₁,x₂,y₁,y₂] : Fin 4 → V) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [hx1x2, hx1x2.symm, hx1y1, hx1y1.symm, hx1y2, hx1y2.symm,
        hy1x2, hy1x2.symm, hx2y2, hx2y2.symm, hy1y2, hy1y2.symm] at h ⊢
  have hcNot₁ : ∀ i : Fin P₁.length, ∀ k : Fin 4, P₁[i.val] ≠ ![x₁,x₂,y₁,y₂] k := by
    intro i k h
    have hmem : P₁[i.val] ∈ P₁ := List.getElem_mem i.isLt
    fin_cases k
    · exact d1q1 _ hmem (by simp [h])
    · exact d1q2 _ hmem (by simp [h])
    · exact d1q1 _ hmem (by simp [h])
    · exact d1q2 _ hmem (by simp [h])
  have hcNot₂ : ∀ i : Fin P₂.length, ∀ k : Fin 4, P₂[i.val] ≠ ![x₁,x₂,y₁,y₂] k := by
    intro i k h
    have hmem : P₂[i.val] ∈ P₂ := List.getElem_mem i.isLt
    fin_cases k
    · exact d2q1 _ hmem (by simp [h])
    · exact d2q2 _ hmem (by simp [h])
    · exact d2q1 _ hmem (by simp [h])
    · exact d2q2 _ hmem (by simp [h])
  have hinj : Function.Injective (label P₁ P₂ x₁ x₂ y₁ y₂) := by
    rintro (i | i | i) (j | j | j) h <;> dsimp only [label] at h
    · exact congrArg Sum.inl (Fin.ext ((hP₁.1.2.1.getElem_inj_iff).mp h))
    · exact (d12 _ (List.getElem_mem i.isLt) (h.symm ▸ List.getElem_mem j.isLt)).elim
    · exact (hcNot₁ i j h).elim
    · exact (d12 _ (List.getElem_mem j.isLt) (h ▸ List.getElem_mem i.isLt)).elim
    · exact congrArg (fun j => Sum.inr (Sum.inl j)) (Fin.ext ((hP₂.1.2.1.getElem_inj_iff).mp h))
    · exact (hcNot₂ i j h).elim
    · exact (hcNot₁ j i h.symm).elim
    · exact (hcNot₂ j i h.symm).elim
    · exact congrArg cross (hcInj h)
  refine ⟨hinj, ?_, ?_⟩
  · change K = _ at hK
    rw [hK]
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_range]
    constructor
    · rintro (((h | h) | h) | h)
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
        exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
        exact ⟨Sum.inr (Sum.inl ⟨i, hi⟩), rfl⟩
      · rcases h with rfl | rfl
        exacts [⟨cross 0, rfl⟩, ⟨cross 2, rfl⟩]
      · rcases h with rfl | rfl
        exacts [⟨cross 1, rfl⟩, ⟨cross 3, rfl⟩]
    · rintro ⟨(i | i | i), rfl⟩
      · exact Or.inl (Or.inl (Or.inl (List.getElem_mem i.isLt)))
      · exact Or.inl (Or.inl (Or.inr (List.getElem_mem i.isLt)))
      · fin_cases i <;> simp [label]
  · have hlen1 : 0 < P₁.length := by unfold pathLength at l1; omega
    have hlen2 : 0 < P₂.length := by unfold pathLength at l2; omega
    have ends₁ (i : Fin P₁.length) :
        (P₁[i.val] = a₁ ↔ i.val = 0) ∧ (P₁[i.val] = b₁ ↔ i.val + 1 = P₁.length) := by
      rw [← PathBasics.getElem_zero_of_head? hP₁.2.1 hlen1,
        ← PathBasics.getElem_last_of_getLast? hP₁.2.2 hlen1,
        hP₁.1.2.1.getElem_inj_iff, hP₁.1.2.1.getElem_inj_iff]
      omega
    have ends₂ (i : Fin P₂.length) :
        (P₂[i.val] = a₂ ↔ i.val = 0) ∧ (P₂[i.val] = b₂ ↔ i.val + 1 = P₂.length) := by
      rw [← PathBasics.getElem_zero_of_head? hP₂.2.1 hlen2,
        ← PathBasics.getElem_last_of_getLast? hP₂.2.2 hlen2,
        hP₂.1.2.1.getElem_inj_iff, hP₂.1.2.1.getElem_inj_iff]
      omega
    have ec₁ (i : Fin P₁.length) (k : Fin 4) :
        G.Adj P₁[i.val] (![x₁,x₂,y₁,y₂] k) ↔
          (i.val = 0 ∧ k.val < 2) ∨ (i.val + 1 = P₁.length ∧ 2 ≤ k.val) := by
      have hm := List.getElem_mem i.isLt
      have h1 := e11 P₁[i.val] hm x₁ (by simp)
      have h2 := e12 P₁[i.val] hm x₂ (by simp)
      have h3 := e11 P₁[i.val] hm y₁ (by simp)
      have h4 := e12 P₁[i.val] hm y₂ (by simp)
      fin_cases k <;> simp [h1, h2, h3, h4, hx1y1, hx1y1.symm, hx2y2, hx2y2.symm, (ends₁ i).1, (ends₁ i).2]
    have ec₂ (i : Fin P₂.length) (k : Fin 4) :
        G.Adj P₂[i.val] (![x₁,x₂,y₁,y₂] k) ↔
          (i.val = 0 ∧ (k.val = 0 ∨ k.val = 3)) ∨
          (i.val + 1 = P₂.length ∧ (k.val = 1 ∨ k.val = 2)) := by
      have hm := List.getElem_mem i.isLt
      have h1 := e21 P₂[i.val] hm x₁ (by simp)
      have h2 := e22 P₂[i.val] hm x₂ (by simp)
      have h3 := e21 P₂[i.val] hm y₁ (by simp)
      have h4 := e22 P₂[i.val] hm y₂ (by simp)
      fin_cases k <;> simp [h1, h2, h3, h4, hx1y1, hx1y1.symm, hx2y2, hx2y2.symm, (ends₂ i).1, (ends₂ i).2]
    have n1 : ¬ G.Adj x₁ y₁ :=
      ((SimpleGraph.compl_adj G x₁ y₁).mp ((hQ₁.1.2.2 0 1 (by simp) (by simp)).mpr (by simp))).2
    have n2 : ¬ G.Adj x₂ y₂ :=
      ((SimpleGraph.compl_adj G x₂ y₂).mp ((hQ₂.1.2.2 0 1 (by simp) (by simp)).mpr (by simp))).2
    have cc₁ := hcomp x₁ (by simp) x₂ (by simp)
    have cc₂ := hcomp x₁ (by simp) y₂ (by simp)
    have cc₃ := hcomp y₁ (by simp) x₂ (by simp)
    have cc₄ := hcomp y₁ (by simp) y₂ (by simp)
    rintro (i | i | i) (j | j | j)
    · exact hP₁.1.2.2 i j i.isLt j.isLt
    · exact iff_false_intro (hanti _ (List.getElem_mem i.isLt) _ (List.getElem_mem j.isLt))
    · exact ec₁ i j
    · exact iff_false_intro (fun h => hanti _ (List.getElem_mem j.isLt) _ (List.getElem_mem i.isLt) h.symm)
    · exact hP₂.1.2.2 i j i.isLt j.isLt
    · exact ec₂ i j
    · simpa only [label, graph, Adj, SimpleGraph.adj_comm] using ec₁ j i
    · simpa only [label, graph, Adj, SimpleGraph.adj_comm] using ec₂ j i
    · fin_cases i <;> fin_cases j <;>
        simp [label, graph, Adj, n1, n2, cc₁, cc₂, cc₃, cc₄,
          cc₁.symm, cc₂.symm, cc₃.symm, cc₄.symm, SimpleGraph.adj_comm]

end Workspace.ProofLemmas.Thm93KnotModel
