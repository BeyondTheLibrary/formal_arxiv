import Workspace.ProofLemmas.Thm93Infrastructure
import Workspace.ProofLemmas.PathBasics

/-! The two long-branch outcomes of 5.8 give alternatives 2 and 3 of 9.3. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm93CaseOneLong
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

/-- The four attachment patterns in 5.8.2. The list `R` is the line-graph path of a branch;
`P` is the path in `F`. -/
abbrev BranchAlternatives {V : Type*} (G : SimpleGraph V) (K N₁ N₂ : Set V)
    (R : List V) (r₁ r₂ : V) (P : List V) (p₁ p₂ : V) : Prop :=
  ((∀ x ∈ N₁ \ {r₁}, G.Adj p₁ x) ∧
    (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
    (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
      (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
  ((∀ x ∈ N₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N₂ \ {r₂}, G.Adj p₂ x) ∧
    (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N₂ \ {r₂}) ∨
      (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
    (Even (pathLength P) ↔ Even (pathLength R))) ∨
  (p₁ = p₂ ∧ (∀ x ∈ (N₁ ∪ N₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
    (∀ y ∈ K, G.Adj p₁ y → y ∈ N₁ ∪ N₂ ∪ {z : V | z ∈ R}) ∧
    Even (pathLength R)) ∨
  (r₁ = r₂ ∧ (∀ x ∈ N₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N₂ \ {r₂}, G.Adj p₂ x) ∧
    (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
      (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N₂ \ {r₂})) ∧
    Even (pathLength P))

/-- The branch is one of the two paths of the knot. Its two end triangles, with the
path ends removed, are exactly those ends' neighbours in the rest of the knot. -/
structure LongSide {V : Type*} (G : SimpleGraph V) (P : List V) (a b : V)
    (K S N₁ N₂ : Set V) : Prop where
  path : IsPathList G P
  odd : Odd (pathLength P)
  a_mem : a ∈ P
  b_mem : b ∈ P
  ends_ne : a ≠ b
  cover : K = {v | v ∈ P} ∪ S
  disjoint : Disjoint {v | v ∈ P} S
  first : N₁ \ {a} = {w ∈ S | G.Adj a w}
  last : N₂ \ {b} = {w ∈ S | G.Adj b w}

/-- A path's length is determined by its vertex set. -/
theorem pathLength_eq_of_support {V : Type*} {G : SimpleGraph V} {P R : List V}
    (hP : IsPathList G P) (hR : IsPathList G R)
    (hset : {v | v ∈ R} = {v | v ∈ P}) : pathLength R = pathLength P := by
  have hp : R.Perm P := (List.perm_ext_iff_of_nodup hR.2.1 hP.2.1).mpr (fun v =>
    Set.ext_iff.mp hset v)
  exact congrArg (fun n => n - 1) hp.length_eq

/-- **PAPER (9.3, printed p. 49):** *"In the first two cases statements 2,3 of the theorem
hold, respectively, and the last case is impossible since `P₁` is odd."*

The two conclusions are stated for an arbitrary choice of the long path and its orientation,
so the four symmetries of 9.3 need no repeated proof. -/
theorem long_branch {V : Type*} {G : SimpleGraph V}
    {P R T : List V} {a b p₁ p₂ : V} {K S N₁ N₂ F : Set V}
    (hs : LongSide G P a b K S N₁ N₂)
    (hR : IsPathList G R) (hset : {v | v ∈ R} = {v | v ∈ P})
    (hT : IsPathFrom G T p₁ p₂) (hTF : ∀ v ∈ T, v ∈ F)
    (halt : BranchAlternatives G K N₁ N₂ R a b T p₁ p₂) :
    ((∀ w ∈ S, G.Adj p₁ w ↔ G.Adj a w) ∧
      Anticomplete G ({v | v ∈ T} \ {p₁}) S ∧
      (∃ w ∈ ({v | v ∈ P} \ {a}), G.Adj p₂ w) ∧
      Anticomplete G ({v | v ∈ T} \ {p₂}) ({v | v ∈ P} \ {a})) ∨
    (Odd (pathLength T) ∧
      (∀ w ∈ S, G.Adj p₁ w ↔ G.Adj a w) ∧
      (∀ w ∈ S, G.Adj p₂ w ↔ G.Adj b w) ∧
      Anticomplete G {v | v ∈ SPGT.interior T} S ∧
      (∀ u ∈ T, ∀ w ∈ P, G.Adj u w → ((u = p₁ ∧ w = a) ∨ (u = p₂ ∧ w = b)))) := by
  have hoddR : ¬ Even (pathLength R) := by
    rw [pathLength_eq_of_support hs.path hR hset]
    exact Nat.not_even_iff_odd.mpr hs.odd
  have haS : a ∉ S := fun h => Set.disjoint_left.mp hs.disjoint hs.a_mem h
  have hbS : b ∉ S := fun h => Set.disjoint_left.mp hs.disjoint hs.b_mem h
  have hS : S ⊆ K := by rw [hs.cover]; exact Set.subset_union_right
  have hP : {v | v ∈ P} ⊆ K := by rw [hs.cover]; exact Set.subset_union_left
  have hf : N₁ \ {a} ⊆ S := by rw [hs.first]; exact fun _ h => h.1
  have hl : N₂ \ {b} ⊆ S := by rw [hs.last]; exact fun _ h => h.1
  have hp₁ := (PathBasics.isPathFrom_ends_mem hT).1
  have hp₂ := (PathBasics.isPathFrom_ends_mem hT).2
  rcases halt with ⟨hfirst, hhit, hno⟩ | ⟨hfirst, hlast, hno, hpar⟩ | ⟨_, _, _, he⟩ | ⟨heq, _⟩
  · left
    have hno' : ∀ x ∈ T, ∀ y ∈ K, y ≠ a → G.Adj x y →
        (x = p₁ ∧ y ∈ N₁ \ {a}) ∨ (x = p₂ ∧ y ∈ {z | z ∈ P} \ {a}) := by
      simpa only [hset] using hno
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w hw
      constructor
      · intro hadj
        rcases hno' p₁ hp₁ w (hS hw) (fun h => haS (h ▸ hw)) hadj with h | h
        · exact (hs.first ▸ h.2).2
        · exact (Set.disjoint_left.mp hs.disjoint h.2.1 hw).elim
      · intro hadj
        exact hfirst w (hs.first ▸ (show w ∈ {w ∈ S | G.Adj a w} from ⟨hw, hadj⟩))
    · rintro u ⟨hu, hune⟩ w hw hadj
      rcases hno' u hu w (hS hw) (fun h => haS (h ▸ hw)) hadj with h | h
      · exact hune h.1
      · exact Set.disjoint_left.mp hs.disjoint h.2.1 hw
    · simpa only [hset] using hhit
    · rintro u ⟨hu, hune⟩ w ⟨hw, hwa⟩ hadj
      rcases hno' u hu w (hP hw) hwa hadj with h | h
      · exact Set.disjoint_left.mp hs.disjoint hw (hf h.2)
      · exact hune h.1
  · right
    have hoT : Odd (pathLength T) := Nat.not_even_iff_odd.mp (fun he => hoddR (hpar.mp he))
    have hne : p₁ ≠ p₂ := PathBasics.isPathFrom_ends_ne hT (by
      obtain ⟨k, hk⟩ := hoT
      omega)
    refine ⟨hoT, ?_, ?_, ?_, ?_⟩
    · intro w hw
      constructor
      · intro hadj
        rcases hno p₁ hp₁ w (hS hw) hadj with h | h | h | h
        · exact (hs.first ▸ h.2).2
        · exact (hne h.1).elim
        · exact (haS (h.2 ▸ hw)).elim
        · exact (hbS (h.2 ▸ hw)).elim
      · intro hadj
        exact hfirst w (hs.first ▸ (show w ∈ {w ∈ S | G.Adj a w} from ⟨hw, hadj⟩))
    · intro w hw
      constructor
      · intro hadj
        rcases hno p₂ hp₂ w (hS hw) hadj with h | h | h | h
        · exact (hne h.1.symm).elim
        · exact (hs.last ▸ h.2).2
        · exact (haS (h.2 ▸ hw)).elim
        · exact (hbS (h.2 ▸ hw)).elim
      · intro hadj
        exact hlast w (hs.last ▸ (show w ∈ {w ∈ S | G.Adj b w} from ⟨hw, hadj⟩))
    · intro u hu w hw hadj
      obtain ⟨huT, hune₁, hune₂⟩ := PathBasics.mem_interior_iff_of_pathFrom hT |>.mp hu
      rcases hno u huT w (hS hw) hadj with h | h | h | h
      exacts [hune₁ h.1, hune₂ h.1, hune₁ h.1, hune₂ h.1]
    · intro u hu w hw hadj
      rcases hno u hu w (hP hw) hadj with h | h | h | h
      · exact (Set.disjoint_left.mp hs.disjoint hw (hf h.2)).elim
      · exact (Set.disjoint_left.mp hs.disjoint hw (hl h.2)).elim
      · exact Or.inl h
      · exact Or.inr h
  · exact (hoddR he).elim
  · exact (hs.ends_ne heq).elim

end Workspace.ProofLemmas.Thm93CaseOneLong
