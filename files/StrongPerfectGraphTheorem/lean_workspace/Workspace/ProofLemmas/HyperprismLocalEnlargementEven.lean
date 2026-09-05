import Workspace.ProofLemmas.HyperprismLocalEnlargementCore
import Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality
import Workspace.ProofLemmas.HyperprismLocalEnlargementPathFacts
import Workspace.ProofLemmas.HyperprismLocalEnlargementRegroup
import Workspace.ProofLemmas.HyperprismSplit
import Workspace.ProofLemmas.HyperprismRungStructure
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3eOddHole

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementEven

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality
open Workspace.ProofLemmas.HyperprismLocalEnlargementPathFacts
open Workspace.ProofLemmas.HyperprismLocalEnlargementRegroup
open Workspace.ProofLemmas.HyperprismSplit
open Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3e

/-- PAPER (10.6, even case, printed p. 62): *"We claim that `A'ᵢ` is complete to
`A''ᵢ` ... and similarly `B'ᵢ` is complete to `B''ᵢ`."*

This is the odd-hole step after the rungs have been split.  The two support hypotheses
say that the path's last end has neighbours in two `B`-sets and its first end has
neighbours in two `A`-sets, in the form used by the printed proof. -/
theorem evenSplitCompleteness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q)
    (hDoubleSupport : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (A j \ P j).Nonempty)
    (hPrimeSupport : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (Q j).Nonempty)
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn)
    (heven : Even f.length)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hAedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ a ∈ A i,
      G.Adj z a → z = f₁ ∧ a ∈ P i)
    (hBedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ b ∈ B i,
      G.Adj z b → z = fn ∧ b ∉ Q i)
    (hPadj : ∀ (i : Fin 3), ∀ a ∈ P i, G.Adj f₁ a)
    (hQadj : ∀ (i : Fin 3), ∀ b ∈ B i, b ∉ Q i → G.Adj fn b)
    (hCnone : ∀ z ∈ f, ∀ (i : Fin 3) (c : V), c ∈ C i → ¬ G.Adj z c) :
    (∀ i : Fin 3, Complete G (P i) (A i \ P i)) ∧
      (∀ i : Fin 3, Complete G (Q i) (B i \ Q i)) :=
  ⟨primeCompleteA G A B C P Q hG hH hs hDoubleSupport hf heven hfout hAedges hBedges
      hPadj hQadj hCnone,
    primeCompleteB G A B C P Q hG hH hs hPrimeSupport hf heven hfout hAedges hBedges
      hPadj hQadj hCnone⟩

/-- The easy subcase in the even block: if the last path vertex is complete to the two
other `B`-sets, add it to `B 0` and put the preceding path vertices into `C 0`. -/
theorem evenDirectAtZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) → x ∉ C k)
    (xA xB : V) (hxAA : xA ∈ A 0) (hxBB : xB ∈ B 1)
    (f : List V) (hfne : f ≠ []) (hfF : ∀ v ∈ f, v ∈ F)
    (hfull : IsPathFrom G (xA :: (f ++ [xB])) xA xB)
    (hleft : ∀ v ∈ f, G.Adj xA v ↔ f.head? = some v)
    (hright : ∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v)
    (hFeq : F = {v : V | v ∈ f}) (heven : Even f.length)
    (hcomplete : ∀ b ∈ B 1 ∪ B 2, G.Adj (f.getLast hfne) b) :
    BiggerHyperprism G A B C := by
  obtain ⟨f₁, fn, hf, hxAf₁, hxBfn⟩ := interiorPathData hfne hfull hleft hright
  have hfnEq : fn = f.getLast hfne := by
    have h := hf.2.2
    rw [List.getLast?_eq_some_getLast hfne] at h
    exact (Option.some_injective _ h).symm
  have h2 : 2 ≤ f.length := by
    have hpos := List.length_pos_of_ne_nil hfne
    have hev := heven
    rw [Nat.even_iff] at hev
    omega
  have hfout : ∀ z ∈ f, z ∉ hyperVerts A B C := by
    intro z hz
    exact hF.1.2.1 (hfF z hz)
  have hCnone := noPathEdgeToC hfF hNoC
  have hBuniq : ∀ (k : Fin 3), k ≠ 0 →
      ∀ z ∈ f, ∀ b ∈ B k, G.Adj z b → z = fn := by
    intro k hk
    exact onlyLastSeesB hH hF hf h2 hFeq hk.symm hxAA hxAf₁.symm
  obtain ⟨b₂, hb₂⟩ := (hH.1 2).2.1
  have hfnb₂ : G.Adj fn b₂ := by
    rw [hfnEq]
    exact hcomplete b₂ (Or.inr hb₂)
  have hxAb₂ : ¬ G.Adj xA b₂ := by
    intro hadj
    rcases cross hH (show (0 : Fin 3) ≠ 2 by decide) (Or.inl (Or.inl hxAA))
        (Or.inl (Or.inr hb₂)) hadj with h | h
    · exact Set.disjoint_left.mp (hH.2.1 2 2) h.2 hb₂
    · exact Set.disjoint_left.mp (hH.2.1 0 0) hxAA h.1
  have hxAnf : xA ∉ f := by
    intro hx
    exact hfout xA hx (mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inl hxAA)⟩)
  have hb₂nf : b₂ ∉ f := by
    intro hx
    exact hfout b₂ hx (mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inr hb₂)⟩)
  have hxAother : ∀ z ∈ f, z ≠ f₁ → ¬ G.Adj xA z := by
    intro z hz hne hadj
    have hh := (hleft z hz).mp hadj
    rw [hf.2.1] at hh
    exact hne (Option.some_injective _ hh).symm
  have hb₂other : ∀ z ∈ f, z ≠ fn → ¬ G.Adj b₂ z := by
    intro z hz hne hadj
    exact hne (hBuniq 2 (by decide) z hz b₂ hb₂ hadj.symm)
  have hfull₂ : IsPathFrom G (xA :: (f ++ [b₂])) xA b₂ :=
    PathAttach.isPathFrom_cons_concat hf hxAf₁ hfnb₂.symm hxAb₂ (by
      intro h
      exact Set.disjoint_left.mp (hH.2.1 0 2) hxAA (h ▸ hb₂))
      hxAnf hb₂nf hxAother hb₂other
  have hAanti : ∀ (k : Fin 3), k ≠ 0 →
      ∀ z ∈ f, ∀ a ∈ A k, ¬ G.Adj z a := by
    intro k hk z hz a ha hadj
    have hk12 : k = 1 ∨ k = 2 := by
      rcases fin3_cases k with h | h | h
      · exact absurd h hk
      · exact Or.inl h
      · exact Or.inr h
    have hfirst : z = f₁ := by
      rcases hk12 with rfl | rfl
      · exact onlyFirstSeesA hH hF hf h2 hFeq (j := 2) (k := 1) (by decide)
          hb₂ hfnb₂ z hz a ha hadj
      · exact onlyFirstSeesA hH hF hf h2 hFeq (j := 1) (k := 2) (by decide)
          hxBB (by simpa [hfnEq] using hcomplete xB (Or.inl hxBB)) z hz a ha hadj
    subst z
    obtain ⟨R, b, hR⟩ := Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_A hH k ha
    have hxor : (G.Adj f₁ a ∨ G.Adj fn b) ∧ ¬ (G.Adj f₁ a ∧ G.Adj fn b) := by
      rcases hk12 with hk1 | hk2
      · subst k
        exact rungXor G A B C hG hH f f₁ fn xA b₂ hf hfull₂ heven
          (show (0 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 1 by decide)
          (show (2 : Fin 3) ≠ 1 by decide) hxAA hb₂ hfout
          (onlyFirstSeesA hH hF hf h2 hFeq (j := 2) (k := 1) (by decide) hb₂ hfnb₂)
          (hBuniq 1 (by decide)) hCnone hR
      · subst k
        exact rungXor G A B C hG hH f f₁ fn xA xB hf hfull heven
          (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
          (show (1 : Fin 3) ≠ 2 by decide) hxAA hxBB hfout
          (onlyFirstSeesA hH hF hf h2 hFeq (j := 1) (k := 2) (by decide) hxBB
            (by simpa [hfnEq] using hcomplete xB (Or.inl hxBB)))
          (hBuniq 2 (by decide)) hCnone hR
    have hfnb : G.Adj fn b := by
      rw [hfnEq]
      apply hcomplete b
      rcases hk12 with rfl | rfl
      · exact Or.inl hR.2.1
      · exact Or.inr hR.2.1
    exact hxor.2 ⟨hadj, hfnb⟩
  have hcrossSwap : ∀ z ∈ f.reverse, ∀ (k : Fin 3), k ≠ 0 →
      ∀ y ∈ B k ∪ A k ∪ C k, G.Adj z y → z = fn ∧ y ∈ B k := by
    intro z hz k hk y hy hadj
    rw [List.mem_reverse] at hz
    rcases hy with (hyB | hyA) | hyC
    · exact ⟨hBuniq k hk z hz y hyB hadj, hyB⟩
    · exact absurd hadj (hAanti k hk z hz y hyA)
    · exact absurd hadj (hCnone z hz k y hyC)
  have hnewRung :
      let B' := fun k : Fin 3 => if k = 0 then B k ∪ {fn} else B k
      let C' := fun k : Fin 3 => if k = 0 then C k ∪ {z : V | z ∈ f.reverse ∧ z ≠ fn} else C k
      ∃ q : List V, IsRungOfHyperprism G B' A C' 0 q ∧ ∀ z ∈ f.reverse, z ∈ q := by
    dsimp only
    have hrev : IsPathFrom G f.reverse fn f₁ := PathBasics.isPathFrom_reverse hf
    have hq : IsPathFrom G (f.reverse ++ [xA]) fn xA := by
      refine PathAttach.isPathFrom_concat hrev hxAf₁ ?_ ?_
      · intro hx
        rw [List.mem_reverse] at hx
        exact hxAnf hx
      · intro z hz hzf₁ hadj
        rw [List.mem_reverse] at hz
        exact hxAother z hz hzf₁ hadj
    refine ⟨f.reverse ++ [xA], ⟨fn, xA, by simp, hxAA, hq, ?_⟩, ?_⟩
    · intro z hz
      rw [PathBasics.mem_interior_iff_of_pathFrom hq] at hz
      rcases List.mem_append.mp hz.1 with hzf | hzx
      · exact Or.inr ⟨hzf, hz.2.1⟩
      · exact absurd (by simpa using hzx : z = xA) hz.2.2
    · intro z hz
      exact List.mem_append_left [xA] hz
  have hbigSwap := Workspace.ProofLemmas.HyperprismLocalEnlargementCore.leftExtensionAtZero
    G B A C (HyperprismTwoAttachments.isHyperprism_swap hH) f.reverse fn
    (by rw [List.mem_reverse]; exact PathBasics.getLast_mem hf.2.2)
    (PathBasics.path_nodup (PathBasics.isPathFrom_reverse hf).1)
    (by
      intro z hz
      rw [List.mem_reverse] at hz
      intro hmem
      exact hfout z hz (by rwa [hyperVerts_swap'] at hmem))
    (by
      intro k hk b hb
      rw [hfnEq]
      apply hcomplete b
      rcases fin3_cases k with h | h | h
      · exact absurd h hk
      · subst k; exact Or.inl hb
      · subst k; exact Or.inr hb)
    hcrossSwap hnewRung
  exact biggerHyperprism_swap hbigSwap

/-- The normalized even case after choosing the orientation in which the last path
vertex sees a vertex of `B 2`. -/
theorem evenOrientedAtZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) → x ∉ C k)
    (xA xB : V) (hxAA : xA ∈ A 0) (hxBB : xB ∈ B 1)
    (f : List V) (hfne : f ≠ []) (hfF : ∀ v ∈ f, v ∈ F)
    (hfull : IsPathFrom G (xA :: (f ++ [xB])) xA xB)
    (hleft : ∀ v ∈ f, G.Adj xA v ↔ f.head? = some v)
    (hright : ∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v)
    (hFeq : F = {v : V | v ∈ f}) (heven : Even f.length)
    (b₂ : V) (hb₂ : b₂ ∈ B 2) (hfnb₂ : G.Adj (f.getLast hfne) b₂) :
    BiggerHyperprism G A B C := by
  classical
  by_cases hcomplete : ∀ b ∈ B 1 ∪ B 2, G.Adj (f.getLast hfne) b
  · exact evenDirectAtZero G A B C F hG hH hF hNoC xA xB hxAA hxBB f hfne
      hfF hfull hleft hright hFeq heven hcomplete
  · obtain ⟨f₁, fn, hf, hxAf₁, hxBfn⟩ := interiorPathData hfne hfull hleft hright
    have hfnEq : fn = f.getLast hfne := by
      have h := hf.2.2
      rw [List.getLast?_eq_some_getLast hfne] at h
      exact (Option.some_injective _ h).symm
    have h2 : 2 ≤ f.length := by
      have hpos := List.length_pos_of_ne_nil hfne
      rcases heven with ⟨d, hd⟩
      omega
    have hfout : ∀ z ∈ f, z ∉ hyperVerts A B C := by
      intro z hz
      exact hF.1.2.1 (hfF z hz)
    have hCnone := noPathEdgeToC hfF hNoC
    have hfnxB : G.Adj fn xB := hxBfn.symm
    have hfnb₂' : G.Adj fn b₂ := by simpa [hfnEq] using hfnb₂
    have hBuniqOther : ∀ (k : Fin 3), k ≠ 0 →
        ∀ z ∈ f, ∀ b ∈ B k, G.Adj z b → z = fn := by
      intro k hk
      exact onlyLastSeesB hH hF hf h2 hFeq hk.symm hxAA hxAf₁.symm
    have hAuniq : ∀ (k : Fin 3),
        ∀ z ∈ f, ∀ a ∈ A k, G.Adj z a → z = f₁ := by
      intro k
      rcases fin3_cases k with rfl | rfl | rfl
      · exact onlyFirstSeesA hH hF hf h2 hFeq (j := 2) (k := 0) (by decide)
          hb₂ hfnb₂'
      · exact onlyFirstSeesA hH hF hf h2 hFeq (j := 2) (k := 1) (by decide)
          hb₂ hfnb₂'
      · exact onlyFirstSeesA hH hF hf h2 hFeq (j := 1) (k := 2) (by decide)
          hxBB hfnxB
    have hfullTo : ∀ {k : Fin 3} {b : V}, k ≠ 0 → b ∈ B k → G.Adj fn b →
        IsPathFrom G (xA :: (f ++ [b])) xA b := by
      intro k b hk hb hfn
      have hxAb : ¬ G.Adj xA b := by
        intro hadj
        rcases cross hH hk.symm (Or.inl (Or.inl hxAA)) (Or.inl (Or.inr hb)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.1 k k) h.2 hb
        · exact Set.disjoint_left.mp (hH.2.1 0 0) hxAA h.1
      have hxAnf : xA ∉ f := by
        intro hx
        exact hfout xA hx (mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inl hxAA)⟩)
      have hbnf : b ∉ f := by
        intro hx
        exact hfout b hx (mem_hyperVerts_iff.mpr ⟨k, Or.inl (Or.inr hb)⟩)
      refine PathAttach.isPathFrom_cons_concat hf hxAf₁ hfn.symm hxAb
        (by intro h; exact Set.disjoint_left.mp (hH.2.1 0 k) hxAA (h ▸ hb)) hxAnf hbnf ?_ ?_
      · intro z hz hne hadj
        have hh := (hleft z hz).mp hadj
        rw [hf.2.1] at hh
        exact hne (Option.some_injective _ hh).symm
      · intro z hz hne hadj
        exact hne (hBuniqOther k hk z hz b hb hadj.symm)
    push_neg at hcomplete
    obtain ⟨bBad, hbBad, hfnbBad⟩ := hcomplete
    obtain ⟨kBad, hkBad, hbBadK⟩ : ∃ k : Fin 3, k ≠ 0 ∧ bBad ∈ B k := by
      rcases hbBad with hbBad | hbBad
      · exact ⟨1, by decide, hbBad⟩
      · exact ⟨2, by decide, hbBad⟩
    obtain ⟨RBad, aBad, hRBad⟩ :=
      Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_B hH kBad hbBadK
    have hf₁aBad : G.Adj f₁ aBad := by
      have hxor : (G.Adj f₁ aBad ∨ G.Adj fn bBad) ∧
          ¬ (G.Adj f₁ aBad ∧ G.Adj fn bBad) := by
        rcases fin3_cases kBad with rfl | rfl | rfl
        · exact absurd rfl hkBad
        · exact rungXor G A B C hG hH f f₁ fn xA b₂ hf
            (hfullTo (show (2 : Fin 3) ≠ 0 by decide) hb₂ hfnb₂') heven
            (show (0 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 1 by decide)
            (show (2 : Fin 3) ≠ 1 by decide) hxAA hb₂ hfout (hAuniq 1)
            (hBuniqOther 1 (by decide)) hCnone hRBad
        · exact rungXor G A B C hG hH f f₁ fn xA xB hf hfull heven
            (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
            (show (1 : Fin 3) ≠ 2 by decide) hxAA hxBB hfout (hAuniq 2)
            (hBuniqOther 2 (by decide)) hCnone hRBad
      rcases hxor.1 with h | h
      · exact h
      · exact absurd (by simpa [hfnEq] using h) hfnbBad
    have hBuniq : ∀ (k : Fin 3),
        ∀ z ∈ f, ∀ b ∈ B k, G.Adj z b → z = fn := by
      intro k
      by_cases hk : k = 0
      · subst k
        exact onlyLastSeesB hH hF hf h2 hFeq hkBad hRBad.1 hf₁aBad
      · exact hBuniqOther k hk
    have hfullBetween : ∀ {r s : Fin 3} {a b : V}, r ≠ s →
        a ∈ A r → b ∈ B s → G.Adj f₁ a → G.Adj fn b →
        IsPathFrom G (a :: (f ++ [b])) a b := by
      intro r s a b hrs ha hb hf₁a hfnb
      have hab : ¬ G.Adj a b := by
        intro hadj
        rcases cross hH hrs (Or.inl (Or.inl ha)) (Or.inl (Or.inr hb)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.1 s s) h.2 hb
        · exact Set.disjoint_left.mp (hH.2.1 r r) ha h.1
      have hanf : a ∉ f := by
        intro hmem
        exact hfout a hmem (mem_hyperVerts_iff.mpr ⟨r, Or.inl (Or.inl ha)⟩)
      have hbnf : b ∉ f := by
        intro hmem
        exact hfout b hmem (mem_hyperVerts_iff.mpr ⟨s, Or.inl (Or.inr hb)⟩)
      refine PathAttach.isPathFrom_cons_concat hf hf₁a.symm hfnb.symm hab
        (by intro h; exact Set.disjoint_left.mp (hH.2.1 r s) ha (h ▸ hb)) hanf hbnf ?_ ?_
      · intro z hz hne hadj
        exact hne (hAuniq r z hz a ha hadj.symm)
      · intro z hz hne hadj
        exact hne (hBuniq s z hz b hb hadj.symm)
    let P : Fin 3 → Set V := fun k => {a ∈ A k | G.Adj f₁ a}
    let Q : Fin 3 → Set V := fun k => {b ∈ B k | ¬ G.Adj fn b}
    have hs : IsRungSplit G A B C P Q := by
      refine ⟨fun k a ha => ha.1, fun k b hb => hb.1, ?_⟩
      intro k R a b hR
      have hxor : (G.Adj f₁ a ∨ G.Adj fn b) ∧ ¬ (G.Adj f₁ a ∧ G.Adj fn b) := by
        rcases fin3_cases k with rfl | rfl | rfl
        · rcases fin3_cases kBad with rfl | rfl | rfl
          · exact absurd rfl hkBad
          · exact rungXor G A B C hG hH f f₁ fn aBad b₂ hf
              (hfullBetween (show (1 : Fin 3) ≠ 2 by decide) hRBad.1 hb₂ hf₁aBad hfnb₂')
              heven (show (1 : Fin 3) ≠ 2 by decide)
              (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide)
              hRBad.1 hb₂ hfout (hAuniq 0) (hBuniq 0) hCnone hR
          · exact rungXor G A B C hG hH f f₁ fn aBad xB hf
              (hfullBetween (show (2 : Fin 3) ≠ 1 by decide) hRBad.1 hxBB hf₁aBad hfnxB)
              heven (show (2 : Fin 3) ≠ 1 by decide)
              (show (2 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 0 by decide)
              hRBad.1 hxBB hfout (hAuniq 0) (hBuniq 0) hCnone hR
        · exact rungXor G A B C hG hH f f₁ fn xA b₂ hf
            (hfullTo (show (2 : Fin 3) ≠ 0 by decide) hb₂ hfnb₂') heven
            (show (0 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 1 by decide)
            (show (2 : Fin 3) ≠ 1 by decide) hxAA hb₂ hfout (hAuniq 1)
            (hBuniq 1) hCnone hR
        · exact rungXor G A B C hG hH f f₁ fn xA xB hf hfull heven
            (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
            (show (1 : Fin 3) ≠ 2 by decide) hxAA hxBB hfout (hAuniq 2)
            (hBuniq 2) hCnone hR
      rcases hxor.1 with ha | hb
      · exact Or.inl ⟨⟨hR.1, ha⟩, ⟨hR.2.1, fun hnb => hxor.2 ⟨ha, hnb⟩⟩⟩
      · exact Or.inr ⟨fun ha => hxor.2 ⟨ha.2, hb⟩, fun hbQ => hbQ.2 hb⟩
    have hxAP : xA ∈ P 0 := ⟨hxAA, hxAf₁.symm⟩
    have haBadP : aBad ∈ P kBad := ⟨hRBad.1, hf₁aBad⟩
    have hbBadQ : bBad ∈ Q kBad := ⟨hbBadK, by simpa [hfnEq] using hfnbBad⟩
    obtain ⟨R₀, b₀, hR₀⟩ :=
      Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_A hH 0 hxAA
    have hb₀Q : b₀ ∈ Q 0 := by
      rcases hs.dich 0 R₀ xA b₀ hR₀ with h | h
      · exact h.2
      · exact absurd hxAP h.1
    obtain ⟨R₁, a₁, hR₁⟩ :=
      Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_B hH 1 hxBB
    have ha₁D : a₁ ∈ A 1 \ P 1 := by
      rcases hs.dich 1 R₁ a₁ xB hR₁ with h | h
      · exact absurd hfnxB h.2.2
      · exact ⟨hR₁.1, h.1⟩
    obtain ⟨R₂, a₂, hR₂⟩ :=
      Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_B hH 2 hb₂
    have ha₂D : a₂ ∈ A 2 \ P 2 := by
      rcases hs.dich 2 R₂ a₂ b₂ hR₂ with h | h
      · exact absurd hfnb₂' h.2.2
      · exact ⟨hR₂.1, h.1⟩
    have hDoubleSupport : ∀ i : Fin 3,
        ∃ j : Fin 3, j ≠ i ∧ (A j \ P j).Nonempty := by
      intro i
      rcases fin3_cases i with rfl | rfl | rfl
      · exact ⟨1, by decide, a₁, ha₁D⟩
      · exact ⟨2, by decide, a₂, ha₂D⟩
      · exact ⟨1, by decide, a₁, ha₁D⟩
    have hPrimeSupport : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (Q j).Nonempty := by
      intro i
      by_cases hi : i = 0
      · subst i
        exact ⟨kBad, hkBad, bBad, hbBadQ⟩
      · exact ⟨0, Ne.symm hi, b₀, hb₀Q⟩
    have hAedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ a ∈ A i,
        G.Adj z a → z = f₁ ∧ a ∈ P i := by
      intro i z hz a ha hadj
      have hz1 := hAuniq i z hz a ha hadj
      exact ⟨hz1, ha, by simpa [hz1] using hadj⟩
    have hBedges : ∀ (i : Fin 3) (z : V), z ∈ f → ∀ b ∈ B i,
        G.Adj z b → z = fn ∧ b ∉ Q i := by
      intro i z hz b hb hadj
      have hzn := hBuniq i z hz b hb hadj
      refine ⟨hzn, ?_⟩
      intro hbQ
      exact hbQ.2 (by simpa [hzn] using hadj)
    have hPadj : ∀ (i : Fin 3), ∀ a ∈ P i, G.Adj f₁ a := fun i a ha => ha.2
    have hQadj : ∀ (i : Fin 3), ∀ b ∈ B i, b ∉ Q i → G.Adj fn b := by
      intro i b hb hbn
      by_contra hcon
      exact hbn ⟨hb, hcon⟩
    obtain ⟨hPA, hQB⟩ := evenSplitCompleteness G A B C P Q hG hH hs
      hDoubleSupport hPrimeSupport hf heven hfout hAedges hBedges hPadj hQadj hCnone
    have hP0 : (P 0).Nonempty := ⟨xA, hxAP⟩
    have hP12 : (P 1 ∪ P 2).Nonempty := by
      refine ⟨aBad, ?_⟩
      rcases fin3_cases kBad with rfl | rfl | rfl
      · exact absurd rfl hkBad
      · exact Or.inl haBadP
      · exact Or.inr haBadP
    have hD : ((A 0 \ P 0) ∪ (A 1 \ P 1) ∪ (A 2 \ P 2)).Nonempty :=
      ⟨a₁, Or.inl (Or.inr ha₁D)⟩
    let Areg := regroupA A P
    let Breg := regroupB B Q
    let Creg := regroupC G A B C P Q
    have hHreg : IsHyperprism G Areg Breg Creg :=
      regroupIsHyperprism G A B C P Q hG hH hs hPA hQB hP0 hP12 hD
    have hf₁CompleteReg : ∀ (r : Fin 3), r ≠ 2 → ∀ a ∈ Areg r, G.Adj f₁ a := by
      intro r hr a ha
      rcases fin3_cases r with rfl | rfl | rfl
      · exact (by simpa [Areg, regroupA] using ha : a ∈ P 0).2
      · rcases (by simpa [Areg, regroupA] using ha : a ∈ P 1 ∪ P 2) with ha | ha
        · exact ha.2
        · exact ha.2
      · exact absurd rfl hr
    have hcrossReg : ∀ z ∈ f, ∀ (r : Fin 3), r ≠ 2 →
        ∀ y ∈ Areg r ∪ Breg r ∪ Creg r, G.Adj z y →
          z = f₁ ∧ y ∈ Areg r := by
      intro z hz r hr y hy hadj
      rcases fin3_cases r with rfl | rfl | rfl
      · simp only [Areg, Breg, Creg, regroupA, regroupB, regroupC, if_true,
          Set.mem_union] at hy ⊢
        rcases hy with (hyA | hyB) | hyC
        · have hh := hAedges 0 z hz y (hs.PA 0 hyA) hadj
          exact ⟨hh.1, hh.2⟩
        · exact absurd hyB (hBedges 0 z hz y (hs.QB 0 hyB) hadj).2
        · exact absurd hadj (hCnone z hz 0 y (Cp_subset_C 0 hyC))
      · simp only [Areg, Breg, Creg, regroupA, regroupB, regroupC, if_false,
          if_true, Set.mem_union] at hy ⊢
        rcases hy with ((hyA | hyA) | (hyB | hyB)) | (hyC | hyC)
        · have hh := hAedges 1 z hz y (hs.PA 1 hyA) hadj
          exact ⟨hh.1, Or.inl hh.2⟩
        · have hh := hAedges 2 z hz y (hs.PA 2 hyA) hadj
          exact ⟨hh.1, Or.inr hh.2⟩
        · exact absurd hyB (hBedges 1 z hz y (hs.QB 1 hyB) hadj).2
        · exact absurd hyB (hBedges 2 z hz y (hs.QB 2 hyB) hadj).2
        · exact absurd hadj (hCnone z hz 1 y (Cp_subset_C 1 hyC))
        · exact absurd hadj (hCnone z hz 2 y (Cp_subset_C 2 hyC))
      · exact absurd rfl hr
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    have hHperm : IsHyperprism G (fun r => Areg (σ r)) (fun r => Breg (σ r))
        (fun r => Creg (σ r)) :=
      HyperprismTwoAttachments.isHyperprism_perm hG hHreg σ
    have hb₂Reg : b₂ ∈ Breg 2 := by
      have hbNotQ : b₂ ∉ Q 2 := fun h => h.2 hfnb₂'
      simp [Breg, regroupB, hb₂, hbNotQ]
    have hb₂nf : b₂ ∉ f := by
      intro hmem
      exact hfout b₂ hmem (mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inr hb₂)⟩)
    have hq : IsPathFrom G (f ++ [b₂]) f₁ b₂ := by
      refine PathAttach.isPathFrom_concat hf hfnb₂'.symm hb₂nf ?_
      intro z hz hne hadj
      exact hne (hBuniq 2 z hz b₂ hb₂ hadj.symm)
    have hnewRung :
        let Ap := fun r : Fin 3 => if r = 0 then Areg (σ r) ∪ {f₁} else Areg (σ r)
        let Cp' := fun r : Fin 3 =>
          if r = 0 then Creg (σ r) ∪ {z : V | z ∈ f ∧ z ≠ f₁} else Creg (σ r)
        ∃ q : List V, IsRungOfHyperprism G Ap (fun r => Breg (σ r)) Cp' 0 q ∧
          ∀ z ∈ f, z ∈ q := by
      dsimp only
      refine ⟨f ++ [b₂], ⟨f₁, b₂, ?_, ?_, hq, ?_⟩, ?_⟩
      · simp [σ]
      · simpa [σ] using hb₂Reg
      · intro z hz
        rw [PathBasics.mem_interior_iff_of_pathFrom hq] at hz
        have hzf : z ∈ f := by
          rcases List.mem_append.mp hz.1 with h | h
          · exact h
          · exact absurd (by simpa using h : z = b₂) hz.2.2
        exact Or.inr ⟨hzf, hz.2.1⟩
      · intro z hz
        exact List.mem_append_left [b₂] hz
    have hbigPerm := Workspace.ProofLemmas.HyperprismLocalEnlargementCore.leftExtensionAtZero
      G (fun r => Areg (σ r)) (fun r => Breg (σ r)) (fun r => Creg (σ r))
      hHperm f f₁ (PathBasics.head_mem hf.2.1) (PathBasics.path_nodup hf.1)
      (by
        intro z hz hmem
        have hOld : z ∈ hyperVerts A B C := by
          rw [hyperVerts_perm, hyperVerts_regroup hH hs] at hmem
          exact hmem
        exact hfout z hz hOld)
      (by
        intro r hr a ha
        rcases fin3_cases r with rfl | rfl | rfl
        · exact absurd rfl hr
        · exact hf₁CompleteReg 1 (by decide) a (by simpa [σ] using ha)
        · exact hf₁CompleteReg 0 (by decide) a (by simpa [σ] using ha))
      (by
        intro z hz r hr y hy hadj
        rcases fin3_cases r with rfl | rfl | rfl
        · exact absurd rfl hr
        · have hh := hcrossReg z hz 1 (by decide) y (by simpa [σ] using hy) hadj
          exact ⟨hh.1, by simpa [σ] using hh.2⟩
        · have hh := hcrossReg z hz 0 (by decide) y (by simpa [σ] using hy) hadj
          exact ⟨hh.1, by simpa [σ] using hh.2⟩)
      hnewRung
    have hbigReg : BiggerHyperprism G Areg Breg Creg := biggerHyperprism_perm hbigPerm
    obtain ⟨Anew, Bnew, Cnew, hHnew, hstrict⟩ := hbigReg
    refine ⟨Anew, Bnew, Cnew, hHnew, ?_⟩
    rwa [hyperVerts_regroup hH hs] at hstrict

/-- The even attachment-path construction with its two attachment indices normalized to
zero and one. -/
theorem evenAtZeroOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) → x ∉ C k)
    (xA xB : V) (hxAA : xA ∈ A 0) (hxBB : xB ∈ B 1)
    (f : List V) (hfne : f ≠ []) (hfF : ∀ v ∈ f, v ∈ F)
    (hfull : IsPathFrom G (xA :: (f ++ [xB])) xA xB)
    (hleft : ∀ v ∈ f, G.Adj xA v ↔ f.head? = some v)
    (hright : ∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v)
    (hFeq : F = {v : V | v ∈ f}) (heven : Even f.length) :
    BiggerHyperprism G A B C := by
  classical
  obtain ⟨f₁, fn, hf, hxAf₁, hxBfn⟩ := interiorPathData hfne hfull hleft hright
  have h2 : 2 ≤ f.length := by
    have hpos := List.length_pos_of_ne_nil hfne
    rcases heven with ⟨d, hd⟩
    omega
  have hfout : ∀ z ∈ f, z ∉ hyperVerts A B C := by
    intro z hz
    exact hF.1.2.1 (hfF z hz)
  have hCnone := noPathEdgeToC hfF hNoC
  have hexR₂ : ∃ (R : List V) (a b : V), IsRungFrom G A B C 2 R a b :=
    exists_rung hH 2
  obtain ⟨R₂, a₂, b₂, hR₂⟩ := hexR₂
  have hxor := rungXor G A B C hG hH f f₁ fn xA xB hf hfull heven
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) hxAA hxBB hfout
    (onlyFirstSeesA hH hF hf h2 hFeq (j := 1) (k := 2) (by decide)
      hxBB hxBfn.symm)
    (onlyLastSeesB hH hF hf h2 hFeq (i := 0) (k := 2) (by decide)
      hxAA hxAf₁.symm)
    hCnone hR₂
  rcases hxor.1 with hf₁a₂ | hfnb₂
  · let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    have hHswap := HyperprismTwoAttachments.isHyperprism_swap hH
    have hH' := HyperprismTwoAttachments.isHyperprism_perm hG hHswap σ
    have hF' := minimalBad_perm σ (minimalBad_swap hF)
    have hNoC' : ∀ (k : Fin 3) (x : V),
        x ∈ attachments G F
          (hyperVerts (fun r => B (σ r)) (fun r => A (σ r)) (fun r => C (σ r))) →
        x ∉ C (σ k) := by
      intro k x hx
      apply hNoC (σ k) x
      rw [hyperVerts_perm, hyperVerts_swap'] at hx
      exact hx
    have hrevne : f.reverse ≠ [] := by simpa using hfne
    have hfullrev : IsPathFrom G (xB :: (f.reverse ++ [xA])) xB xA := by
      simpa using PathBasics.isPathFrom_reverse hfull
    have hleftrev : ∀ v ∈ f.reverse,
        G.Adj xB v ↔ f.reverse.head? = some v := by
      intro v hv
      rw [List.mem_reverse] at hv
      simpa using hright v hv
    have hrightrev : ∀ v ∈ f.reverse,
        G.Adj xA v ↔ f.reverse.getLast? = some v := by
      intro v hv
      rw [List.mem_reverse] at hv
      simpa using hleft v hv
    have hFeqrev : F = {v : V | v ∈ f.reverse} := by
      rw [hFeq]
      ext v
      simp
    have hlastRev : f.reverse.getLast hrevne = f₁ := by
      have hh := hf.2.1
      rw [← List.getLast?_reverse, List.getLast?_eq_some_getLast hrevne] at hh
      exact Option.some_injective _ hh
    have hbig := evenOrientedAtZero G (fun r => B (σ r)) (fun r => A (σ r))
      (fun r => C (σ r)) F hG hH' hF' hNoC' xB xA
      (by simpa [σ] using hxBB) (by simpa [σ] using hxAA) f.reverse hrevne
      (by intro v hv; rw [List.mem_reverse] at hv; exact hfF v hv)
      hfullrev hleftrev hrightrev hFeqrev (by simpa using heven) a₂
      (by simpa [σ] using hR₂.1) (by simpa [hlastRev] using hf₁a₂)
    exact biggerHyperprism_swap (biggerHyperprism_perm hbig)
  · have hfnEq : fn = f.getLast hfne := by
      have h := hf.2.2
      rw [List.getLast?_eq_some_getLast hfne] at h
      exact (Option.some_injective _ h).symm
    exact evenOrientedAtZero G A B C F hG hH hF hNoC xA xB hxAA hxBB f hfne
      hfF hfull hleft hright hFeq heven b₂ hR₂.2.1 (by simpa [← hfnEq] using hfnb₂)

/-- The even attachment-path enlargement, with arbitrary distinct attachment indices. -/
theorem evenAttachmentPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ x ∈ attachments G F (hyperVerts A B C), ∀ k : Fin 3, x ∉ C k)
    (i j : Fin 3) (hij : i ≠ j) (xA xB : V)
    (_hxAatt : xA ∈ attachments G F (hyperVerts A B C)) (hxAA : xA ∈ A i)
    (_hxBatt : xB ∈ attachments G F (hyperVerts A B C)) (hxBB : xB ∈ B j)
    (hPath : ∃ f : List V,
      f ≠ [] ∧ (∀ v ∈ f, v ∈ F) ∧
      IsPathFrom G (xA :: (f ++ [xB])) xA xB ∧
      (∀ v ∈ f, G.Adj xA v ↔ f.head? = some v) ∧
      (∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v) ∧
      F = {v : V | v ∈ f} ∧ Even f.length) :
    BiggerHyperprism G A B C := by
  classical
  obtain ⟨f, hfne, hfF, hfull, hleft, hright, hFeq, heven⟩ := hPath
  have hex : ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
    rcases fin3_cases i with rfl | rfl | rfl <;>
      rcases fin3_cases j with rfl | rfl | rfl
    all_goals try { exact absurd rfl hij }
    all_goals decide
  obtain ⟨σ, hσ0, hσ1⟩ := hex
  have hH' := HyperprismTwoAttachments.isHyperprism_perm hG hH σ
  have hF' := minimalBad_perm σ hF
  have hNoC' : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F
        (hyperVerts (fun r => A (σ r)) (fun r => B (σ r)) (fun r => C (σ r))) →
      x ∉ C (σ k) := by
    intro k x hx
    apply hNoC x (by rwa [hyperVerts_perm] at hx) (σ k)
  have hbig := evenAtZeroOne G (fun r => A (σ r)) (fun r => B (σ r))
    (fun r => C (σ r)) F hG hH' hF' hNoC' xA xB
    (by simpa [hσ0] using hxAA) (by simpa [hσ1] using hxBB) f hfne hfF hfull
    hleft hright hFeq heven
  exact biggerHyperprism_perm hbig

end Workspace.ProofLemmas.HyperprismLocalEnlargementEven
