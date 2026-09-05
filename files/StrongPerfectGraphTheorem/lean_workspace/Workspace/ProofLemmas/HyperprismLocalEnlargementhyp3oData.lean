import Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oSplit
import Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality
import Workspace.ProofLemmas.HyperprismLocalEnlargementRegroup
import Workspace.Statements.S10.Thm_10_5

/-!
# The odd block of claim (2) of 10.6 — producing the extension data
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oData

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.HyperprismSplit
open Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality
open Workspace.ProofLemmas.HyperprismLocalEnlargementRegroup
open Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oCore
open Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oSplit
open Workspace.ProofLemmas.Thm106Assembly

/-- A local copy of the monotonicity of `LocalForHyperprism` (the version in
`HyperprismLocalEnlargementMinimality` is private). -/
theorem local_mono
    {V : Type*} {A B C : Fin 3 → Set V} {X Y : Set V}
    (hXY : X ⊆ Y) (hY : LocalForHyperprism A B C Y) : LocalForHyperprism A B C X := by
  rcases hY with h | h | h | h | h
  · exact Or.inl (hXY.trans h)
  · exact Or.inr (Or.inl (hXY.trans h))
  · exact Or.inr (Or.inr (Or.inl (hXY.trans h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hXY.trans h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hXY.trans h))))

/-- The boilerplate part of the conclusion of the odd block: the outside path is always the
whole of `f`, and the new row-zero rung is always `f` itself. -/
theorem packageData
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C A₀ B₀ C₀ : Fin 3 → Set V)
    {f : List V} {f₁ fn : V}
    (hH₀ : IsHyperprism G A₀ B₀ C₀)
    (hverts : hyperVerts A₀ B₀ C₀ = hyperVerts A B C)
    (hf : IsPathFrom G f f₁ fn) (hne : f₁ ≠ fn)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hu : ∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A₀ k, G.Adj f₁ a)
    (hv : ∀ (k : Fin 3), k ≠ 0 → ∀ b ∈ B₀ k, G.Adj fn b)
    (hcr : ∀ z ∈ f, ∀ (k : Fin 3), k ≠ 0 → ∀ y ∈ A₀ k ∪ B₀ k ∪ C₀ k, G.Adj z y →
      (z = f₁ ∧ y ∈ A₀ k) ∨ (z = fn ∧ y ∈ B₀ k)) :
    ∃ (A' B' C' : Fin 3 → Set V) (p : List V) (u v : V),
      IsHyperprism G A' B' C' ∧
      hyperVerts A' B' C' = hyperVerts A B C ∧
      u ∈ p ∧ v ∈ p ∧ u ≠ v ∧ p.Nodup ∧
      (∀ z ∈ p, z ∉ hyperVerts A' B' C') ∧
      (∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A' k, G.Adj u a) ∧
      (∀ (k : Fin 3), k ≠ 0 → ∀ b ∈ B' k, G.Adj v b) ∧
      (∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
        ∀ y ∈ A' k ∪ B' k ∪ C' k, G.Adj z y →
          (z = u ∧ y ∈ A' k) ∨ (z = v ∧ y ∈ B' k)) ∧
      (let A'' := fun k : Fin 3 => if k = 0 then A' k ∪ {u} else A' k
       let B'' := fun k : Fin 3 => if k = 0 then B' k ∪ {v} else B' k
       let C'' := fun k : Fin 3 => if k = 0 then
         C' k ∪ {z : V | z ∈ p ∧ z ≠ u ∧ z ≠ v} else C' k
       ∃ q : List V, IsRungOfHyperprism G A'' B'' C'' 0 q ∧ ∀ z ∈ p, z ∈ q) := by
  refine ⟨A₀, B₀, C₀, f, f₁, fn, hH₀, hverts, PathBasics.head_mem hf.2.1,
    PathBasics.getLast_mem hf.2.2, hne, PathBasics.path_nodup hf.1, ?_, hu, hv, hcr, ?_⟩
  · intro z hz
    rw [hverts]
    exact hfout z hz
  · dsimp only
    refine ⟨f, ⟨f₁, fn, ?_, ?_, hf, ?_⟩, fun z hz => hz⟩
    · simp
    · simp
    · intro w hw
      rw [PathBasics.mem_interior_iff_of_pathFrom hf] at hw
      simp only [if_pos rfl, Set.mem_union, Set.mem_setOf_eq]
      exact Or.inr ⟨hw.1, hw.2.1, hw.2.2⟩


/-- PAPER (10.6, odd case, printed p. 62), the whole paragraph beginning *"Now assume `n` is
odd"* and ending *"and similarly `B'ᵢ` is complete to `B''ᵢ`"*, with the two attachment
indices normalised to `0` and `1`.  The conclusion is the data feeding the final displayed
construction. -/
theorem oddDataAtZeroOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hK4 : NoK4 G)
    (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) → x ∉ C k)
    {xA xB : V} (hxAA : xA ∈ A 0) (hxBB : xB ∈ B 1)
    (f : List V) (hfne : f ≠ []) (hfF : ∀ v ∈ f, v ∈ F)
    (hfull : IsPathFrom G (xA :: (f ++ [xB])) xA xB)
    (hleft : ∀ v ∈ f, G.Adj xA v ↔ f.head? = some v)
    (hright : ∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v)
    (hFeq : F = {v : V | v ∈ f}) (hodd : Odd f.length) :
    ∃ (A₀ B₀ C₀ : Fin 3 → Set V) (p : List V) (u v : V),
      IsHyperprism G A₀ B₀ C₀ ∧
      hyperVerts A₀ B₀ C₀ = hyperVerts A B C ∧
      u ∈ p ∧ v ∈ p ∧ u ≠ v ∧ p.Nodup ∧
      (∀ z ∈ p, z ∉ hyperVerts A₀ B₀ C₀) ∧
      (∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A₀ k, G.Adj u a) ∧
      (∀ (k : Fin 3), k ≠ 0 → ∀ b ∈ B₀ k, G.Adj v b) ∧
      (∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
        ∀ y ∈ A₀ k ∪ B₀ k ∪ C₀ k, G.Adj z y →
          (z = u ∧ y ∈ A₀ k) ∨ (z = v ∧ y ∈ B₀ k)) ∧
      (let A' := fun k : Fin 3 => if k = 0 then A₀ k ∪ {u} else A₀ k
       let B' := fun k : Fin 3 => if k = 0 then B₀ k ∪ {v} else B₀ k
       let C' := fun k : Fin 3 => if k = 0 then
         C₀ k ∪ {z : V | z ∈ p ∧ z ≠ u ∧ z ≠ v} else C₀ k
       ∃ q : List V, IsRungOfHyperprism G A' B' C' 0 q ∧ ∀ z ∈ p, z ∈ q) := by
  classical
  obtain ⟨f₁, fn, hf, hxAf₁, hxBfn⟩ := interiorPathData hfne hfull hleft hright
  have hf₁f : f₁ ∈ f := PathBasics.head_mem hf.2.1
  have hfnf : fn ∈ f := PathBasics.getLast_mem hf.2.2
  have hfout : ∀ z ∈ f, z ∉ hyperVerts A B C := fun z hz => hF.1.2.1 (hfF z hz)
  have hCnone := noPathEdgeToC hfF hNoC
  have hleft' : ∀ z ∈ f, G.Adj xA z → z = f₁ := by
    intro z hz hadj
    have h := (hleft z hz).mp hadj
    rw [hf.2.1] at h
    exact (Option.some_injective _ h).symm
  have hright' : ∀ z ∈ f, G.Adj xB z → z = fn := by
    intro z hz hadj
    have h := (hright z hz).mp hadj
    rw [hf.2.2] at h
    exact (Option.some_injective _ h).symm
  obtain ⟨R₀, b₀, hR₀⟩ :=
    Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_A hH 0 hxAA
  obtain ⟨R₁, a₁, hR₁⟩ :=
    Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_B hH 1 hxBB
  have hb₀ : b₀ ∈ B 0 := hR₀.2.1
  have ha₁ : a₁ ∈ A 1 := hR₁.1
  obtain ⟨zb, hzbf, hzbb⟩ := endAttachmentB hG hH hf hodd hfout
    (show (0 : Fin 3) ≠ 1 by decide) hxAA hxBB hR₀ hxAf₁ hxBfn.symm hleft' hright' hCnone
  obtain ⟨za, hzaf, hzaa⟩ := endAttachmentA hG hH hf hodd hfout
    (show (0 : Fin 3) ≠ 1 by decide) hxAA hxBB hR₁ hxAf₁ hxBfn.symm hleft' hright' hCnone
  -- *"by 10.5 we may assume that `n > 1`"*
  have h2 : 2 ≤ f.length := by
    by_contra hcon
    have hlen1 : f.length = 1 := by
      have := PathBasics.path_length_pos hf.1
      omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen1
    subst hc
    have hcf₁ : c = f₁ := by simpa using hf.2.1
    have hcfn : c = fn := by simpa using hf.2.2
    have hzac : za = c := by simpa using hzaf
    have hzbc : zb = c := by simpa using hzbf
    obtain ⟨R₂, a₂, b₂, hR₂⟩ := exists_rung hH 2
    set aa : Fin 3 → V := ![xA, a₁, a₂] with haa
    set bb : Fin 3 → V := ![b₀, xB, b₂] with hbb
    set RR : Fin 3 → List V := ![R₀, R₁, R₂] with hRR
    have hRall : ∀ i : Fin 3, IsRungFrom G A B C i (RR i) (aa i) (bb i) := by
      intro i
      fin_cases i
      · simpa [aa, bb, RR] using hR₀
      · simpa [aa, bb, RR] using hR₁
      · simpa [aa, bb, RR] using hR₂
    have hprism : IsEvenPrism G aa bb (RR 0) (RR 1) (RR 2) := rungs_isEvenPrism hG hH hRall
    have hxAne : xA ≠ a₁ := fun h =>
      Set.disjoint_left.mp (hH.2.2.2.2.1 0 1 (by decide)) hxAA (h ▸ ha₁)
    have hb₀ne : b₀ ≠ xB := fun h =>
      Set.disjoint_left.mp (hH.2.2.2.2.2.1 0 1 (by decide)) hb₀ (h ▸ hxBB)
    have hmajor : MajorForPrism G aa bb c := by
      constructor
      · have hsub : ({xA, a₁} : Set V) ⊆ ({aa 0, aa 1, aa 2} : Set V) ∩ G.neighborSet c := by
          rintro x (rfl | rfl)
          · refine ⟨Or.inl rfl, ?_⟩
            simp only [SimpleGraph.mem_neighborSet, hcf₁]
            exact hxAf₁.symm
          · refine ⟨Or.inr (Or.inl rfl), ?_⟩
            simp only [SimpleGraph.mem_neighborSet, ← hzac]
            exact hzaa
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rwa [Set.ncard_pair hxAne] at this
      · have hsub : ({b₀, xB} : Set V) ⊆ ({bb 0, bb 1, bb 2} : Set V) ∩ G.neighborSet c := by
          rintro x (rfl | rfl)
          · refine ⟨Or.inl rfl, ?_⟩
            simp only [SimpleGraph.mem_neighborSet, ← hzbc]
            exact hzbb
          · refine ⟨Or.inr (Or.inl rfl), ?_⟩
            simp only [SimpleGraph.mem_neighborSet, hcfn]
            exact hxBfn.symm
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rwa [Set.ncard_pair hb₀ne] at this
    exact hNoBalanced
      (Workspace.Statements.S10.SPGT.thm_10_5 G hG hK4 aa bb (RR 0) (RR 1) (RR 2) c
        hprism hmajor)
  have hf₁ne : f₁ ≠ fn := PathBasics.isPathFrom_ends_ne hf (by
    simp only [pathLength]; omega)
  -- *"From the minimality of `F`, one of `b₁, a₂` is adjacent to `f₁` and the other to `fₙ`"*
  have hpairF₁ : ∀ w w' : V, w ∈ f → G.Adj w a₁ → w' ∈ f → G.Adj w' b₀ →
      w = f₁ ∨ w' = f₁ := by
    intro w w' hw hwa hw' hw'b
    by_contra hcon
    push_neg at hcon
    refine HyperprismTwoAttachments.not_local_pair hH (show (1 : Fin 3) ≠ 0 by decide)
      ha₁ hb₀ (local_mono ?_ (localAfterFirst hF hf h2 hFeq))
    rintro y (rfl | rfl)
    · exact ⟨mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inl ha₁)⟩, w,
        ⟨by rw [hFeq]; exact hw, by simpa using hcon.1⟩, hwa.symm⟩
    · exact ⟨mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inr hb₀)⟩, w',
        ⟨by rw [hFeq]; exact hw', by simpa using hcon.2⟩, hw'b.symm⟩
  have hpairFn : ∀ w w' : V, w ∈ f → G.Adj w a₁ → w' ∈ f → G.Adj w' b₀ →
      w = fn ∨ w' = fn := by
    intro w w' hw hwa hw' hw'b
    by_contra hcon
    push_neg at hcon
    refine HyperprismTwoAttachments.not_local_pair hH (show (1 : Fin 3) ≠ 0 by decide)
      ha₁ hb₀ (local_mono ?_ (localBeforeLast hF hf h2 hFeq))
    rintro y (rfl | rfl)
    · exact ⟨mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inl ha₁)⟩, w,
        ⟨by rw [hFeq]; exact hw, by simpa using hcon.1⟩, hwa.symm⟩
    · exact ⟨mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inr hb₀)⟩, w',
        ⟨by rw [hFeq]; exact hw', by simpa using hcon.2⟩, hw'b.symm⟩
  -- *"This proves that `fₙ` is adjacent to `b₁` and `f₁` to `a₂`."*
  have hf₁a₁ : G.Adj f₁ a₁ ∧ G.Adj fn b₀ := by
    rcases hpairF₁ za zb hzaf hzaa hzbf hzbb with hza | hzb
    · rcases hpairFn za zb hzaf hzaa hzbf hzbb with hza' | hzb'
      · exact absurd (hza ▸ hza' : f₁ = fn) hf₁ne
      · exact ⟨hza ▸ hzaa, hzb' ▸ hzbb⟩
    · -- the excluded case: `f₁` sees `b₀` and `fₙ` sees `a₁`
      exfalso
      rcases hpairFn za zb hzaf hzaa hzbf hzbb with hza' | hzb'
      · -- `za = fn`, `zb = f₁`
        have hb₀only : ∀ z ∈ f, G.Adj z b₀ → z = f₁ := by
          intro z hz hadj
          by_contra hzne
          refine HyperprismTwoAttachments.not_local_pair hH (show (1 : Fin 3) ≠ 0 by decide)
            ha₁ hb₀ (local_mono ?_ (localAfterFirst hF hf h2 hFeq))
          rintro y (rfl | rfl)
          · exact ⟨mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inl ha₁)⟩, za,
              ⟨by rw [hFeq]; exact hzaf, by simpa using (hza' ▸ hf₁ne.symm : za ≠ f₁)⟩,
              hzaa.symm⟩
          · exact ⟨mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inr hb₀)⟩, z,
              ⟨by rw [hFeq]; exact hz, by simpa using hzne⟩, hadj.symm⟩
        exact shortOddHole hG hH hf hodd h2 hfout (show (0 : Fin 3) ≠ 1 by decide)
          hb₀ hxBB (hzb ▸ hzbb) hxBfn.symm hb₀only
          (fun z hz hadj => hright' z hz hadj.symm)
      · exact absurd (hzb ▸ hzb' : f₁ = fn) hf₁ne
  obtain ⟨hf₁a₁, hfnb₀⟩ := hf₁a₁
  have hf₁xA : G.Adj f₁ xA := hxAf₁.symm
  have hfnxB : G.Adj fn xB := hxBfn.symm
  -- *"for every vertex in `X ∩ A`, `f₁` is its unique neighbour in `F`"*, and the same for `B`
  have hAuniq : ∀ (k : Fin 3), ∀ z ∈ f, ∀ a ∈ A k, G.Adj z a → z = f₁ := by
    intro k
    by_cases hk : k = 1
    · subst k
      exact onlyFirstSeesA hH hF hf h2 hFeq (j := 0) (k := 1) (by decide) hb₀ hfnb₀
    · exact onlyFirstSeesA hH hF hf h2 hFeq (j := 1) (k := k) hk hxBB hfnxB
  have hBuniq : ∀ (k : Fin 3), ∀ z ∈ f, ∀ b ∈ B k, G.Adj z b → z = fn := by
    intro k
    by_cases hk : k = 0
    · subst k
      exact onlyLastSeesB hH hF hf h2 hFeq (i := 1) (k := 0) (by decide) ha₁ hf₁a₁
    · exact onlyLastSeesB hH hF hf h2 hFeq (i := 0) (k := k) (Ne.symm hk) hxAA hf₁xA
  -- the split `A'ᵢ = Aᵢ ∩ X`, `B'ᵢ = Bᵢ ∩ X`
  set P : Fin 3 → Set V := fun k => {a ∈ A k | G.Adj f₁ a} with hP
  set Q : Fin 3 → Set V := fun k => {b ∈ B k | G.Adj fn b} with hQ
  have hPadj : ∀ (i : Fin 3), ∀ a ∈ P i, G.Adj f₁ a := fun i a ha => ha.2
  have hQadj : ∀ (i : Fin 3), ∀ b ∈ Q i, G.Adj fn b := fun i b hb => hb.2
  have hother : ∀ m : Fin 3, ∃ t : Fin 3, t ≠ m ∧ ∃ a' b' : V,
      a' ∈ A t ∧ b' ∈ B t ∧ G.Adj f₁ a' ∧ G.Adj fn b' := by
    intro m
    by_cases hm : m = 0
    · exact ⟨1, by simp [hm], a₁, xB, ha₁, hxBB, hf₁a₁, hfnxB⟩
    · exact ⟨0, Ne.symm hm, xA, b₀, hxAA, hb₀, hf₁xA, hfnb₀⟩
  have hxnor : ∀ (m : Fin 3) (R : List V) (a b : V), IsRungFrom G A B C m R a b →
      (G.Adj f₁ a ↔ G.Adj fn b) := by
    intro m R a b hR
    obtain ⟨t, htm, a', b', ha', hb', hfa', hfb'⟩ := hother m
    exact rungXnor hG hH hf hodd hfout hAuniq hBuniq hCnone hR htm ha' hb' hfa' hfb'
  have hs : IsRungSplit G A B C P Q := by
    refine ⟨fun k a ha => ha.1, fun k b hb => hb.1, ?_⟩
    intro m R a b hR
    by_cases hadj : G.Adj f₁ a
    · exact Or.inl ⟨⟨hR.1, hadj⟩, ⟨hR.2.1, (hxnor m R a b hR).mp hadj⟩⟩
    · exact Or.inr ⟨fun h => hadj h.2, fun h => hadj ((hxnor m R a b hR).mpr h.2)⟩
  have hAedges : ∀ (i : Fin 3), ∀ z ∈ f, ∀ a ∈ A i, G.Adj z a → z = f₁ ∧ a ∈ P i := by
    intro i z hz a ha hadj
    have hzf := hAuniq i z hz a ha hadj
    exact ⟨hzf, ha, by rw [← hzf]; exact hadj⟩
  have hBedges : ∀ (i : Fin 3), ∀ z ∈ f, ∀ b ∈ B i, G.Adj z b → z = fn ∧ b ∈ Q i := by
    intro i z hz b hb hadj
    have hzf := hBuniq i z hz b hb hadj
    exact ⟨hzf, hb, by rw [← hzf]; exact hadj⟩
  have hcrossPQ : ∀ (D : Fin 3 → Set V), (∀ k, D k ⊆ A k) → True := fun _ _ => trivial
  have hxAP : xA ∈ P 0 := ⟨hxAA, hf₁xA⟩
  have ha₁P : a₁ ∈ P 1 := ⟨ha₁, hf₁a₁⟩
  have hb₀Q : b₀ ∈ Q 0 := ⟨hb₀, hfnb₀⟩
  have hxBQ : xB ∈ Q 1 := ⟨hxBB, hfnxB⟩
  have hPsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (P j).Nonempty := by
    intro i
    by_cases hi : i = 0
    · exact ⟨1, by simp [hi], a₁, ha₁P⟩
    · exact ⟨0, Ne.symm hi, xA, hxAP⟩
  have hQsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (Q j).Nonempty := by
    intro i
    by_cases hi : i = 0
    · exact ⟨1, by simp [hi], xB, hxBQ⟩
    · exact ⟨0, Ne.symm hi, b₀, hb₀Q⟩
  -- the crossing condition, which is the same in both cases
  have hcrossGen : ∀ (D E K : Fin 3 → Set V), (∀ k, D k ⊆ A 0 ∪ A 1 ∪ A 2) →
      (∀ k, E k ⊆ B 0 ∪ B 1 ∪ B 2) → (∀ k, K k ⊆ C 0 ∪ C 1 ∪ C 2) →
      (∀ z ∈ f, ∀ (k : Fin 3), ∀ y ∈ D k ∪ E k ∪ K k, G.Adj z y →
        (z = f₁ ∧ y ∈ D k) ∨ (z = fn ∧ y ∈ E k)) := by
    intro D E K hD hE hK z hz k y hy hadj
    rcases hy with (hyD | hyE) | hyK
    · obtain ⟨m, hm⟩ := mem_union3.mp (hD k hyD)
      exact Or.inl ⟨hAuniq m z hz y hm hadj, hyD⟩
    · obtain ⟨m, hm⟩ := mem_union3.mp (hE k hyE)
      exact Or.inr ⟨hBuniq m z hz y hm hadj, hyE⟩
    · obtain ⟨m, hm⟩ := mem_union3.mp (hK k hyK)
      exact absurd hadj (hCnone z hz m y hm)
  by_cases hcase : ∃ r : Fin 3, ∀ k : Fin 3, k ≠ r → A k ⊆ P k
  · -- *"and so we can add `f₁` to `A₃`, `fₙ` to `B₃` and `f₂,…,f_{n-1}` to `C₃`"*
    obtain ⟨r, hr⟩ := hcase
    have hrQ : ∀ k : Fin 3, k ≠ r → B k ⊆ Q k := by
      intro k hk b hb
      obtain ⟨R, a, hR⟩ :=
        Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_B hH k hb
      exact ⟨hb, (hxnor k R a b hR).mp (hr k hk hR.1).2⟩
    set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 r with hσ
    have hσ0 : σ 0 = r := Equiv.swap_apply_left 0 r
    have hσne : ∀ k : Fin 3, k ≠ 0 → σ k ≠ r := by
      intro k hk h
      exact hk (σ.injective (h.trans hσ0.symm))
    refine packageData G A B C (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k))
      (HyperprismTwoAttachments.isHyperprism_perm hG hH σ) (hyperVerts_perm A B C σ)
      hf hf₁ne hfout ?_ ?_ ?_
    · intro k hk a ha
      exact (hr (σ k) (hσne k hk) ha).2
    · intro k hk b hb
      exact (hrQ (σ k) (hσne k hk) hb).2
    · intro z hz k _ y hy hadj
      exact hcrossGen (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k))
        (fun k x hx => mem_union3_of (σ k) hx)
        (fun k x hx => mem_union3_of (σ k) hx)
        (fun k x hx => mem_union3_of (σ k) hx)
        z hz k y hy hadj
  · -- the split-and-regroup construction
    push_neg at hcase
    have hAsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (A j \ P j).Nonempty := by
      intro i
      obtain ⟨j, hj, hsub⟩ := hcase i
      obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hsub
      exact ⟨j, hj, a, ha, hna⟩
    have hBsupp : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i ∧ (B j \ Q j).Nonempty := by
      intro i
      obtain ⟨j, hj, a, ha, hna⟩ := hAsupp i
      obtain ⟨R, b, hR⟩ :=
        Workspace.ProofLemmas.HyperprismRungStructure.exists_rung_from_A hH j ha
      refine ⟨j, hj, b, hR.2.1, ?_⟩
      intro hbQ
      exact hna ⟨ha, (hxnor j R a b hR).mpr hbQ.2⟩
    obtain ⟨hPA, hQB⟩ := oddSplitCompleteness hG hH hs hAsupp hBsupp hPsupp hQsupp
      hf hodd hfout hAedges hBedges hPadj hQadj hCnone
    have hD : ((A 0 \ P 0) ∪ (A 1 \ P 1) ∪ (A 2 \ P 2)).Nonempty := by
      obtain ⟨j, -, a, ha⟩ := hAsupp 0
      exact ⟨a, mem_union3_of (f := fun k => A k \ P k) j ha⟩
    have hHreg : IsHyperprism G (regroupA A P) (regroupB B Q) (regroupC G A B C P Q) :=
      regroupIsHyperprism G A B C P Q hG hH hs hPA hQB ⟨xA, hxAP⟩ ⟨a₁, Or.inl ha₁P⟩ hD
    set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2 with hσ
    refine packageData G A B C (fun k => regroupA A P (σ k)) (fun k => regroupB B Q (σ k))
      (fun k => regroupC G A B C P Q (σ k))
      (HyperprismTwoAttachments.isHyperprism_perm hG hHreg σ)
      (by rw [hyperVerts_perm]; exact hyperVerts_regroup hH hs) hf hf₁ne hfout ?_ ?_ ?_
    · intro k hk a ha
      fin_cases k
      · exact absurd rfl hk
      · have : a ∈ P 1 ∪ P 2 := by simpa [σ, regroupA] using ha
        rcases this with h | h
        · exact h.2
        · exact h.2
      · have : a ∈ P 0 := by simpa [σ, regroupA] using ha
        exact this.2
    · intro k hk b hb
      fin_cases k
      · exact absurd rfl hk
      · have : b ∈ Q 1 ∪ Q 2 := by simpa [σ, regroupB] using hb
        rcases this with h | h
        · exact h.2
        · exact h.2
      · have : b ∈ Q 0 := by simpa [σ, regroupB] using hb
        exact this.2
    · intro z hz k _ y hy hadj
      refine hcrossGen (fun k => regroupA A P (σ k)) (fun k => regroupB B Q (σ k))
        (fun k => regroupC G A B C P Q (σ k)) ?_ ?_ ?_ z hz k y hy hadj
      · intro k x hx0
        have hx : x ∈ regroupA A P (σ k) := hx0
        rcases fin3_cases (σ k) with h | h | h <;> rw [h] at hx
        · exact mem_union3_of 0 (hs.PA 0 (by simpa [regroupA] using hx))
        · rcases (by simpa [regroupA] using hx : x ∈ P 1 ∪ P 2) with hh | hh
          · exact mem_union3_of 1 (hs.PA 1 hh)
          · exact mem_union3_of 2 (hs.PA 2 hh)
        · rcases (by simpa [regroupA] using hx :
              x ∈ (A 0 \ P 0) ∪ (A 1 \ P 1) ∪ (A 2 \ P 2)) with (hh | hh) | hh
          · exact mem_union3_of 0 hh.1
          · exact mem_union3_of 1 hh.1
          · exact mem_union3_of 2 hh.1
      · intro k x hx0
        have hx : x ∈ regroupB B Q (σ k) := hx0
        rcases fin3_cases (σ k) with h | h | h <;> rw [h] at hx
        · exact mem_union3_of 0 (hs.QB 0 (by simpa [regroupB] using hx))
        · rcases (by simpa [regroupB] using hx : x ∈ Q 1 ∪ Q 2) with hh | hh
          · exact mem_union3_of 1 (hs.QB 1 hh)
          · exact mem_union3_of 2 (hs.QB 2 hh)
        · rcases (by simpa [regroupB] using hx :
              x ∈ (B 0 \ Q 0) ∪ (B 1 \ Q 1) ∪ (B 2 \ Q 2)) with (hh | hh) | hh
          · exact mem_union3_of 0 hh.1
          · exact mem_union3_of 1 hh.1
          · exact mem_union3_of 2 hh.1
      · intro k x hx0
        have hx : x ∈ regroupC G A B C P Q (σ k) := hx0
        rcases fin3_cases (σ k) with h | h | h <;> rw [h] at hx
        · exact mem_union3_of 0 (Cp_subset_C 0 (by simpa [regroupC] using hx))
        · rcases (by simpa [regroupC] using hx :
              x ∈ Cp G A B C P Q 1 ∪ Cp G A B C P Q 2) with hh | hh
          · exact mem_union3_of 1 (Cp_subset_C 1 hh)
          · exact mem_union3_of 2 (Cp_subset_C 2 hh)
        · rcases (by simpa [regroupC] using hx :
              x ∈ Cpp G A B C P Q 0 ∪ Cpp G A B C P Q 1 ∪ Cpp G A B C P Q 2) with
              (hh | hh) | hh
          · exact mem_union3_of 0 (Cpp_subset_C 0 hh)
          · exact mem_union3_of 1 (Cpp_subset_C 1 hh)
          · exact mem_union3_of 2 (Cpp_subset_C 2 hh)

end Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oData
