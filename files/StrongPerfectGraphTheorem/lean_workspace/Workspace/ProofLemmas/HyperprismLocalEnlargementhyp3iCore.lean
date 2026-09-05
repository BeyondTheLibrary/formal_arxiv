import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismRungStructure
import Workspace.Statements.S10.Thm_10_3
import Workspace.Statements.S10.Thm_10_5

/-!
# 10.6, claim (2): the interior-attachment block, varying-rung part

This module carries the printed sentences

> *"From the minimality of `F` it follows that `F = {f₁,…,fₙ}`.  Since this holds for all
> choices of `R₃` it follows that `f₁` is complete to `A₃` and there are no edges between
> `{f₁,…,fₙ}` and `B₃ ∪ C₃`.  Since `a₃ ∈ X` the same conclusion follows for all choices of
> `R₂` …"*

(printed p. 61) into Lean.  Everything is stated for the strip indexed `0` playing the role of
the paper's `R₁`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iCore

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismRungStructure
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.Thm106Assembly

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

/-! ### Bookkeeping -/

/-- The vertex set of the prism formed by three rungs. -/
def prismVerts (R : Fin 3 → List V) : Set V :=
  {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}

theorem mem_prismVerts {R : Fin 3 → List V} {v : V} :
    v ∈ prismVerts R ↔ (v ∈ R 0 ∨ v ∈ R 1 ∨ v ∈ R 2) := by
  simp only [prismVerts, Set.mem_union, Set.mem_setOf_eq, or_assoc]

/-- The conclusion of 10.3 in its `A`-form, for the prism made of the rungs `R`, with the
paper's `R₁` being the rung of index `0`. -/
def AForm (G : SimpleGraph V) (a : Fin 3 → V) (R : Fin 3 → List V)
    (f : List V) (f₁ fn : V) : Prop :=
  G.Adj f₁ (a 1) ∧ G.Adj f₁ (a 2) ∧ (∃ y ∈ R 0, y ≠ a 0 ∧ G.Adj fn y) ∧
    (∀ x ∈ f, ∀ k ∈ prismVerts R, k ≠ a 0 → G.Adj x k →
      (x = f₁ ∧ (k = a 1 ∨ k = a 2)) ∨ (x = fn ∧ k ∈ R 0))

theorem getElem_idx_eq {W : Type*} (l : List W) {i j : ℕ} (hij : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst hij; rfl

theorem fin3_pair {m n : Fin 3} (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hmn : m ≠ n) :
    (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) := by
  revert hm0 hn0 hmn; revert m n; decide

theorem other_index {k : Fin 3} (hk : k ≠ 0) : ∃ n : Fin 3, n ≠ 0 ∧ k ≠ n := by
  revert hk; revert k; decide

/-- The `A`-end of a rung is one of its vertices. -/
theorem rung_mem_A_end {i : Fin 3} {p : List V} {x y : V}
    (h : IsRungFrom G A B C i p x y) : x ∈ p :=
  List.mem_of_mem_head? (by rw [h.2.2.1.2.1]; rfl)

/-- The `B`-end of a rung is one of its vertices. -/
theorem rung_mem_B_end {i : Fin 3} {p : List V} {x y : V}
    (h : IsRungFrom G A B C i p x y) : y ∈ p :=
  List.mem_of_mem_getLast? (by rw [h.2.2.1.2.2]; rfl)

/-- Greatest index below `n` satisfying `Q`. -/
theorem exists_greatest {Q : ℕ → Prop} : ∀ (n : ℕ), (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
  intro n
  induction n with
  | zero => rintro ⟨k, hk, -⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro hex
    by_cases hQ : Q n
    · exact ⟨n, by omega, hQ, fun m hm _ => by omega⟩
    · have hex' : ∃ k, k < n ∧ Q k := by
        obtain ⟨k, hk, hQk⟩ := hex
        refine ⟨k, ?_, hQk⟩
        rcases (by omega : k < n ∨ k = n) with h | h
        · exact h
        · exact absurd (h ▸ hQk) hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      refine ⟨k, by omega, hQk, ?_⟩
      intro m hm hQm
      rcases (by omega : m < n ∨ m = n) with h | h
      · exact hmax m h hQm
      · exact absurd (h ▸ hQm) hQ

/-! ### *"From the minimality of `F` it follows that `F = {f₁,…,fₙ}`"* -/

/-- PAPER (10.6, claim (2), printed p. 61): *"From the minimality of `F` it follows that
`F = {f₁,…,fₙ}`."*

The hypotheses are exactly the attachments produced by 10.3: two `A`-ends in two different
strips, and one vertex of the rung of index `0` other than its `A`-end. -/
theorem fullF [Fintype V] {F : Set V} (hH : IsHyperprism G A B C)
    (hF : MinimalBad G A B C F)
    {g : List V} (hg : IsPathList G g) (hgF : ∀ v ∈ g, v ∈ F)
    {m n : Fin 3} (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hmn : m ≠ n)
    {α₁ α₂ : V} (hα₁ : α₁ ∈ A m) (hα₂ : α₂ ∈ A n)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ g) (hz₂ : z₂ ∈ g)
    (hadj₁ : G.Adj α₁ z₁) (hadj₂ : G.Adj α₂ z₂)
    {R0 : List V} {a0 b0 y : V} (hR0 : IsRungFrom G A B C 0 R0 a0 b0)
    (hy : y ∈ R0) (hyne : y ≠ a0) {z₃ : V} (hz₃ : z₃ ∈ g) (hadj₃ : G.Adj y z₃) :
    F = {v : V | v ∈ g} := by
  classical
  have hsub : {v : V | v ∈ g} ⊆ F := fun v hv => hgF v hv
  have hconn : ConnectedSet G {v : V | v ∈ g} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hg
  by_contra hne
  have hlocal := hF.local_of_ssubset hsub (fun h => hne h.symm) hconn
  have hattα₁ : α₁ ∈ attachments G {v : V | v ∈ g} (hyperVerts A B C) :=
    ⟨subset_hyperVerts m (Or.inl (Or.inl hα₁)), z₁, hz₁, hadj₁⟩
  have hattα₂ : α₂ ∈ attachments G {v : V | v ∈ g} (hyperVerts A B C) :=
    ⟨subset_hyperVerts n (Or.inl (Or.inl hα₂)), z₂, hz₂, hadj₂⟩
  have hatty : y ∈ attachments G {v : V | v ∈ g} (hyperVerts A B C) :=
    ⟨rung_subset_hyperVerts hR0 y hy, z₃, hz₃, hadj₃⟩
  rcases localForHyperprism_iff.mp hlocal with ⟨i, hi⟩ | hA | hB
  · have h1 : i = m := by
      by_contra hc
      exact notMem_S hH (Ne.symm hc) (Or.inl (Or.inl hα₁)) (hi hattα₁)
    have h2 : i = n := by
      by_contra hc
      exact notMem_S hH (Ne.symm hc) (Or.inl (Or.inl hα₂)) (hi hattα₂)
    exact hmn (h1 ▸ h2)
  · obtain ⟨k, hk⟩ := mem_union3.mp (hA hatty)
    have hk0 : k = 0 := by
      by_contra hc
      exact notMem_S hH (Ne.symm hc) (rung_mem_S hR0 y hy) (Or.inl (Or.inl hk))
    subst hk0
    exact hyne (rung_eq_A hH hR0 hy hk)
  · obtain ⟨k, hk⟩ := mem_union3.mp (hB hattα₁)
    exact Set.disjoint_left.mp (hH.2.1 m k) hα₁ hk

/-! ### *"Since this holds for all choices of `R₃` …"* -/

/-- PAPER (10.6, claim (2), printed p. 61): *"Since this holds for all choices of `R₃` it
follows that `f₁` is complete to `A₃` and there are no edges between `{f₁,…,fₙ}` and
`B₃ ∪ C₃`.  Since `a₃ ∈ X` the same conclusion follows for all choices of `R₂` …"*

Here `m` is the index of the strip whose rung is being varied and `n` the index of the strip
whose rung is kept; the kept rung supplies the second attachment `a n` that 10.3 needs. -/
theorem varyRung [Fintype V] [DecidableEq V] {F : Set V}
    (hG : Berge G) (hK4 : NoK4 G) (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (hR : ∀ i : Fin 3, IsRungFrom G A B C i (R i) (a i) (b i))
    {x₁ : V} (hx₁F : ∃ w ∈ F, G.Adj x₁ w) (hx₁int : x₁ ∈ SPGT.interior (R 0))
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn) (hfF : ∀ v ∈ f, v ∈ F)
    (hFf : F = {v : V | v ∈ f})
    (hA : AForm G a R f f₁ fn)
    {m n : Fin 3} (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hmn : m ≠ n)
    {Q : List V} {α β : V} (hQ : IsRungFrom G A B C m Q α β) :
    G.Adj f₁ α ∧ ∀ z ∈ f, ∀ w ∈ Q, G.Adj z w → z = f₁ ∧ w = α := by
  classical
  obtain ⟨hAa1, hAa2, hAy, honly⟩ := hA
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? (by rw [hf.2.1]; rfl)
  have hcase := fin3_pair hm0 hn0 hmn
  -- the modified rung family
  set R' : Fin 3 → List V := fun i => if i = m then Q else R i with hR'def
  set a' : Fin 3 → V := fun i => if i = m then α else a i with ha'def
  set b' : Fin 3 → V := fun i => if i = m then β else b i with hb'def
  have h0m : (0 : Fin 3) ≠ m := Ne.symm hm0
  have hR'0 : R' 0 = R 0 := by simp [hR'def, h0m]
  have ha'0 : a' 0 = a 0 := by simp [ha'def, h0m]
  have hR'rung : ∀ i : Fin 3, IsRungFrom G A B C i (R' i) (a' i) (b' i) := by
    intro i
    by_cases hi : i = m
    · subst hi; simpa [hR'def, ha'def, hb'def] using hQ
    · simpa [hR'def, ha'def, hb'def, hi] using hR i
  have ha'1 : a' 1 = α ∨ a' 1 = a n := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp [ha'def]
  have ha'2 : a' 2 = α ∨ a' 2 = a n := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp [ha'def]
  have hαa' : α = a' 1 ∨ α = a' 2 := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp [ha'def]
  have hana' : a n = a' 1 ∨ a n = a' 2 := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp [ha'def]
  have hbnb' : b n = b' 1 ∨ b n = b' 2 := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp [hb'def]
  have hPV : ∀ w : V, w ∈ prismVerts R' ↔ (w ∈ R 0 ∨ w ∈ Q ∨ w ∈ R n) := by
    intro w
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
      simp only [mem_prismVerts, hR'def] <;> norm_num <;> tauto
  -- the prism `R 0, Q, R n` and its consequences
  have hEven : IsEvenPrism G a' b' (R' 0) (R' 1) (R' 2) := rungs_isEvenPrism hG hH hR'rung
  have hmaj : ∀ v ∈ F, ¬ MajorForPrism G a' b' v := by
    intro v _ hv
    exact hNoBalanced (Workspace.Statements.S10.SPGT.thm_10_5 G hG hK4 a' b'
      (R' 0) (R' 1) (R' 2) v hEven hv)
  have hFout : F ⊆ (prismVerts R')ᶜ := by
    intro v hv hvK
    refine hF.1.2.1 hv ?_
    rcases (hPV v).mp hvK with h | h | h
    · exact rung_subset_hyperVerts (hR 0) v h
    · exact rung_subset_hyperVerts hQ v h
    · exact rung_subset_hyperVerts (hR n) v h
  have hx₁K : IsAttachment G F (prismVerts R') x₁ :=
    ⟨(hPV x₁).mpr (Or.inl (Workspace.ProofLemmas.PathBasics.interior_subset hx₁int)), hx₁F⟩
  have hanQ : a n ∈ R n := rung_mem_A_end (hR n)
  have hf₁an : G.Adj f₁ (a n) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h2 <;> assumption
  have hx₂K : IsAttachment G F (prismVerts R') (a n) :=
    ⟨(hPV _).mpr (Or.inr (Or.inr hanQ)), f₁, hfF f₁ hf₁mem, hf₁an.symm⟩
  have hx₂notR0 : a n ∉ R 0 := rung_disj hH hn0 (hR n) (hR 0) (a n) hanQ
  obtain ⟨g, g₁, gm, hg, hgF, hcaseAB⟩ :=
    Workspace.Statements.S10.SPGT.thm_10_3 G hG hK4 a' b' R' (prismVerts R') F
      (rungs_formPrism hH hR'rung) rfl hFout hF.1.1 hmaj x₁ (a n) hx₁K
      (by rw [hR'0]; exact hx₁int) hx₂K (by rw [hR'0]; exact hx₂notR0)
  have hg₁mem : g₁ ∈ g := List.mem_of_mem_head? (by rw [hg.2.1]; rfl)
  have hgmmem : gm ∈ g := List.mem_of_mem_getLast? (by rw [hg.2.2]; rfl)
  have hg₁f : g₁ ∈ f := by
    have := hgF g₁ hg₁mem
    rwa [hFf] at this
  -- the `B`-form of 10.3 is impossible: `g₁` would see `b n`
  rcases hcaseAB with ⟨hAg1, hAg2, hAgy, honly'⟩ | ⟨hBg1, hBg2, _, _⟩
  · -- the `A`-form
    have hg₁an : G.Adj g₁ (a n) := by
      rcases hana' with h | h <;> rw [h] <;> assumption
    have hanK : a n ∈ prismVerts R := mem_prismVerts.mpr (by
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h2
      · exact Or.inr (Or.inr hanQ)
      · exact Or.inr (Or.inl hanQ))
    have hanne : a n ≠ a 0 := fun h =>
      Set.disjoint_left.mp (hH.2.2.2.2.1 n 0 hn0) (hR n).1
        (show a n ∈ A 0 by rw [h]; exact (hR 0).1)
    have hg₁eq : g₁ = f₁ := by
      rcases honly g₁ hg₁f (a n) hanK hanne hg₁an with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hx₂notR0
    have hf₁α : G.Adj f₁ α := by
      rw [← hg₁eq]
      rcases hαa' with h | h <;> rw [h] <;> assumption
    refine ⟨hf₁α, ?_⟩
    -- `F = V(g)` again, so every vertex of `f` is a vertex of `g`
    obtain ⟨y', hy'R0, hy'ne, hgmy'⟩ := hAgy
    have hFg : F = {v : V | v ∈ g} :=
      fullF hH hF hg.1 hgF (m := 1) (n := 2) (by decide) (by decide) (by decide)
        (hR'rung 1).1 (hR'rung 2).1 hg₁mem hg₁mem hAg1.symm hAg2.symm
        (hR'rung 0) hy'R0 hy'ne hgmmem hgmy'.symm
    intro z hz w hw hadj
    have hzg : z ∈ g := by
      have := hfF z hz
      rwa [hFg] at this
    have hwK : w ∈ prismVerts R' := (hPV w).mpr (Or.inr (Or.inl hw))
    have hwne : w ≠ a' 0 := by
      rw [ha'0]
      intro h
      exact rung_disj hH hm0 hQ (hR 0) w hw (show w ∈ R 0 by rw [h]; exact rung_mem_A_end (hR 0))
    rcases honly' z hzg w hwK hwne hadj with ⟨hz1, hw1⟩ | ⟨-, hw2⟩
    · refine ⟨hz1.trans hg₁eq, ?_⟩
      have hwan : w ≠ a n := fun h =>
        rung_disj hH hmn hQ (hR n) w hw (h ▸ hanQ)
      rcases hw1 with h | h
      · rcases ha'1 with h' | h'
        · rw [h, h']
        · exact absurd (h.trans h') hwan
      · rcases ha'2 with h' | h'
        · rw [h, h']
        · exact absurd (h.trans h') hwan
    · rw [hR'0] at hw2
      exact absurd hw2 (rung_disj hH hm0 hQ (hR 0) w hw)
  · -- the `B`-form
    exfalso
    have hg₁bn : G.Adj g₁ (b n) := by
      rcases hbnb' with h | h <;> rw [h] <;> assumption
    have hbnRn : b n ∈ R n := rung_mem_B_end (hR n)
    have hbnK : b n ∈ prismVerts R := mem_prismVerts.mpr (by
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h2
      · exact Or.inr (Or.inr hbnRn)
      · exact Or.inr (Or.inl hbnRn))
    have hbnne : b n ≠ a 0 := fun h =>
      Set.disjoint_left.mp (hH.2.1 0 n) (h ▸ (hR 0).1) (hR n).2.1
    rcases honly g₁ hg₁f (b n) hbnK hbnne hg₁bn with ⟨-, h⟩ | ⟨-, h⟩
    · rcases h with h | h
      · exact Set.disjoint_left.mp (hH.2.1 1 n) (h ▸ (hR 1).1) (hR n).2.1
      · exact Set.disjoint_left.mp (hH.2.1 2 n) (h ▸ (hR 2).1) (hR n).2.1
    · exact rung_disj hH hn0 (hR n) (hR 0) (b n) hbnRn h

/-! ### The rung of the enlarged strip -/

/-- PAPER (10.6, claim (2), printed p. 61): *"But then we can add `f₁` to `A₁` and
`{f₂,…,fₙ}` to `C₁` …"*

The path exhibited here is the paper's `f₁-⋯-fₙ-R₁`, cut at the neighbour of `fₙ` on `R₁`
closest to `b₁`: it is a rung of the enlarged first strip through all of `f₁,…,fₙ`. -/
theorem newRung (hH : IsHyperprism G A B C)
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (hR : ∀ i : Fin 3, IsRungFrom G A B C i (R i) (a i) (b i))
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hA : AForm G a R f f₁ fn) :
    ∃ q : List V,
      IsRungOfHyperprism G (fun k : Fin 3 => if k = 0 then A k ∪ {f₁} else A k) B
        (fun k : Fin 3 => if k = 0 then C k ∪ {z : V | z ∈ f ∧ z ≠ f₁} else C k) 0 q ∧
      ∀ z ∈ f, z ∈ q := by
  classical
  obtain ⟨hAa1, hAa2, ⟨y0, hy0R, hy0ne, hfny0⟩, honly⟩ := hA
  have hP : IsRungFrom G A B C 0 (R 0) (a 0) (b 0) := hR 0
  have hPpath : IsPathFrom G (R 0) (a 0) (b 0) := hP.2.2.1
  have hPnd : (R 0).Nodup := hPpath.1.2.1
  have hPpos : 0 < (R 0).length :=
    Workspace.ProofLemmas.PathBasics.path_length_pos hPpath.1
  have hP0 : (R 0)[0]'hPpos = a 0 :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hPpath.2.1 hPpos
  have hjlt : (R 0).length - 1 < (R 0).length := by omega
  have hPlast : (R 0)[(R 0).length - 1]'hjlt = b 0 :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hPpath.2.2 hPpos
  obtain ⟨j0, hj0lt, hj0y⟩ := List.mem_iff_getElem.mp hy0R
  have hj0pos : 0 < j0 := by
    rcases Nat.eq_zero_or_pos j0 with h | h
    · exact absurd (by rw [← hj0y]; subst h; exact hP0) hy0ne
    · exact h
  have hQj0 : G.Adj fn ((R 0).getD j0 (a 0)) := by
    rw [List.getD_eq_getElem _ _ hj0lt, hj0y]; exact hfny0
  obtain ⟨i0, hi0lt, hi0adj, hi0max⟩ :=
    exists_greatest (Q := fun k => G.Adj fn ((R 0).getD k (a 0))) (R 0).length
      ⟨j0, hj0lt, hQj0⟩
  have hi0pos : 0 < i0 := lt_of_lt_of_le hj0pos (hi0max j0 hj0lt hQj0)
  have hu : G.Adj fn ((R 0)[i0]'hi0lt) := by
    rw [← List.getD_eq_getElem _ (a 0) hi0lt]; exact hi0adj
  have hij : i0 ≤ (R 0).length - 1 := by omega
  have hSpath : IsPathFrom G (((R 0).drop i0).take ((R 0).length - 1 - i0 + 1))
      ((R 0)[i0]'hi0lt) ((R 0)[(R 0).length - 1]'hjlt) :=
    ⟨Workspace.ProofLemmas.PathBasics.isPathList_take
        (Workspace.ProofLemmas.PathBasics.isPathList_drop hPpath.1 hi0lt) (by omega),
      Workspace.ProofLemmas.PathBasics.head?_slice (R 0) hij hjlt,
      Workspace.ProofLemmas.PathBasics.getLast?_slice (R 0) hij hjlt⟩
  have hSmemP : ∀ w ∈ ((R 0).drop i0).take ((R 0).length - 1 - i0 + 1), w ∈ R 0 := by
    intro w hw
    obtain ⟨k, hk, -, -, hkw⟩ :=
      (Workspace.ProofLemmas.PathBasics.mem_slice_iff (R 0) hij hjlt).mp hw
    exact hkw ▸ List.getElem_mem hk
  have hdisj : ∀ x ∈ f, x ∉ ((R 0).drop i0).take ((R 0).length - 1 - i0 + 1) := by
    intro x hx hxS
    exact hfout x hx (rung_subset_hyperVerts hP x (hSmemP x hxS))
  have hcross : ∀ x ∈ f, ∀ w ∈ ((R 0).drop i0).take ((R 0).length - 1 - i0 + 1),
      (G.Adj x w ↔ (x = fn ∧ w = (R 0)[i0]'hi0lt)) := by
    intro x hx w hw
    constructor
    · intro hadj
      obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
        (Workspace.ProofLemmas.PathBasics.mem_slice_iff (R 0) hij hjlt).mp hw
      have hwP : w ∈ prismVerts R := mem_prismVerts.mpr (Or.inl (hSmemP w hw))
      have hwne : w ≠ a 0 := by
        intro h
        have h1 : (R 0)[k]'hk = (R 0)[0]'hPpos := by rw [hkw, h, hP0]
        have := (List.Nodup.getElem_inj_iff hPnd).mp h1
        omega
      rcases honly x hx w hwP hwne hadj with ⟨-, hw1⟩ | ⟨hxn, -⟩
      · exfalso
        rcases hw1 with h | h
        · exact rung_disj hH (show (1 : Fin 3) ≠ 0 by decide) (hR 1) (hR 0) (a 1)
            (rung_mem_A_end (hR 1)) (show a 1 ∈ R 0 by rw [← h]; exact hSmemP w hw)
        · exact rung_disj hH (show (2 : Fin 3) ≠ 0 by decide) (hR 2) (hR 0) (a 2)
            (rung_mem_A_end (hR 2)) (show a 2 ∈ R 0 by rw [← h]; exact hSmemP w hw)
      · refine ⟨hxn, ?_⟩
        have hkle : k ≤ i0 := hi0max k hk (by
          rw [List.getD_eq_getElem _ _ hk, hkw]; exact hxn ▸ hadj)
        rw [← hkw]
        exact getElem_idx_eq (R 0) (le_antisymm hkle hk1) hk hi0lt
    · rintro ⟨rfl, rfl⟩
      exact hu
  have hq : IsPathFrom G (f ++ ((R 0).drop i0).take ((R 0).length - 1 - i0 + 1)) f₁ (b 0) := by
    have h := Workspace.ProofLemmas.PathGlue.glue_path hf hSpath hdisj hcross
    rwa [hPlast] at h
  have hA0 : (fun k : Fin 3 => if k = 0 then A k ∪ {f₁} else A k) 0 = A 0 ∪ {f₁} := by simp
  have hC0 : (fun k : Fin 3 => if k = 0 then C k ∪ {z : V | z ∈ f ∧ z ≠ f₁} else C k) 0
      = C 0 ∪ {z : V | z ∈ f ∧ z ≠ f₁} := by simp
  refine ⟨_, ⟨f₁, b 0, ?_, hP.2.1, hq, ?_⟩, fun z hz => List.mem_append_left _ hz⟩
  · rw [hA0]; exact Or.inr rfl
  · intro w hw
    rw [hC0]
    obtain ⟨hwq, hwf₁, hwb0⟩ :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).mp hw
    rcases List.mem_append.mp hwq with h | h
    · exact Or.inr ⟨h, hwf₁⟩
    · refine Or.inl (hP.2.2.2 w ?_)
      obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
        (Workspace.ProofLemmas.PathBasics.mem_slice_iff (R 0) hij hjlt).mp h
      have hkne : k ≠ (R 0).length - 1 := by
        intro hc
        exact hwb0 (by rw [← hkw]; exact (getElem_idx_eq (R 0) hc hk hjlt).trans hPlast)
      rw [← hkw]
      exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hPpath.1 hk
        (by omega) (by omega)

/-! ### The interior block of claim (2), given the `A`-form of 10.3 -/

/-- PAPER (10.6, claim (2), printed p. 61), the whole first block once 10.3 has been applied
in its `A`-form: *"From the minimality of `F` it follows that `F={f₁,…,fₙ}`.  Since this holds
for all choices of `R₃` … so `f₁` is complete to `A₂` and there are no edges between
`{f₁,…,fₙ}` and `B₂ ∪ C₂`.  But then we can add `f₁` to `A₁` and `{f₂,…,fₙ}` to `C₁` …"*

The conclusion is the body of
`HyperprismLocalEnlargementInterior.ExtensionData G A B C`, spelled out. -/
theorem coreFromA [Fintype V] [DecidableEq V] {F : Set V}
    (hG : Berge G) (hK4 : NoK4 G) (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (hR : ∀ i : Fin 3, IsRungFrom G A B C i (R i) (a i) (b i))
    {x₁ : V} (hx₁F : ∃ w ∈ F, G.Adj x₁ w) (hx₁int : x₁ ∈ SPGT.interior (R 0))
    {f : List V} {f₁ fn : V} (hf : IsPathFrom G f f₁ fn) (hfF : ∀ v ∈ f, v ∈ F)
    (hA : AForm G a R f f₁ fn) :
    ∃ (p : List V) (u : V),
      u ∈ p ∧ p.Nodup ∧
      (∀ z ∈ p, z ∉ hyperVerts A B C) ∧
      (∀ (k : Fin 3), k ≠ 0 → ∀ α ∈ A k, G.Adj u α) ∧
      (∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
        ∀ y ∈ A k ∪ B k ∪ C k, G.Adj z y → z = u ∧ y ∈ A k) ∧
      (let A' := fun k : Fin 3 => if k = 0 then A k ∪ {u} else A k
       let C' := fun k : Fin 3 =>
         if k = 0 then C k ∪ {z : V | z ∈ p ∧ z ≠ u} else C k
       ∃ q : List V, IsRungOfHyperprism G A' B C' 0 q ∧ ∀ z ∈ p, z ∈ q) := by
  classical
  obtain ⟨hAa1, hAa2, ⟨y0, hy0R, hy0ne, hfny0⟩, honly⟩ := id hA
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? (by rw [hf.2.1]; rfl)
  have hfnmem : fn ∈ f := List.mem_of_mem_getLast? (by rw [hf.2.2]; rfl)
  have hout : ∀ z ∈ f, z ∉ hyperVerts A B C := fun z hz => hF.1.2.1 (hfF z hz)
  have hFf : F = {v : V | v ∈ f} :=
    fullF hH hF hf.1 hfF (m := 1) (n := 2) (by decide) (by decide) (by decide)
      (hR 1).1 (hR 2).1 hf₁mem hf₁mem hAa1.symm hAa2.symm (hR 0) hy0R hy0ne hfnmem hfny0.symm
  refine ⟨f, f₁, hf₁mem, hf.1.2.1, hout, ?_, ?_, ?_⟩
  · intro k hk α hα
    obtain ⟨n, hn0, hkn⟩ := other_index hk
    obtain ⟨Q, β, hQ⟩ := exists_rung_from_A hH k hα
    exact (varyRung hG hK4 hNoBalanced hH hF hR hx₁F hx₁int hf hfF hFf hA hk hn0 hkn hQ).1
  · intro z hz k hk y hy hadj
    obtain ⟨n, hn0, hkn⟩ := other_index hk
    obtain ⟨Q, α, β, hQ, hyQ⟩ := exists_rung_through hH k hy
    obtain ⟨h3, h4⟩ :=
      (varyRung hG hK4 hNoBalanced hH hF hR hx₁F hx₁int hf hfF hFf hA hk hn0 hkn hQ).2
        z hz y hyQ hadj
    exact ⟨h3, by rw [h4]; exact hQ.1⟩
  · exact newRung hH hR hf hout hA

end Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iCore
