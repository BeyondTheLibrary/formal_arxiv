import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_4
import Workspace.Statements.S10.Thm_10_4
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.Thm101ClaimOne

/-!
# 11.1, statement (1) — the step-by-step claim of the printed proof

PAPER (printed p. 66, inside the proof of 11.1):

*"(1) For every step `a₁-R₁-b₁`, `a₂-R₂-b₂`, if `v` has a neighbour in `R₁ ∪ R₂` then `v` is
adjacent to `a₁, a₂` and to no other vertices of `R₁ ∪ R₂`."*

Its printed proof is the block

*"For assume `v` has a neighbour in `R₁` say, and hence in `R₁ \ b₁`.  Now `R₀, R₁, R₂` form a
prism `K` say, and no vertex in `F` is major with respect to `K` since no vertex in `F` is
adjacent to `b₁` or `b₂`.  Yet `F` has an attachment in `R₀ \ a₀` and one in `R₁ \ b₁`, so its
set of attachments is not local.  Since `b₁` is not an attachment of `F`, it follows from 10.4
that `F` has an attachment in `R₂`; and therefore `v` has a neighbour in `R₂ \ b₂`.  If `v` has
any neighbours in `R₁ ∪ R₂` different from `a₁, a₂`, say a neighbour in the interior of `R₁`,
then `v` can be linked onto the triangle `b₀, b₁, b₂`, via the paths `v-P-b₀`, from `v` to `b₁`
with interior in `R₁ \ a₁`, and from `v` to `b₂` with interior in `R₂`; but this contradicts
2.4.  This proves (1)."*

with `F` the connected subset of `V(P)` containing `v`, disjoint from `V(R₀)` and with an
attachment in `R₀ \ a₀` that the proof of 11.1 fixes in its first sentence (the stretch of `P`
running from `v` up to the vertex before `P` first meets `V(R₀)`; `P` does meet `V(R₀)`, since
`b₀` is its last vertex, and it avoids `a₀`).

The hypotheses below are exactly those of 11.1 that this block uses — 11.1's *"`v` has a
neighbour in `A ∪ C`"* is not among them — together with the step and the neighbour whose
existence the claim assumes.
-/
set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm111Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V} {a b : V} {R : List V}
    (h : IsRungOfStrip G A C B a R b) : ∀ x ∈ R, x ∈ A ∪ B ∪ C := by
  intro x hx
  by_cases hxa : x = a
  · exact Or.inl (Or.inl (hxa ▸ h.2.1))
  by_cases hxb : x = b
  · exact Or.inl (Or.inr (hxb ▸ h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 x
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).mpr
        ⟨hx, hxa, hxb⟩))

private theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  obtain ⟨h₁, h₂, hd, he⟩ := h
  refine ⟨h₂, h₁, ?_, ?_⟩
  · exact fun x hx hx' => hd x hx' hx
  · intro x hx y hy
    rw [SimpleGraph.adj_comm]
    simpa [and_comm, or_comm] using he y hy x hx

private theorem exists_least_bounded {Q : ℕ → Prop} (n : ℕ)
    (h : ∃ k, k < n ∧ Q k) : ∃ k, k < n ∧ Q k ∧ ∀ m, m < k → ¬ Q m := by
  classical
  obtain ⟨k, hk, hQ⟩ := h
  have hex : ∃ m, Q m := ⟨k, hQ⟩
  exact ⟨Nat.find hex, lt_of_le_of_lt (Nat.find_min' hex hQ) hk, Nat.find_spec hex,
    fun m hm => Nat.find_min hex hm⟩

private theorem mem_take_iff (p : List V) (k : ℕ) (x : V) :
    x ∈ p.take k ↔ ∃ (i : ℕ) (hi : i < p.length), i < k ∧ p[i]'hi = x := by
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take, lt_min_iff] at hi
    exact ⟨i, hi.2, hi.1, by rw [← hix]; simp⟩
  · rintro ⟨i, hi, hik, rfl⟩
    refine List.mem_iff_getElem.mpr ⟨i, ?_, ?_⟩
    · rw [List.length_take, lt_min_iff]
      exact ⟨hik, hi⟩
    · simp

private theorem not_two_le_ncard {G : SimpleGraph V} {x y z c w : V}
    (hx : G.Adj w x → x = c) (hy : G.Adj w y → y = c) (hz : G.Adj w z → z = c) :
    ¬ (2 ≤ (({x, y, z} : Set V) ∩ G.neighborSet w).ncard) := by
  have hsub : ({x, y, z} : Set V) ∩ G.neighborSet w ⊆ ({c} : Set V) := by
    rintro t ⟨ht, hn⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
    rcases ht with rfl | rfl | rfl
    · exact hx hn
    · exact hy hn
    · exact hz hn
  intro htwo
  have hcard := Set.ncard_le_ncard hsub (Set.finite_singleton c)
  rw [Set.ncard_singleton] at hcard
  omega

private theorem formPrism_mid {G : SimpleGraph V} {A C B : Set V}
    {a₀ b₀ a₁ b₁ a₂ b₂ : V} {R₀ R₁ R₂ : List V}
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    FormPrism G ![a₁, a₀, a₂] ![b₁, b₀, b₂] R₁ R₀ R₂ := by
  have hbase :=
    Workspace.ProofLemmas.PrismFromBanisterAndStep.formPrism_of_banister_and_step hban hstep
  let aa : Fin 3 → V := ![a₁, a₂, a₀]
  let bb : Fin 3 → V := ![b₁, b₂, b₀]
  let RR : Fin 3 → List V := ![R₁, R₂, R₀]
  have hbase' : FormPrism G aa bb (RR 0) (RR 1) (RR 2) := by
    simpa [aa, bb, RR] using hbase
  let σ : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2
  have hp := Workspace.ProofLemmas.PrismSymmetry.formPrism_perm hbase' σ
  have hσ0 : σ 0 = 0 := by
    change Equiv.swap (1 : Fin 3) 2 0 = 0
    exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hσ1 : σ 1 = 2 := by
    change Equiv.swap (1 : Fin 3) 2 1 = 2
    exact Equiv.swap_apply_left _ _
  have hσ2 : σ 2 = 1 := by
    change Equiv.swap (1 : Fin 3) 2 2 = 1
    exact Equiv.swap_apply_right _ _
  have haa : (fun i => aa (σ i)) = ![a₁, a₀, a₂] := by
    funext i
    fin_cases i <;> simp [aa, hσ0, hσ1, hσ2]
  have hbb : (fun i => bb (σ i)) = ![b₁, b₀, b₂] := by
    funext i
    fin_cases i <;> simp [bb, hσ0, hσ1, hσ2]
  have hRR : (fun i => RR (σ i)) = ![R₁, R₀, R₂] := by
    funext i
    fin_cases i <;> simp [RR, hσ0, hσ1, hσ2]
  rw [haa, hbb, hRR] at hp
  simpa using hp

/-- The use of 10.4 in statement (1): an attachment on one step rung forces an
attachment on the other one. -/
private theorem other_rung_neighbor (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (A C B : Set V) (hS : StepConnected G A C B)
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hvB : VertexAnticomplete G v B)
    (P : List V) (hP : IsPathFrom G P v b₀)
    (hPavoid : ∀ w ∈ P, w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V))
    (hPint : Anticomplete G {w : V | w ∈ interior P} (A ∪ B ∪ C))
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hn₁ : ∃ x ∈ R₁, G.Adj v x) :
    ∃ y ∈ R₂, G.Adj v y := by
  classical
  obtain ⟨hR₀path, hR₀avoid, -, hright, hR₀int⟩ := id hban
  obtain ⟨hr₁, hr₂, hdisj, -⟩ := id hstep
  have ha₀R₀ : a₀ ∈ R₀ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR₀path).1
  have hb₀R₀ : b₀ ∈ R₀ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR₀path).2
  have ha₁R₁ : a₁ ∈ R₁ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).1
  have hb₁R₁ : b₁ ∈ R₁ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).2
  have ha₂R₂ : a₂ ∈ R₂ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).1
  have hb₂R₂ : b₂ ∈ R₂ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).2
  have ha₁A : a₁ ∈ A := hr₁.2.1
  have hb₁B : b₁ ∈ B := hr₁.2.2.1
  have ha₂A : a₂ ∈ A := hr₂.2.1
  have hb₂B : b₂ ∈ B := hr₂.2.2.1
  have hvP : v ∈ P := Workspace.ProofLemmas.PathBasics.head_mem hP.2.1
  have hva₀ : v ≠ a₀ := by
    intro he
    exact hPavoid v hvP (Or.inr (by simpa [he]))
  have hvb₀ : v ≠ b₀ := by
    obtain ⟨b, hbB⟩ := hS.2.1.2
    rintro rfl
    exact hvB b hbB (hright.2.1 b hbB)
  have hvR₀ : v ∉ R₀ := by
    intro hvR
    obtain ⟨x, hxR, hvx⟩ := hn₁
    exact hR₀int v
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR₀path).mpr
        ⟨hvR, hva₀, hvb₀⟩)
      x (rung_mem_strip hr₁ x hxR) hvx
  have hPlen : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
  have hPzero : P[0]'hPlen = v :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 hPlen
  have hPlast : P[P.length - 1]'(by omega) = b₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 hPlen
  obtain ⟨k, hk, ⟨hk', hkR₀⟩, hkmin⟩ :=
    exists_least_bounded (Q := fun i => ∃ hi : i < P.length, P[i]'hi ∈ R₀) P.length
      ⟨P.length - 1, by omega, by omega, by rw [hPlast]; exact hb₀R₀⟩
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [hPzero] at hkR₀
      exact (hvR₀ hkR₀).elim
    · exact hkpos
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let F : Set V := {x : V | x ∈ P.take (j + 1)}
  let K : Set V := {x : V | x ∈ R₁} ∪ {x : V | x ∈ R₀} ∪ {x : V | x ∈ R₂}
  have hFmem : ∀ x ∈ P.take (j + 1), x ∈ P :=
    fun x hx => List.mem_of_mem_take hx
  have hFnotR₀ : ∀ x ∈ P.take (j + 1), x ∉ R₀ := by
    intro x hx hxR
    obtain ⟨i, hi, hij, rfl⟩ := (mem_take_iff P (j + 1) x).mp hx
    exact hkmin i hij ⟨hi, hxR⟩
  have hFnotS : ∀ x ∈ P.take (j + 1), x ∉ A ∪ B ∪ C := by
    intro x hx hxS
    exact hPavoid x (hFmem x hx) (Or.inl hxS)
  have hvF : v ∈ F := by
    simp only [F, Set.mem_setOf_eq, mem_take_iff]
    exact ⟨0, hPlen, by omega, hPzero⟩
  have hFint : ∀ x ∈ P.take (j + 1), x ≠ v → x ∈ interior P := by
    intro x hx hxv
    obtain ⟨i, hi, hij, hix⟩ := (mem_take_iff P (j + 1) x).mp hx
    have hi0 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact (hxv (hix ▸ hPzero)).elim
      · exact hi0
    rw [← hix]
    exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hP.1 hi hi0 (by omega)
  have hFanti : ∀ x ∈ F, x ≠ v → VertexAnticomplete G x (A ∪ B ∪ C) := by
    intro x hx hxv
    exact hPint x (hFint x hx hxv)
  have hFK : F ⊆ Kᶜ := by
    intro x hx
    change x ∈ P.take (j + 1) at hx
    simp only [K, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq]
    rintro ((hx₁ | hx₀) | hx₂)
    · exact hFnotS x hx (rung_mem_strip hr₁ x hx₁)
    · exact hFnotR₀ x hx hx₀
    · exact hFnotS x hx (rung_mem_strip hr₂ x hx₂)
  have hFconn : ConnectedSet G F := by
    simp only [F]
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (Workspace.ProofLemmas.PathBasics.isPathList_take hP.1 (by omega))
  have hform : FormPrism G ![a₁, a₀, a₂] ![b₁, b₀, b₂] R₁ R₀ R₂ :=
    formPrism_mid hban hstep
  obtain ⟨x, hxR₁, hvx⟩ := hn₁
  have hxb₁ : x ≠ b₁ := fun he => hvB b₁ hb₁B (he ▸ hvx)
  have hzatt : P[j + 1]'hk' ∈ attachments G F K := by
    refine ⟨?_, P[j]'(by omega), ?_, ?_⟩
    · simp only [K, Set.mem_union, Set.mem_setOf_eq]
      exact Or.inl (Or.inr hkR₀)
    · simp only [F, Set.mem_setOf_eq, mem_take_iff]
      exact ⟨j, by omega, by omega, rfl⟩
    · exact (Workspace.ProofLemmas.PathBasics.path_adj_succ hP.1 (i := j) hk').symm
  have hxatt : x ∈ attachments G F K := by
    refine ⟨?_, v, hvF, hvx.symm⟩
    simp only [K, Set.mem_union, Set.mem_setOf_eq]
    exact Or.inl (Or.inl hxR₁)
  have hznea₀ : P[j + 1]'hk' ≠ a₀ := by
    intro he
    exact hPavoid _ (List.getElem_mem hk') (Or.inr (by simpa [he]))
  have hznotS : P[j + 1]'hk' ∉ A ∪ B ∪ C := hR₀avoid _ hkR₀
  have hxS : x ∈ A ∪ B ∪ C := rung_mem_strip hr₁ x hxR₁
  have hFloc : ¬ LocalForPrism ![a₁, a₀, a₂] ![b₁, b₀, b₂] R₁ R₀ R₂
      (attachments G F K) := by
    rintro (h | h | h | h | h)
    · exact hznotS (rung_mem_strip hr₁ _ (h hzatt))
    · exact hR₀avoid x (h hxatt) hxS
    · exact hznotS (rung_mem_strip hr₂ _ (h hzatt))
    · have hz := h hzatt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz
      · exact hznotS (hz ▸ Or.inl (Or.inl ha₁A))
      · exact hznea₀ hz
      · exact hznotS (hz ▸ Or.inl (Or.inl ha₂A))
    · have hx' := h hxatt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with hx' | hx' | hx'
      · exact hxb₁ hx'
      · exact hR₀avoid b₀ hb₀R₀ (hx' ▸ hxS)
      · exact hdisj x hxR₁ (hx' ▸ hb₂R₂)
  have hFmaj : IsEvenPrism G ![a₁, a₀, a₂] ![b₁, b₀, b₂] R₁ R₀ R₂ →
      ∀ y ∈ F, ¬ MajorForPrism G ![a₁, a₀, a₂] ![b₁, b₀, b₂] y := by
    intro _ y hy hmaj
    have htwo := hmaj.2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at htwo
    apply not_two_le_ncard (x := b₁) (y := b₀) (z := b₂) (c := b₀) (w := y) _ _ _ htwo
    · intro hyb
      by_cases hyv : y = v
      · exact (hvB b₁ hb₁B (hyv ▸ hyb)).elim
      · exact (hFanti y hy hyv b₁ (Or.inl (Or.inr hb₁B)) hyb).elim
    · exact fun _ => rfl
    · intro hyb
      by_cases hyv : y = v
      · exact (hvB b₂ hb₂B (hyv ▸ hyb)).elim
      · exact (hFanti y hy hyv b₂ (Or.inl (Or.inr hb₂B)) hyb).elim
  by_contra hnone
  push_neg at hnone
  have hR₃ : ∀ y ∈ attachments G F K, y ∉ R₂ := by
    intro y hy hyR₂
    obtain ⟨-, f, hf, hyf⟩ := hy
    by_cases hfv : f = v
    · subst f
      exact hnone y hyR₂ hyf.symm
    · exact hFanti f hf hfv y (rung_mem_strip hr₂ y hyR₂) hyf.symm
  have h104 := _root_.Workspace.Statements.S10.SPGT.thm_10_4 G hG hK4
    ![a₁, a₀, a₂] ![b₁, b₀, b₂] ![R₁, R₀, R₂] K F hform
    (by simp [K]) hFK hFconn hFmaj hFloc hR₃
  have hb₁att : b₁ ∈ attachments G F K := by
    rw [h104.2]
    simp
  obtain ⟨-, f, hf, hb₁f⟩ := hb₁att
  by_cases hfv : f = v
  · subst f
    exact hvB b₁ hb₁B hb₁f.symm
  · exact hFanti f hf hfv b₁ (Or.inl (Or.inr hb₁B)) hb₁f.symm

/-- Once both step rungs contain a neighbour, a further neighbour away from the two
left ends links `v` onto the right triangle, contradicting 2.4. -/
private theorem extra_neighbor_contradiction (G : SimpleGraph V) (hG : Berge G)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hvB : VertexAnticomplete G v B)
    (P : List V) (hP : IsPathFrom G P v b₀)
    (hPavoid : ∀ w ∈ P, w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V))
    (hPint : Anticomplete G {w : V | w ∈ interior P} (A ∪ B ∪ C))
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hn₁ : ∃ x ∈ R₁, x ≠ a₁ ∧ G.Adj v x)
    (hn₂ : ∃ x ∈ R₂, G.Adj v x) : False := by
  classical
  obtain ⟨-, -, -, hright, -⟩ := id hban
  obtain ⟨hr₁, hr₂, hdisj, hcross⟩ := id hstep
  have hb₁B : b₁ ∈ B := hr₁.2.2.1
  have hb₂B : b₂ ∈ B := hr₂.2.2.1
  have hlenP : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
  have hPzero : P[0]'hlenP = v :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 hlenP
  have hvb₀ : v ≠ b₀ := by
    rintro rfl
    exact hvB b₁ hb₁B (hright.2.1 b₁ hb₁B)
  have hlenP₂ : 2 ≤ P.length := by
    by_contra hc
    have hone : P.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hone
    have hxv : x = v := by simpa using hP.2.1
    have hxb : x = b₀ := by simpa using hP.2.2
    exact hvb₀ (hxv.symm.trans hxb)
  have hPtail : IsPathList G (P.drop 1) :=
    Workspace.ProofLemmas.PathBasics.isPathList_drop hP.1 (by omega)
  have hPtailLast : (P.drop 1).getLast? = some b₀ := by
    rw [List.getLast?_drop, if_neg (by omega)]
    exact hP.2.2
  have hPtailSub : ∀ x ∈ P.drop 1, x ∈ P :=
    fun x hx => List.mem_of_mem_drop hx
  have hPtailNeV : ∀ x ∈ P.drop 1, x ≠ v := by
    intro x hx hxv
    obtain ⟨s, hs, hsx⟩ :=
      (Workspace.ProofLemmas.Thm101ClaimOne.mem_drop_iff (p := P) (k := 1) (y := x)).mp hx
    have he : P[1 + s]'hs = P[0]'hlenP := by rw [hsx, hxv, hPzero]
    have := hP.1.2.1.getElem_inj_iff.mp he
    omega
  obtain ⟨w₁, hw₁R, hw₁a, hvw₁⟩ := hn₁
  obtain ⟨k₁, hk₁, hq₁, hvq₁, hsub₁, -, ha₁tail, hmax₁⟩ :=
    Workspace.ProofLemmas.Thm101ClaimOne.last_attach hr₁.1 ⟨w₁, hw₁R, hvw₁⟩
  have hlen₁ : 0 < R₁.length := Workspace.ProofLemmas.PathBasics.path_length_pos hr₁.1.1
  have hR₁zero : R₁[0]'hlen₁ = a₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hr₁.1.2.1 hlen₁
  obtain ⟨t₁, ht₁, ht₁w⟩ := List.mem_iff_getElem.mp hw₁R
  have ht₁pos : 0 < t₁ := by
    rcases Nat.eq_zero_or_pos t₁ with rfl | ht
    · exact (hw₁a (by rw [← ht₁w, hR₁zero])).elim
    · exact ht
  have hk₁pos : 0 < k₁ := by
    have hle := hmax₁ t₁ ht₁ (by rw [ht₁w]; exact hvw₁)
    omega
  have ha₁notTail : a₁ ∉ R₁.drop k₁ := by
    intro ha
    have he := ha₁tail.mp ha
    have hne := Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hr₁.1.1 hk₁ hlen₁
      (by omega : k₁ ≠ 0)
    rw [hR₁zero] at hne
    exact hne he
  obtain ⟨k₂, hk₂, hq₂, hvq₂, hsub₂, -, -, -⟩ :=
    Workspace.ProofLemmas.Thm101ClaimOne.last_attach hr₂.1 hn₂
  have edge_P_rung : ∀ {a b : V} {R Q : List V},
      IsRungOfStrip G A C B a R b → (∀ y ∈ Q, y ∈ R) →
      ∀ x ∈ P.drop 1, ∀ y ∈ Q,
        (G.Adj x y ↔ (x = b₀ ∧ y = b)) := by
    intro a b R Q hr hsub x hx y hy
    have hyR : y ∈ R := hsub y hy
    have hyS : y ∈ A ∪ B ∪ C := rung_mem_strip hr y hyR
    constructor
    · intro hxy
      by_cases hxb : x = b₀
      · refine ⟨hxb, ?_⟩
        subst x
        have hyB : y ∈ B := by
          rcases hyS with (hyA | hyB) | hyC
          · exact (hright.2.2 y (Or.inl hyA) hxy).elim
          · exact hyB
          · exact (hright.2.2 y (Or.inr hyC) hxy).elim
        exact hr.2.2.2.2.1 y hyR hyB
      · have hxint : x ∈ interior P :=
          (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP).mpr
            ⟨hPtailSub x hx, hPtailNeV x hx, hxb⟩
        exact (hPint x hxint y hyS hxy).elim
    · rintro ⟨rfl, rfl⟩
      exact hright.2.1 _ hr.2.2.1
  have hlink : VertexCanBeLinkedOntoTriangle G v b₀ b₁ b₂ := by
    refine ⟨P.drop 1, R₁.drop k₁, R₂.drop k₂,
      ⟨hPtail, hq₁.1, hq₂.1⟩, ⟨?_, ?_, ?_⟩,
      ⟨Or.inr hPtailLast, Or.inr hq₁.2.2, Or.inr hq₂.2.2⟩,
      ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · intro x hx hxR
      exact hPavoid x (hPtailSub x hx)
        (Or.inl (rung_mem_strip hr₁ x (hsub₁ x hxR)))
    · intro x hx hxR
      exact hPavoid x (hPtailSub x hx)
        (Or.inl (rung_mem_strip hr₂ x (hsub₂ x hxR)))
    · exact fun x hx hx' => hdisj x (hsub₁ x hx) (hsub₂ x hx')
    · exact fun x hx y hy => edge_P_rung hr₁ hsub₁ x hx y hy
    · exact fun x hx y hy => edge_P_rung hr₂ hsub₂ x hx y hy
    · intro x hx y hy
      rw [hcross x (hsub₁ x hx) y (hsub₂ y hy)]
      constructor
      · rintro (h | h)
        · exact (ha₁notTail (h.1 ▸ hx)).elim
        · exact h
      · exact fun h => Or.inr h
    · refine ⟨P[1]'(by omega), ?_, ?_⟩
      · exact (Workspace.ProofLemmas.Thm101ClaimOne.mem_drop_iff
          (p := P) (k := 1) (y := P[1]'(by omega))).mpr ⟨0, by omega, rfl⟩
      · have hpAdj := Workspace.ProofLemmas.PathBasics.path_adj_succ hP.1 (i := 0)
          (show 1 < P.length by omega)
        rw [hPzero] at hpAdj
        exact hpAdj
    · exact ⟨R₁[k₁]'hk₁,
        (Workspace.ProofLemmas.Thm101ClaimOne.mem_drop_iff
          (p := R₁) (k := k₁) (y := R₁[k₁]'hk₁)).mpr ⟨0, by omega, by simp⟩,
        hvq₁⟩
    · exact ⟨R₂[k₂]'hk₂,
        (Workspace.ProofLemmas.Thm101ClaimOne.mem_drop_iff
          (p := R₂) (k := k₂) (y := R₂[k₂]'hk₂)).mpr ⟨0, by omega, by simp⟩,
        hvq₂⟩
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG v b₀ b₁ b₂ hlink with
    ⟨-, hvb₁⟩ | ⟨-, hvb₂⟩ | ⟨hvb₁, -⟩
  · exact hvB b₁ hb₁B hvb₁
  · exact hvB b₂ hb₂B hvb₂
  · exact hvB b₁ hb₁B hvb₁

private theorem claim_oriented (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (A C B : Set V) (hS : StepConnected G A C B)
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hvB : VertexAnticomplete G v B)
    (P : List V) (hP : IsPathFrom G P v b₀)
    (hPavoid : ∀ w ∈ P, w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V))
    (hPint : Anticomplete G {w : V | w ∈ interior P} (A ∪ B ∪ C))
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hn₁ : ∃ x ∈ R₁, G.Adj v x) :
    G.Adj v a₁ ∧ G.Adj v a₂ ∧
      ∀ x : V, (x ∈ R₁ ∨ x ∈ R₂) → G.Adj v x → (x = a₁ ∨ x = a₂) := by
  have hn₂ := other_rung_neighbor G hG hK4 A C B hS a₀ b₀ R₀ hban v hvB P hP
    hPavoid hPint a₁ R₁ b₁ a₂ R₂ b₂ hstep hn₁
  have honly₁ : ∀ x ∈ R₁, G.Adj v x → x = a₁ := by
    intro x hx hvx
    by_contra hxa
    exact extra_neighbor_contradiction G hG A C B a₀ b₀ R₀ hban v hvB P hP hPavoid
      hPint a₁ R₁ b₁ a₂ R₂ b₂ hstep ⟨x, hx, hxa, hvx⟩ hn₂
  have hstep' : IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := step_symm hstep
  have honly₂ : ∀ x ∈ R₂, G.Adj v x → x = a₂ := by
    intro x hx hvx
    by_contra hxa
    exact extra_neighbor_contradiction G hG A C B a₀ b₀ R₀ hban v hvB P hP hPavoid
      hPint a₂ R₂ b₂ a₁ R₁ b₁ hstep' ⟨x, hx, hxa, hvx⟩ hn₁
  obtain ⟨x₁, hx₁, hvx₁⟩ := hn₁
  obtain ⟨x₂, hx₂, hvx₂⟩ := hn₂
  have hx₁eq := honly₁ x₁ hx₁ hvx₁
  have hx₂eq := honly₂ x₂ hx₂ hvx₂
  refine ⟨hx₁eq ▸ hvx₁, hx₂eq ▸ hvx₂, ?_⟩
  intro x hx hvx
  rcases hx with hx | hx
  · exact Or.inl (honly₁ x hx hvx)
  · exact Or.inr (honly₂ x hx hvx)

/-- Statement (1) of the printed proof of 11.1. -/
theorem thm111Claim1 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (A C B : Set V) (hS : StepConnected G A C B)
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ A ∪ B ∪ C)
    (hvB : SPGT.VertexAnticomplete G v B)
    (P : List V) (hP : IsPathFrom G P v b₀)
    (hPavoid : ∀ w ∈ P, w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V))
    (hPint : SPGT.Anticomplete G {w : V | w ∈ SPGT.interior P} (A ∪ B ∪ C))
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hnb : ∃ x : V, (x ∈ R₁ ∨ x ∈ R₂) ∧ G.Adj v x) :
    G.Adj v a₁ ∧ G.Adj v a₂ ∧
      ∀ x : V, (x ∈ R₁ ∨ x ∈ R₂) → G.Adj v x → (x = a₁ ∨ x = a₂) := by
  obtain ⟨x, hx, hvx⟩ := hnb
  rcases hx with hx | hx
  · exact claim_oriented G hG hK4 A C B hS a₀ b₀ R₀ hban v hvB P hP hPavoid hPint
      a₁ R₁ b₁ a₂ R₂ b₂ hstep ⟨x, hx, hvx⟩
  · obtain ⟨hva₂, hva₁, honly⟩ :=
      claim_oriented G hG hK4 A C B hS a₀ b₀ R₀ hban v hvB P hP hPavoid hPint
        a₂ R₂ b₂ a₁ R₁ b₁ (step_symm hstep) ⟨x, hx, hvx⟩
    refine ⟨hva₁, hva₂, ?_⟩
    intro y hy hvy
    rcases honly y hy.symm hvy with h | h
    · exact Or.inr h
    · exact Or.inl h

end Workspace.ProofLemmas.Thm111Claim1
