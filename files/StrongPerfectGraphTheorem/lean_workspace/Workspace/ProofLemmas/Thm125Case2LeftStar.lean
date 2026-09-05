import Workspace.ProofLemmas.Thm125Case2Prelude
import Workspace.ProofLemmas.Thm114Endgame
import Workspace.ProofLemmas.Thm114Balanced

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The 11.4 step inside case (2) of Theorem 12.5

The printed proof invokes 11.4 after finding a vertex in the old banister complete to the
displayed antipath.  Here the antipath already has the endpoint-minimality properties used in
the proof of 11.4, so we apply its proved endgame directly.  This keeps the argument independent
of the still-unneeded general 11.4 scaffold.
-/

namespace Workspace.ProofLemmas.Thm125Case2LeftStar

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the asymmetric endpoint case of 12.5, the left endpoint is a left-star. -/
theorem leftStar
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : G.Adj q₁ a₀) (hqkb₀ : ¬ G.Adj qk b₀)
    (t : V) (htint : t ∈ interior R₀)
    (htQ : VertexComplete G t {z : V | z ∈ q}) :
    IsLeftStar G A C B q₁ := by
  classical
  by_contra hnleft
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hS : StepConnected G A C B := hstair.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hstair.2.1
  have hodd := Workspace.Statements.S11.SPGT.thm_11_3 G hG hprism A C B hS
    a₀ b₀ R₀ hban
  have hne : q₁ ≠ qk := endpoint_ne hq hq₁ hqk
  have hq2 : 2 ≤ q.length := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
    by_contra hc
    have hlen : q.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have h1 : x = q₁ := by simpa using hq.2.1
    have hk : x = qk := by simpa using hq.2.2
    exact hne (h1.symm.trans hk)
  have hBneigh : ∃ b ∈ B, G.Adj q₁ b := by
    obtain ⟨i, hi, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1 G hG hK4 hprism
      hbreaker A C B a₀ b₀ R₀ hK.1 q₁ hq₁.1.1
    fin_cases i
    · exfalso
      rcases hi.2.1 with hs | hnA
      · exact hnleft hs
      · exact hnA (fun a ha => hq₁.1.2 a (Or.inl ha))
    · exact hi.1.2.2.1
    · rcases hi with hs | hs
      · exact (hnleft hs.1).elim
      · exfalso
        obtain ⟨a, ha⟩ := hS.2.1.1
        exact hs.1.2.2 a (Or.inl ha) (hq₁.1.2 a (Or.inl ha))
  have hBmiss : ∃ b ∈ B, ¬ G.Adj q₁ b := by
    by_contra hno
    push_neg at hno
    exact hq₁.2 ⟨hq₁.1.1, by
      intro x hx
      rcases hx with hxB | rfl
      · exact hno x hxB
      · exact hqa₀⟩
  let B₁ : Set V := {b : V | b ∈ B ∧ G.Adj q₁ b}
  let B₂ : Set V := {b : V | b ∈ B ∧ ¬ G.Adj q₁ b}
  have hBunion : B₁ ∪ B₂ = B := by
    ext b
    simp only [B₁, B₂, Set.mem_union, Set.mem_setOf_eq]
    by_cases h : G.Adj q₁ b <;> simp [h]
  have hBdisj : Disjoint B₁ B₂ := by
    rw [Set.disjoint_left]
    rintro b ⟨-, hb⟩ ⟨-, hnb⟩
    exact hnb hb
  have hB₁ne : B₁.Nonempty := by
    obtain ⟨b, hb, hadj⟩ := hBneigh
    exact ⟨b, hb, hadj⟩
  have hB₂ne : B₂.Nonempty := by
    obtain ⟨b, hb, hadj⟩ := hBmiss
    exact ⟨b, hb, hadj⟩
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hend₁, hend₂⟩ :=
    hS.2.2.2.2 B₁ B₂ (Or.inr hBunion) hBdisj hB₁ne hB₂ne
  have hb₁B₁ : b₁ ∈ B₁ := by
    rcases hend₁ with ha | hb
    · exact (Set.disjoint_left.mp hS.1.1 hstep.1.2.1 ha.1).elim
    · exact hb
  have hb₂B₂ : b₂ ∈ B₂ := by
    rcases hend₂ with ha | hb
    · exact (Set.disjoint_left.mp hS.1.1 hstep.2.1.2.1 ha.1).elim
    · exact hb
  have hb₁B : b₁ ∈ B := hb₁B₁.1
  have hb₂B : b₂ ∈ B := hb₂B₂.1
  have hq₁b₁ : G.Adj q₁ b₁ := hb₁B₁.2
  have hq₁b₂ : ¬ G.Adj q₁ b₂ := hb₂B₂.2
  let qr : List V := q.reverse
  have hqr : IsAntipathFrom G qr qk q₁ := by
    dsimp [qr]
    exact Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hq
  have hqrS : ∀ x ∈ qr, x ∉ A ∪ B ∪ C := by
    intro x hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    exact fun hs => outside_of_mem hq hqint hq₁.1 hqk.1 hxq (Or.inr hs)
  have hqrR₀ : ∀ x ∈ qr, x ∉ R₀ := by
    intro x hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    exact fun hR => outside_of_mem hq hqint hq₁.1 hqk.1 hxq (Or.inl hR)
  have ha₀qr : ∀ x ∈ qr, G.Adj a₀ x := by
    intro x hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    by_cases hx₁ : x = q₁
    · simpa [hx₁] using hqa₀.symm
    · exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hxq hx₁).2 a₀
        (Or.inr rfl)).symm
  have hb₁qr : ∀ x ∈ qr, G.Adj b₁ x := by
    intro x hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    by_cases hx₁ : x = q₁
    · simpa [hx₁] using hq₁b₁.symm
    · exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hxq hx₁).2 b₁
        (Or.inl hb₁B)).symm
  have hb₀start : ¬ G.Adj b₀ qk := fun h => hqkb₀ h.symm
  have hb₀tail : ∀ x ∈ qr.tail, G.Adj b₀ x := by
    intro x hx
    have hxqr : x ∈ qr := List.mem_of_mem_tail hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hxqr)
    have hxk : x ≠ qk := by
      intro he
      have hhead : qr.head? = some qk := hqr.2.1
      have hqkhead : qk ∈ qr.head? := by rw [hhead]; simp
      have hcons : qk :: qr.tail = qr := List.cons_head?_tail hqkhead
      have hnd : (qk :: qr.tail).Nodup := by rw [hcons]; exact hqr.1.2.1
      exact (List.nodup_cons.1 hnd).1 (he ▸ hx)
    exact ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hxq hxk).2 b₀
      (Or.inr rfl)).symm
  have hb₂finish : ¬ G.Adj b₂ q₁ := fun h => hq₁b₂ h.symm
  have hb₂drop : ∀ x ∈ qr.dropLast, G.Adj b₂ x := by
    intro x hx
    have hxqr : x ∈ qr := List.mem_of_mem_dropLast hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hxqr)
    have hlast : qr.getLast hqr.1.1 = q₁ := by
      have h := hqr.2.2
      rw [List.getLast?_eq_some_getLast hqr.1.1] at h
      exact Option.some_injective _ h
    have hx₁ : x ≠ q₁ := by
      have hm := (Workspace.ProofLemmas.PathBasics.mem_dropLast_iff hqr.1.2.1 hqr.1.1).1 hx
      simpa [hlast] using hm.2
    exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hxq hx₁).2 b₂
      (Or.inl hb₂B)).symm
  let F : Set V := {x : V | x ∈ interior R₀}
  let X : Set V := insert b₀ {x : V | x ∈ qr}
  have hFconn : ConnectedSet G F := by
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (Workspace.ProofLemmas.PathGlue.isPathFrom_interior hban.1.1 (by
        have hlen := hstair.2.2
        rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hlen
        omega)).1
  have hFS : Anticomplete G F (A ∪ B ∪ C) := by
    simpa [F] using hban.2.2.2.2
  have hSFX : A ∪ B ∪ C ⊆ (F ∪ X)ᶜ := by
    intro x hxS hxmem
    rcases hxmem with hxF | hxX
    · exact hban.2.1 x (Workspace.ProofLemmas.PathBasics.interior_subset hxF) hxS
    · rcases hxX with rfl | hxqr
      · exact hban.2.2.2.1.1 hxS
      · exact hqrS x hxqr hxS
  have hFX : Disjoint F X := by
    rw [Set.disjoint_left]
    intro x hxF hxX
    rcases hxX with rfl | hxqr
    · exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 hxF |>.2.2 rfl
    · exact hqrR₀ x hxqr (Workspace.ProofLemmas.PathBasics.interior_subset hxF)
  have hR₀len : 4 ≤ R₀.length := by
    have hlen := hstair.2.2
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hlen
    omega
  let fR : V := R₀[R₀.length - 2]'(by omega)
  have hfRF : fR ∈ F := by
    exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hban.1.1
      (k := R₀.length - 2) (by omega) (by omega) (by omega)
  have hb₀fR : G.Adj b₀ fR := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hban.1.1
      (i := R₀.length - 2) (by omega)
    have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 (by omega)
    have he : R₀[R₀.length - 2 + 1]'(by omega) = b₀ := by
      calc
        R₀[R₀.length - 2 + 1]'(by omega) = R₀[R₀.length - 1]'(by omega) := by
          congr 1 <;> omega
        _ = b₀ := hl
    exact he ▸ h.symm
  have hXnbr : ∀ x ∈ X, ∃ f ∈ F, G.Adj x f := by
    intro x hx
    rcases hx with rfl | hxqr
    · exact ⟨fR, hfRF, hb₀fR⟩
    · have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hxqr)
      exact ⟨t, htint, (htQ x hxq).symm⟩
  have hb₁F : VertexAnticomplete G b₁ F := by
    intro x hx hadj
    exact hFS x hx b₁ (Or.inl (Or.inr hb₁B)) hadj.symm
  have hb₁FX : b₁ ∉ F ∪ X := by
    rintro (hbF | hbX)
    · exact hban.2.1 b₁ (Workspace.ProofLemmas.PathBasics.interior_subset hbF)
        (Or.inl (Or.inr hb₁B))
    · rcases hbX with hb0 | hbq
      · exact hban.2.2.2.1.1 (hb0.symm ▸ Or.inl (Or.inr hb₁B))
      · exact hqrS b₁ hbq (Or.inl (Or.inr hb₁B))
  have hb₁X : VertexComplete G b₁ X := by
    intro x hx
    rcases hx with rfl | hxqr
    · exact (hban.2.2.2.1.2.1 b₁ hb₁B).symm
    · exact hb₁qr x hxqr
  have hbal : Balanced G (A ∪ B ∪ C) X :=
    Workspace.ProofLemmas.Thm114Balanced.balanced_of_complete_star hG
      (A ∪ B ∪ C) F X hFconn hFS hSFX hFX hXnbr b₁ hb₁FX hb₁X hb₁F
  exact Workspace.ProofLemmas.Thm114Endgame.thm114_endgame hG A C B a₀ b₀ R₀ hban
    hodd.2 a₁ b₁ a₂ b₂ R₁ R₂ hstep (hodd.1 a₂ R₂ b₂ hstep.2.1)
    qr qk q₁ hqr (by simpa [qr] using hq2) hqrS hqrR₀ ha₀qr hb₁qr hb₀start hb₀tail
    hb₂finish hb₂drop hbal

end Workspace.ProofLemmas.Thm125Case2LeftStar
