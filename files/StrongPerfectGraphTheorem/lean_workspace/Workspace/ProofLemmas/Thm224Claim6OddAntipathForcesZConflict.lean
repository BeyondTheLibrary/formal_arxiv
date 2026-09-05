import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.PathAttach
import Workspace.Statements.S02.Thm_2_2

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim6OddAntipathForcesZConflict

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

theorem thm224Claim6OddAntipathForcesZConflict
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u r L : List V} {Y A₀ : Set V} {z y u₁ u₂ : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u)
    (hlen : Even u.length)
    (hushape : u = u₁ :: u₂ :: r)
    (hL : IsPathFrom Gᶜ L u₁ (x (t + 1)))
    (hLint : ∀ w ∈ interior L, w ∈ wheelSystemX x t)
    (hext : IsPathFrom Gᶜ (z :: (L ++ [y])) z y)
    (heven : Even (pathLength (z :: (L ++ [y]))))
    (havoid : wheelSystemA G z A₀ x t ⊆ {w : V | w ∈ z :: (L ++ [y])}ᶜ) :
    False := by
  classical
  let A : Set V := wheelSystemA G z A₀ x t
  let X : Set V := wheelSystemX x t
  let q : V := x (t + 1)
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨-, -, -, -, hAconn, hzA, -, hxNbr, -, -, -, -, -, hqYy,
    -, hzXq, -, -, hyX, -, -, -, hyu, -⟩ := hcons
  change VertexAnticomplete G y (A ∪ {q}) at hcon
  change IsPathFrom Gᶜ L u₁ q at hL
  change (∀ w ∈ interior L, w ∈ X) at hLint
  change ConnectedSet G A at hAconn
  change VertexAnticomplete G z A at hzA
  change (∀ j ≤ t + 1, ∃ a ∈ A, G.Adj (x j) a) at hxNbr
  change q ∉ Y ∪ {y} at hqYy
  change VertexComplete G z (X ∪ {q}) at hzXq
  change VertexComplete G y X at hyX
  change A ⊆ {w : V | w ∈ z :: (L ++ [y])}ᶜ at havoid
  have hu₁u : u₁ ∈ u := by
    rw [hushape]
    simp
  have hu₁head : u.head? = some u₁ := by
    rw [hushape]
    simp
  have hyu₁ : G.Adj y u₁ := (hyu u₁ hu₁u).mpr hu₁head
  have hu₁Aanti : VertexAnticomplete G u₁ A := by
    apply hu.2.2.2.1 u₁
    rw [hushape]
    cases r <;> simp
  have hqy : q ≠ y := by
    intro hEq
    apply hqYy
    rw [hEq]
    simp
  have hyL : y ∉ L := by
    intro hyL
    have hnd : (z :: (L ++ [y])).Nodup := hext.1.2.1
    have hndtail : (L ++ [y]).Nodup := (List.nodup_cons.mp hnd).2
    exact (List.nodup_append.mp hndtail).2.2 y hyL y (by simp) rfl
  have hyq : Gᶜ.Adj y q :=
    (G.compl_adj y q).mpr ⟨hqy.symm, hcon q (Or.inr rfl)⟩
  have hyother : ∀ w ∈ L, w ≠ q → ¬ Gᶜ.Adj y w := by
    intro w hw hwq hyw
    by_cases hwu₁ : w = u₁
    · subst w
      exact ((G.compl_adj y u₁).mp hyw).2 hyu₁
    · have hwint : w ∈ interior L :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
          ⟨hw, hwu₁, hwq⟩
      exact ((G.compl_adj y w).mp hyw).2 (hyX w (hLint w hwint))
  have hK : IsPathFrom Gᶜ (L ++ [y]) u₁ y :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_concat hL hyq hyL hyother
  have hoddK : Odd (pathLength (L ++ [y])) := by
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff]
    simp only [pathLength, List.length_cons, List.length_append, List.length_nil] at heven ⊢
    omega
  have hnotA : ∀ {w : V}, w ∈ z :: (L ++ [y]) → w ∉ A := by
    intro w hw hwA
    exact (show w ∉ z :: (L ++ [y]) from havoid hwA) hw
  have hu₁L : u₁ ∈ L :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hL).1
  have hu₁notA : u₁ ∉ A :=
    hnotA (List.mem_cons_of_mem z (List.mem_append_left [y] hu₁L))
  have hynotA : y ∉ A := hnotA (by simp)
  have hznotA : z ∉ A := hnotA List.mem_cons_self
  have hu₁Ac : VertexComplete Gᶜ u₁ A := by
    intro a ha
    exact (G.compl_adj u₁ a).mpr
      ⟨fun hEq => hu₁notA (hEq.symm ▸ ha), hu₁Aanti a ha⟩
  have hyAc : VertexComplete Gᶜ y A := by
    intro a ha
    exact (G.compl_adj y a).mpr
      ⟨fun hEq => hynotA (hEq.symm ▸ ha), hcon a (Or.inl ha)⟩
  have hzAc : VertexComplete Gᶜ z A := by
    intro a ha
    exact (G.compl_adj z a).mpr
      ⟨fun hEq => hznotA (hEq.symm ▸ ha), hzA a ha⟩
  have hKout : ∀ w ∈ L ++ [y], w ∉ A := by
    intro w hw
    exact hnotA (List.mem_cons_of_mem z hw)
  have hintNotComplete : ∀ w ∈ interior (L ++ [y]), ¬ VertexComplete Gᶜ w A := by
    intro w hw hwAc
    obtain ⟨hwK, hwu₁, hwy⟩ :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hK).mp hw
    have hwL : w ∈ L := by
      rcases List.mem_append.mp hwK with hwL | hwy'
      · exact hwL
      · exact (hwy (by simpa using hwy')).elim
    by_cases hwq : w = q
    · subst w
      obtain ⟨a, ha, hqa⟩ := hxNbr (t + 1) (le_refl _)
      exact ((G.compl_adj q a).mp (hwAc a ha)).2 hqa
    · have hwLint : w ∈ interior L :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
          ⟨hwL, hwu₁, hwq⟩
      obtain ⟨j, hj, hwj⟩ := hLint w hwLint
      obtain ⟨a, ha, hxa⟩ := hxNbr j (by omega)
      have hwa : G.Adj w a := by
        rw [hwj]
        exact hxa
      exact ((G.compl_adj w a).mp (hwAc a ha)).2 hwa
  have hnoedge : ¬ ∃ a ∈ L ++ [y], ∃ b ∈ L ++ [y], EdgeComplete Gᶜ A a b := by
    rintro ⟨a, ha, b, hb, hab, haAc, hbAc⟩
    have haends : a = u₁ ∨ a = y := by
      by_cases hau₁ : a = u₁
      · exact Or.inl hau₁
      by_cases hay : a = y
      · exact Or.inr hay
      exact (hintNotComplete a
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hK).mpr
          ⟨ha, hau₁, hay⟩) haAc).elim
    have hbends : b = u₁ ∨ b = y := by
      by_cases hbu₁ : b = u₁
      · exact Or.inl hbu₁
      by_cases hby : b = y
      · exact Or.inr hby
      exact (hintNotComplete b
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hK).mpr
          ⟨hb, hbu₁, hby⟩) hbAc).elim
    rcases haends with rfl | rfl <;> rcases hbends with rfl | rfl
    · exact (Gᶜ).irrefl hab
    · exact ((G.compl_adj _ _).mp hab).2 (by simpa using hyu₁.symm)
    · exact ((G.compl_adj _ _).mp hab).2 (by simpa using hyu₁)
    · exact (Gᶜ).irrefl hab
  have hBerge : Berge G := hG.1.1.1.1.1
  have hBergeCompl : Berge Gᶜ := by
    constructor
    · exact hBerge.2
    · simpa only [compl_compl] using hBerge.1
  have hAanti : AnticonnectedSet Gᶜ A := by
    simpa only [AnticonnectedSet, compl_compl] using hAconn
  obtain ⟨w, hwint, hzw⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 Gᶜ hBergeCompl A hAanti (L ++ [y]) u₁ y
      hK hKout hoddK hu₁Ac hyAc hnoedge z hzAc
  obtain ⟨hwK, hwu₁, hwy⟩ :=
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hK).mp hwint
  have hwL : w ∈ L := by
    rcases List.mem_append.mp hwK with hwL | hwy'
    · exact hwL
    · exact (hwy (by simpa using hwy')).elim
  by_cases hwq : w = q
  · subst w
    exact ((G.compl_adj z q).mp hzw).2 (hzXq q (Or.inr rfl))
  · have hwLint : w ∈ interior L :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
        ⟨hwL, hwu₁, hwq⟩
    exact ((G.compl_adj z w).mp hzw).2 (hzXq w (Or.inl (hLint w hwLint)))

end Workspace.ProofLemmas.Thm224Claim6OddAntipathForcesZConflict
