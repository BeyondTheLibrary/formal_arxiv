import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.Statements.S13.Thm_13_6

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim6LongAntipathEven

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

theorem thm224Claim6LongAntipathEven
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u r : List V} {Y A₀ : Set V} {z y u₁ u₂ : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u)
    (hlen : Even u.length)
    (hushape : u = u₁ :: u₂ :: r)
    (hqu₁ : G.Adj (x (t + 1)) u₁)
    (hu₁notX : ¬ VertexComplete G u₁ (wheelSystemX x t)) :
    ∃ L : List V,
      IsPathFrom Gᶜ L u₁ (x (t + 1)) ∧
      (∀ w ∈ interior L, w ∈ wheelSystemX x t) ∧
      IsPathFrom Gᶜ (z :: (L ++ [y])) z y ∧
      4 ≤ pathLength (z :: (L ++ [y])) ∧
      Even (pathLength (z :: (L ++ [y]))) ∧
      wheelSystemA G z A₀ x t ⊆ {w : V | w ∈ z :: (L ++ [y])}ᶜ := by
  classical
  let A : Set V := wheelSystemA G z A₀ x t
  let X : Set V := wheelSystemX x t
  let q : V := x (t + 1)
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨-, hframe, hA₀sub, -, hAconn, hzA, hAnoX, hxNbr,
      -, hXanti, -, -, hqX, hqYy, hqXnc, hzXq, -, -, hyX, -, hpath,
      hzu, hyu, a, haA₀, b, hbA₀, hab, -, -, -, -, -⟩ := hcons
  change VertexAnticomplete G y (A ∪ {q}) at hcon
  change A₀ ⊆ A at hA₀sub
  change ConnectedSet G A at hAconn
  change VertexAnticomplete G z A at hzA
  change (∀ a ∈ A, ¬ VertexComplete G a X) at hAnoX
  change (∀ j ≤ t + 1, ∃ a ∈ A, G.Adj (x j) a) at hxNbr
  change AnticonnectedSet G X at hXanti
  change q ∉ X at hqX
  change q ∉ Y ∪ {y} at hqYy
  change ¬ VertexComplete G q X at hqXnc
  change VertexComplete G z (X ∪ {q}) at hzXq
  change VertexComplete G y X at hyX
  change ¬ VertexComplete G u₁ X at hu₁notX
  change G.Adj q u₁ at hqu₁
  have hpath' : IsPathList G (z :: y :: u₁ :: u₂ :: r) := by
    simpa only [hushape] using hpath
  have hnd : (z :: y :: u₁ :: u₂ :: r).Nodup := hpath'.2.1
  have hu₁u : u₁ ∈ u := by rw [hushape]; simp
  have hu₂u : u₂ ∈ u := by rw [hushape]; simp
  have hu₁drop : u₁ ∈ u.dropLast := by
    rw [hushape]
    cases r <;> simp
  have hu₁Aanti : VertexAnticomplete G u₁ A := hu.2.2.2.1 u₁ hu₁drop
  have hzy : G.Adj z y := by
    simpa using (Workspace.ProofLemmas.PathBasics.path_adj_succ hpath' (i := 0) (by simp))
  have hyu₁ : G.Adj y u₁ := by
    simpa using (Workspace.ProofLemmas.PathBasics.path_adj_succ hpath' (i := 1) (by simp))
  have hu₁u₂ : G.Adj u₁ u₂ := by
    simpa using (Workspace.ProofLemmas.PathBasics.path_adj_succ hpath' (i := 2) (by simp))
  have hzu₁ : z ≠ u₁ := by
    intro heq
    subst u₁
    exact (List.nodup_cons.mp hnd).1 (by simp)
  have hzyne : z ≠ y := hzy.ne
  have hyu₁ne : y ≠ u₁ := hyu₁.ne
  have hu₁u₂ne : u₁ ≠ u₂ := hu₁u₂.ne
  have htwo : ∀ v : V, ∃ c ∈ A, c ≠ v := by
    intro v
    by_cases hav : a = v
    · refine ⟨b, hA₀sub hbA₀, ?_⟩
      intro hbv
      exact hab (hav.trans hbv.symm)
    · exact ⟨a, hA₀sub haA₀, hav⟩
  have no_isolated_mem :
      ∀ v : V, VertexAnticomplete G v A → (∃ c ∈ A, c ≠ v) → v ∉ A := by
    intro v hvanti hex hvA
    obtain ⟨c, hcA, hcv⟩ := hex
    obtain ⟨P, hP, hPmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hAconn hvA hcA
    have hPpos : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
    have hP2 : 2 ≤ P.length := by
      by_contra hlt
      have hP1 : P.length = 1 := by omega
      obtain ⟨d, rfl⟩ : ∃ d, P = [d] := by
        cases P with
        | nil => simp at hP1
        | cons d l =>
          cases l with
          | nil => exact ⟨d, rfl⟩
          | cons e l => simp at hP1
      have hdv : d = v := Option.some_injective _ hP.2.1
      have hdc : d = c := Option.some_injective _ hP.2.2
      exact hcv (hdc.symm.trans hdv)
    have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
    have hP0 : P[0]'hPpos = v :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 hPpos
    rw [hP0] at hadj
    exact hvanti _ (hPmem _ (List.getElem_mem (show 1 < P.length by omega))) hadj
  have hzNotA : z ∉ A := no_isolated_mem z hzA (htwo z)
  have hu₁NotA : u₁ ∉ A := no_isolated_mem u₁ hu₁Aanti (htwo u₁)
  have hzq : G.Adj z q := hzXq q (Or.inr rfl)
  have hqNotA : q ∉ A := by
    intro hqA
    exact hzA q hqA hzq
  have hyNotA : y ∉ A := by
    intro hyA
    exact hAnoX y hyA hyX
  have hXNotA : ∀ w ∈ X, w ∉ A := by
    intro w hwX hwA
    exact hzA w hwA (hzXq w (Or.inl hwX))
  have hu₁NotX : u₁ ∉ X := by
    intro hu₁X
    exact hzu u₁ hu₁u (hzXq u₁ (Or.inl hu₁X))
  have hu₁Miss : ∃ w ∈ X, ¬ G.Adj u₁ w := by
    by_contra h
    apply hu₁notX
    intro w hw
    by_contra huw
    exact h ⟨w, hw, huw⟩
  have hqMiss : ∃ w ∈ X, ¬ G.Adj q w := by
    by_contra h
    apply hqXnc
    intro w hw
    by_contra hqw
    exact h ⟨w, hw, hqw⟩
  obtain ⟨L, hL, hLint⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_antipath_interior_in
      hXanti hu₁NotX hqX hu₁Miss hqMiss
  have hL3 : 3 ≤ L.length := by
    have hLpos : 0 < L.length := Workspace.ProofLemmas.PathBasics.path_length_pos hL.1
    by_contra hlt
    have hLle : L.length ≤ 2 := by omega
    by_cases hLone : L.length = 1
    · obtain ⟨d, rfl⟩ : ∃ d, L = [d] := by
        cases L with
        | nil => simp at hLone
        | cons d l =>
          cases l with
          | nil => exact ⟨d, rfl⟩
          | cons e l => simp at hLone
      have hdu : d = u₁ := by
        simpa only [List.head?_singleton, Option.some.injEq] using hL.2.1
      have hdq : d = q := by
        simpa only [List.getLast?_singleton, Option.some.injEq] using hL.2.2
      subst u₁
      rw [hdq] at hqu₁
      exact G.irrefl hqu₁
    · have hLtwo : L.length = 2 := by omega
      have hplen : pathLength L = 1 := by simp only [pathLength]; omega
      have hcadj := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hL hplen
      exact ((G.compl_adj u₁ q).mp hcadj).2 hqu₁.symm
  have hyqne : y ≠ q := by
    intro heq
    apply hqYy
    rw [← heq]
    simp
  have hyq : Gᶜ.Adj y q :=
    (G.compl_adj y q).mpr ⟨hyqne, hcon q (Or.inr rfl)⟩
  have hyNotL : y ∉ L := by
    intro hyL
    by_cases hyu : y = u₁
    · exact hyu₁ne hyu
    by_cases hyq' : y = q
    · exact hyqne hyq'
    have hyInt : y ∈ interior L :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
        ⟨hyL, hyu, hyq'⟩
    exact G.irrefl (hyX y (hLint y hyInt))
  have hyOther : ∀ w ∈ L, w ≠ q → ¬ Gᶜ.Adj y w := by
    intro w hw hwq hyw
    by_cases hwu : w = u₁
    · subst w
      exact ((G.compl_adj y u₁).mp hyw).2 hyu₁
    · have hwInt : w ∈ interior L :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
          ⟨hw, hwu, hwq⟩
      exact ((G.compl_adj y w).mp hyw).2 (hyX w (hLint w hwInt))
  have hLy : IsPathFrom Gᶜ (L ++ [y]) u₁ y :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_concat hL hyq hyNotL hyOther
  have hzNotL : z ∉ L := by
    intro hzL
    by_cases hzu : z = u₁
    · exact hzu₁ hzu
    by_cases hzq' : z = q
    · exact hzq.ne hzq'
    have hzInt : z ∈ interior L :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
        ⟨hzL, hzu, hzq'⟩
    exact G.irrefl (hzXq z (Or.inl (hLint z hzInt)))
  have hzNotLy : z ∉ L ++ [y] := by
    intro hzmem
    rcases List.mem_append.mp hzmem with hzL | hzy'
    · exact hzNotL hzL
    · exact hzyne (by simpa using hzy')
  have hzu₁c : Gᶜ.Adj z u₁ :=
    (G.compl_adj z u₁).mpr ⟨hzu₁, hzu u₁ hu₁u⟩
  have hzOther : ∀ w ∈ L ++ [y], w ≠ u₁ → ¬ Gᶜ.Adj z w := by
    intro w hw hwu zcw
    rcases List.mem_append.mp hw with hwL | hwy
    · by_cases hwq : w = q
      · subst w
        exact ((G.compl_adj z q).mp zcw).2 hzq
      · have hwInt : w ∈ interior L :=
          (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
            ⟨hwL, hwu, hwq⟩
        exact ((G.compl_adj z w).mp zcw).2 (hzXq w (Or.inl (hLint w hwInt)))
    · have hwy' : w = y := by simpa using hwy
      subst w
      exact ((G.compl_adj z y).mp zcw).2 hzy
  have hext : IsPathFrom Gᶜ (z :: (L ++ [y])) z y :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_cons hLy hzu₁c hzNotLy hzOther
  have hlarge : 4 ≤ pathLength (z :: (L ++ [y])) := by
    simp only [pathLength, List.length_cons, List.length_append, List.length_nil]
    omega
  let U : Set V := {w : V | w ∈ u₂ :: r}
  let W : Set V := A ∪ U
  have hUPath : IsPathList G (u₂ :: r) := by
    have hs := Workspace.ProofLemmas.PathBasics.isPathList_drop hpath' (k := 3) (by simp)
    simpa using hs
  have hUconn : ConnectedSet G U := by
    change ConnectedSet G {w : V | w ∈ u₂ :: r}
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hUPath
  let un : V := (u₂ :: r).getLast (by simp)
  have hunU : un ∈ U := by
    change un ∈ u₂ :: r
    unfold un
    exact List.getLast_mem (by simp)
  have hunlast : (u₂ :: r).getLast? = some un := List.getLast?_eq_some_getLast (by simp)
  have hunlastu : u.getLast? = some un := by
    rw [hushape, List.getLast?_cons_of_ne_nil (by simp), hunlast]
  have hundata := hu.2.2.1 un (by simp [hunlastu])
  obtain ⟨c, hcA, hunc⟩ := hundata.1
  have hWconn : ConnectedSet G W := by
    change ConnectedSet G (A ∪ U)
    apply Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hAconn hUconn
    exact Or.inr ⟨c, hcA, un, hunU, hunc.symm⟩
  have hWanti : AnticonnectedSet Gᶜ W := by
    simpa only [AnticonnectedSet, compl_compl] using hWconn
  have hzNotU : z ∉ U := by
    change z ∉ u₂ :: r
    intro hzU
    exact (List.nodup_cons.mp hnd).1 (by simp [hzU])
  have hyNotU : y ∉ U := by
    change y ∉ u₂ :: r
    intro hyU
    have htail := (List.nodup_cons.mp hnd).2
    exact (List.nodup_cons.mp htail).1 (by simp [hyU])
  have hu₁NotU : u₁ ∉ U := by
    change u₁ ∉ u₂ :: r
    intro huU
    have htail := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
    exact (List.nodup_cons.mp htail).1 huU
  have hAavoid : A ⊆ {w : V | w ∈ z :: (L ++ [y])}ᶜ := by
    intro w hwA hwK
    rcases (Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton.mp hwK) with
      rfl | hwL | rfl
    · exact hzNotA hwA
    · by_cases hwu : w = u₁
      · subst w; exact hu₁NotA hwA
      by_cases hwq : w = q
      · subst w; exact hqNotA hwA
      have hwInt : w ∈ interior L :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
          ⟨hwL, hwu, hwq⟩
      exact hXNotA w (hLint w hwInt) hwA
    · exact hyNotA hwA
  have hUavoid : U ⊆ {w : V | w ∈ z :: (L ++ [y])}ᶜ := by
    intro w hwU hwK
    change w ∈ u₂ :: r at hwU
    rcases (Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton.mp hwK) with
      rfl | hwL | rfl
    · exact hzNotU hwU
    · by_cases hwu : w = u₁
      · subst w; exact hu₁NotU hwU
      by_cases hwq : w = q
      · subst w
        have hqU : q ∈ u := by
          rw [hushape]
          exact List.mem_cons.mpr (Or.inr hwU)
        exact (hzu q hqU) hzq
      have hwInt : w ∈ interior L :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
          ⟨hwL, hwu, hwq⟩
      have hwXu : w ∈ X := hLint w hwInt
      have hwInu : w ∈ u := by
        rw [hushape]
        exact List.mem_cons.mpr (Or.inr hwU)
      exact hzu w hwInu (hzXq w (Or.inl hwXu))
    · exact hyNotU hwU
  have hWavoid : W ⊆ {w : V | w ∈ z :: (L ++ [y])}ᶜ := by
    intro w hwW
    rcases hwW with hwA | hwU
    · exact hAavoid hwA
    · exact hUavoid hwU
  have hzWc : VertexComplete Gᶜ z W := by
    intro w hwW
    have hwne : z ≠ w := by
      intro heq
      apply hWavoid hwW
      rw [← heq]
      exact List.mem_cons_self
    apply (G.compl_adj z w).mpr
    refine ⟨hwne, ?_⟩
    rcases hwW with hwA | hwU
    · exact hzA w hwA
    · change w ∈ u₂ :: r at hwU
      exact hzu w (by
        rw [hushape]
        exact List.mem_cons.mpr (Or.inr hwU))
  have hyWc : VertexComplete Gᶜ y W := by
    intro w hwW
    have hwne : y ≠ w := by
      intro heq
      apply hWavoid hwW
      rw [← heq]
      simp
    apply (G.compl_adj y w).mpr
    refine ⟨hwne, ?_⟩
    rcases hwW with hwA | hwU
    · exact hcon w (Or.inl hwA)
    · intro hyw
      change w ∈ u₂ :: r at hwU
      have hwu : w ∈ u := by
        rw [hushape]
        exact List.mem_cons.mpr (Or.inr hwU)
      have hhead := (hyu w hwu).mp hyw
      rw [hushape] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact hu₁NotU (hhead ▸ hwU)
  have hLnotWc : ∀ w ∈ L, ¬ VertexComplete Gᶜ w W := by
    intro w hwL hwWc
    by_cases hwu : w = u₁
    · subst w
      have hc := hwWc u₂ (Or.inr (by change u₂ ∈ u₂ :: r; simp))
      exact ((G.compl_adj u₁ u₂).mp hc).2 hu₁u₂
    by_cases hwq : w = q
    · subst w
      obtain ⟨d, hdA, hqd⟩ := hxNbr (t + 1) le_rfl
      have hc := hwWc d (Or.inl hdA)
      exact ((G.compl_adj q d).mp hc).2 hqd
    have hwInt : w ∈ interior L :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).mpr
        ⟨hwL, hwu, hwq⟩
    obtain ⟨j, hj, hwj⟩ := hLint w hwInt
    obtain ⟨d, hdA, hxd⟩ := hxNbr j (by omega)
    have hwd : G.Adj w d := by rw [hwj]; exact hxd
    have hc := hwWc d (Or.inl hdA)
    exact ((G.compl_adj w d).mp hc).2 hwd
  have hnoedge : ¬ ∃ a ∈ z :: (L ++ [y]), ∃ b ∈ z :: (L ++ [y]),
      EdgeComplete Gᶜ W a b := by
    rintro ⟨v, hvK, w, hwK, hvw, hvW, hwW⟩
    have hvends : v = z ∨ v = y := by
      rcases (Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton.mp hvK) with
        rfl | hvL | rfl
      · exact Or.inl rfl
      · exact (hLnotWc v hvL hvW).elim
      · exact Or.inr rfl
    have hwends : w = z ∨ w = y := by
      rcases (Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton.mp hwK) with
        rfl | hwL | rfl
      · exact Or.inl rfl
      · exact (hLnotWc w hwL hwW).elim
      · exact Or.inr rfl
    rcases hvends with hvz | hvy <;> rcases hwends with hwz | hwy
    · subst v
      subst w
      exact (Gᶜ).irrefl hvw
    · subst v
      subst w
      exact ((G.compl_adj z y).mp hvw).2 hzy
    · subst v
      subst w
      exact ((G.compl_adj y z).mp hvw).2 hzy.symm
    · subst v
      subst w
      exact (Gᶜ).irrefl hvw
  have hF5 : InF5 G := hG.1.1.1
  have hBerge : Berge G := hF5.1.1
  have hBergeC : Berge Gᶜ := by
    constructor
    · exact hBerge.2
    · simpa only [compl_compl] using hBerge.1
  have hF3C : InF3 Gᶜ := by
    refine ⟨hBergeC, ?_⟩
    intro n H hs
    obtain ⟨hleft, hright⟩ := hF5.1.2 n H hs
    exact ⟨by simpa only [compl_compl] using hright,
      by simpa only [compl_compl] using hleft⟩
  have hF5C : InF5 Gᶜ := by
    refine ⟨hF3C, hF5.2.2, ?_⟩
    simpa only [compl_compl] using hF5.2.1
  have heven : Even (pathLength (z :: (L ++ [y]))) := by
    apply Nat.not_odd_iff_even.mp
    intro hodd
    rcases Workspace.Statements.S13.SPGT.thm_13_6 Gᶜ hF5C
        (z :: (L ++ [y])) z y hext hodd W hWavoid hWanti hzWc hyWc with hedge | hshort
    · exact hnoedge hedge
    · omega
  exact ⟨L, hL, hLint, hext, hlarge, heven, hAavoid⟩

end Workspace.ProofLemmas.Thm224Claim6LongAntipathEven


