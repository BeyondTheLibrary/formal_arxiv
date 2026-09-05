import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.Thm224MinimalNeighborHole
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.Statements.S17.Thm_17_1

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224HatCatchContradiction

open Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

private theorem triangle_ne
    {V : Type*} {G : SimpleGraph V} {b₁ b₂ b₃ : V}
    (h : IsTriangle G ({b₁, b₂, b₃} : Set V)) :
    b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ := by
  have hpair : ∀ a b : V, ({a, b} : Set V).ncard ≤ 2 := by
    intro a b
    have hle := Set.ncard_insert_le a ({b} : Set V)
    simpa using hle
  have hcard := h.1
  refine ⟨?_, ?_, ?_⟩ <;> intro he
  · have hs : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by
      ext v
      simp [he]
    rw [hs] at hcard
    exact (by have := hpair b₂ b₃; omega)
  · have hs : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by
      ext v
      simp [he]
    rw [hs] at hcard
    exact (by have := hpair b₂ b₃; omega)
  · have hs : ({b₁, b₂, b₃} : Set V) = ({b₁, b₃} : Set V) := by
      ext v
      simp [he]
    rw [hs] at hcard
    exact (by have := hpair b₁ b₃; omega)

/-- Two distinct vertices of a triangle have adjacent partners in any reflection. -/
private theorem reflection_pair
    {V : Type*} {G : SimpleGraph V} {a₁ a₂ a₃ b₁ b₂ b₃ u v : V}
    (h : IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃)
    (hu : u ∈ ({a₁, a₂, a₃} : Set V))
    (hv : v ∈ ({a₁, a₂, a₃} : Set V)) (huv : u ≠ v) :
    ∃ bu ∈ ({b₁, b₂, b₃} : Set V), ∃ bv ∈ ({b₁, b₂, b₃} : Set V),
      G.Adj u bu ∧ G.Adj v bv ∧ G.Adj bu bv := by
  obtain ⟨hA, hB, hdisj, hiff⟩ := h
  obtain ⟨hb12, hb13, hb23⟩ := triangle_ne hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · exact ⟨b₁, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hb12⟩
  · exact ⟨b₁, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hb13⟩
  · exact ⟨b₂, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) hb12.symm⟩
  · exact absurd rfl huv
  · exact ⟨b₂, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hb23⟩
  · exact ⟨b₃, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) hb13.symm⟩
  · exact ⟨b₃, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hb23.symm⟩
  · exact absurd rfl huv

/-- A hat on the minimal-neighbour hole yields the explicit catch obstruction of 17.1. -/
theorem thm224HatCatchContradiction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u : List V} {Y A₀ : Set V} {z y : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u)
    (hlen : Even u.length)
    (hadj : ∃ v ∈ u.dropLast, G.Adj (x (t + 1)) v)
    (hXt : ∀ v ∈ u.dropLast, ¬ VertexComplete G v (wheelSystemX x t))
    {k : ℕ} (hk : k < u.dropLast.length)
    (hqk : G.Adj (x (t + 1)) (u.dropLast[k]'hk))
    (hleast : ∀ (j : ℕ) (hj : j < k),
      ¬ G.Adj (x (t + 1)) (u.dropLast[j]'(lt_trans hj hk)))
    (hH :
      let H := [z, y] ++ u.take (k + 1) ++ [x (t + 1)]
      IsHoleList G H ∧
      6 ≤ holeLength H ∧
      (∀ w ∈ H, w ∉ wheelSystemX x t) ∧
      (∀ w ∈ H, VertexComplete G w (wheelSystemX x t) ↔ w = z ∨ w = y)) :
    let H := [z, y] ++ u.take (k + 1) ++ [x (t + 1)]
    ∀ h ∈ wheelSystemX x t, IsHatForHole G H z y h → False := by
  classical
  dsimp only
  intro h hhX hhat
  let q := x (t + 1)
  let A := wheelSystemA G z A₀ x t
  let U : Set V := {v : V | v ∈ u}
  let H := [z, y] ++ u.take (k + 1) ++ [q]
  let F := (A ∪ U) ∪ {q}
  let K : Set V := {z, y, h}
  change IsHatForHole G H z y h at hhat
  change IsHoleList G H ∧ 6 ≤ holeLength H ∧
      (∀ w ∈ H, w ∉ wheelSystemX x t) ∧
      (∀ w ∈ H, VertexComplete G w (wheelSystemX x t) ↔ w = z ∨ w = y) at hH
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  have hdl : u.dropLast.length = u.length - 1 := List.length_dropLast
  have hulen : k + 2 ≤ u.length := by omega
  have htakeLen : (u.take (k + 1)).length = k + 1 := by
    rw [List.length_take]
    omega
  have hHlen : H.length = k + 4 := by
    simp only [H, q, List.length_append, List.length_cons, List.length_nil,
      List.length_singleton, htakeLen]
    omega
  have hk2 : 2 ≤ k := by
    have h6 := hH.2.1
    change 6 ≤ H.length at h6
    rw [hHlen] at h6
    omega
  have huPos : 0 < u.length := by omega
  have hdropPos : 0 < u.dropLast.length := by omega
  let u₁ := u[0]'huPos
  have hu₁u : u₁ ∈ u := List.getElem_mem huPos
  have hu₁head : u.head? = some u₁ := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem huPos]
  have htakePos : 0 < (u.take (k + 1)).length := by rw [htakeLen]; omega
  have hu₁take : u₁ ∈ u.take (k + 1) := by
    have he : (u.take (k + 1))[0]'htakePos = u₁ := by simp [u₁]
    rw [← he]
    exact List.getElem_mem htakePos
  have hzH : z ∈ H := by simp [H]
  have hyH : y ∈ H := by simp [H]
  have hu₁H : u₁ ∈ H := by simp [H, hu₁take]
  have hqH : q ∈ H := by simp [H]
  have hzy : G.Adj z y := hhat.2.2.2.1
  have hhz : G.Adj h z := hhat.2.2.2.2.1
  have hhy : G.Adj h y := hhat.2.2.2.2.2.1
  have hhonly : ∀ v ∈ H, v ≠ z → v ≠ y → ¬ G.Adj h v :=
    hhat.2.2.2.2.2.2
  have hzq : G.Adj z q := by simpa [q] using hzXq (x (t + 1)) (Or.inr rfl)
  have hqneY : q ≠ y := by
    intro he
    exact hqYy (by simpa [q, he])
  have hu₁neZ : u₁ ≠ z := by
    intro he
    exact (List.nodup_cons.mp hpath.2.1).1
      (List.mem_cons_of_mem y (he ▸ hu₁u))
  have hu₁neY : u₁ ≠ y := by
    intro he
    exact (List.nodup_cons.mp (List.nodup_cons.mp hpath.2.1).2).1
      (he ▸ hu₁u)
  have hhu₁ : ¬ G.Adj h u₁ := hhonly u₁ hu₁H hu₁neZ hu₁neY
  have hqneZ : q ≠ z := hzq.ne.symm
  have hhq : ¬ G.Adj h q := hhonly q hqH hqneZ hqneY
  have hqneH : q ≠ h := by
    intro he
    exact hqX (by simpa [q, he] using hhX)
  have hqU₁ : ¬ G.Adj q u₁ := by
    have h0 := hleast 0 (by omega)
    have he : (u.dropLast)[0]'hdropPos = u₁ := by
      simp [u₁]
    simpa [q, he] using h0

  have huPath : IsPathList G u := by
    have hp := Workspace.ProofLemmas.PathBasics.isPathList_drop hpath (k := 2)
      (by simp only [List.length_cons]; omega)
    simpa using hp
  have hUconn : ConnectedSet G U := by
    exact Workspace.ProofLemmas.KiteTailBasics.connectedSet_of_isPathList huPath
  let un := u.getLast hu.2.1
  have hunopt : un ∈ u.getLast? := by
    simp [un, List.getLast?_eq_some_getLast hu.2.1]
  obtain ⟨c, hcA, hunc⟩ := (hu.2.2.1 un hunopt).1
  have hAUconn : ConnectedSet G (A ∪ U) := by
    apply Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hAconn hUconn
    exact Or.inr ⟨c, hcA, un,
      (Workspace.ProofLemmas.PathBasics.getLast_mem
        (List.getLast?_eq_some_getLast hu.2.1)), hunc.symm⟩
  have hFconn : ConnectedSet G F := by
    apply Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton hAUconn
    obtain ⟨c, hcA, hqc⟩ := hxNbr (t + 1) (by omega)
    exact ⟨c, Or.inl hcA, by simpa [q] using hqc⟩

  have hA_two : ∀ v : V, v ∈ A → ∃ c ∈ A, c ≠ v := by
    intro v hv
    by_cases hva : v = a
    · exact ⟨b, hA₀sub hb, by simpa [hva] using hab.symm⟩
    · exact ⟨a, hA₀sub ha, fun hav => hva hav.symm⟩
  have hanti_not_mem : ∀ v : V, VertexAnticomplete G v A → v ∉ A := by
    intro v hvanti hvA
    obtain ⟨c, hc, hcv⟩ := hA_two v hvA
    obtain ⟨L, hL, hLmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hAconn hvA hc
    have hLtwo : 2 ≤ L.length := by
      have hLpos := Workspace.ProofLemmas.PathBasics.path_length_pos hL.1
      by_contra hlt
      have hLone : L.length = 1 := by omega
      obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hLone
      have hdv : d = v := by simpa using hL.2.1
      have hdc : d = c := by simpa using hL.2.2
      exact hcv (hdc.symm.trans hdv)
    have hedge := Workspace.ProofLemmas.PathBasics.path_adj_succ hL.1
      (i := 0) (by omega)
    have hzero : L[0]'(by omega) = v :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hL.2.1 (by omega)
    rw [hzero] at hedge
    exact hvanti _ (hLmem _ (List.getElem_mem (show 1 < L.length by omega))) hedge
  have hzNotA : z ∉ A := hanti_not_mem z hzA
  have hyNotA : y ∉ A :=
    hanti_not_mem y (fun v hv => hcon v (Or.inl hv))
  have hzNotU : z ∉ U := by
    intro hzU
    exact (List.nodup_cons.mp hpath.2.1).1 (List.mem_cons_of_mem y hzU)
  have hyNotU : y ∉ U := by
    intro hyU
    exact (List.nodup_cons.mp (List.nodup_cons.mp hpath.2.1).2).1 hyU
  have hqNotA : q ∉ A := by
    intro hqA
    exact hzA q hqA hzq
  have hqNotU : q ∉ U := by
    intro hqU
    exact hzu q hqU hzq
  have hhNotA : h ∉ A := by
    intro hhA
    exact hzA h hhA hhz.symm
  have hhNotU : h ∉ U := by
    intro hhU
    exact hzu h hhU hhz.symm
  have hzNotF : z ∉ F := by simp [F, hzNotA, hzNotU, hqneZ.symm]
  have hyNotF : y ∉ F := by simp [F, hyNotA, hyNotU, hqneY.symm]
  have hhNotF : h ∉ F := by simp [F, hhNotA, hhNotU, hqneH.symm]
  have hFK : F ⊆ Kᶜ := by
    intro v hvF hvK
    simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hvK
    rcases hvK with rfl | rfl | rfl
    · exact hzNotF hvF
    · exact hyNotF hvF
    · exact hhNotF hvF

  have hKtri : IsTriangle G K := by
    refine ⟨Set.ncard_eq_three.mpr ⟨z, y, h, hzy.ne, ?_, ?_, rfl⟩, ?_⟩
    · exact hhz.ne.symm
    · exact hhy.ne.symm
    · intro v hv w hw hvw
      simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
      rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      · exact (hvw rfl).elim
      · exact hzy
      · exact hhz.symm
      · exact hzy.symm
      · exact (hvw rfl).elim
      · exact hhy.symm
      · exact hhz
      · exact hhy
      · exact (hvw rfl).elim
  have hcatchAdj : ∀ v ∈ K, ∃ f ∈ F, G.Adj v f := by
    intro v hv
    simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨q, by simp [F], hzq⟩
    · exact ⟨u₁, by simp [F, U, hu₁u], (hyu u₁ hu₁u).mpr hu₁head⟩
    · obtain ⟨j, hj, hhj⟩ := hhX
      obtain ⟨c, hcA, hjc⟩ := hxNbr j (by omega)
      refine ⟨c, Or.inl (Or.inl hcA), ?_⟩
      simpa [hhj] using hjc
  have hcatch : Catches G F K :=
    ⟨hKtri, hFconn, Set.disjoint_left.mpr hFK, hcatchAdj⟩

  have hzUnique : ∀ f ∈ F, G.Adj z f → f = q := by
    intro f hf hzf
    rcases hf with (hfA | hfU) | hfq
    · exact (hzA f hfA hzf).elim
    · exact (hzu f hfU hzf).elim
    · simpa using hfq
  have hyUnique : ∀ f ∈ F, G.Adj y f → f = u₁ := by
    intro f hf hyf
    rcases hf with (hfA | hfU) | hfq
    · exact (hcon f (Or.inl hfA) hyf).elim
    · exact Option.some.inj (hu₁head.symm.trans ((hyu f hfU).mp hyf)) |>.symm
    · have hfq' : f = q := by simpa using hfq
      exact (hcon q (Or.inr (by simp [q])) (hfq' ▸ hyf)).elim

  have hncard : ∀ f ∈ F, (G.neighborSet f ∩ K).ncard ≤ 1 := by
    have bound : ∀ (f w : V), (G.neighborSet f ∩ K) ⊆ ({w} : Set V) →
        (G.neighborSet f ∩ K).ncard ≤ 1 := by
      intro f w hsub
      have hle := Set.ncard_le_ncard hsub (Set.finite_singleton w)
      simpa using hle
    intro f hf
    rcases hf with (hfA | hfU) | hfq
    · refine bound f h ?_
      rintro v ⟨hfv, hvK⟩
      have hfv' : G.Adj f v := by simpa only [SimpleGraph.mem_neighborSet] using hfv
      simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hvK
      rcases hvK with rfl | rfl | rfl
      · exact (hzA f hfA hfv'.symm).elim
      · exact (hcon f (Or.inl hfA) hfv'.symm).elim
      · rfl
    · apply (Set.ncard_le_one (Set.toFinite _)).mpr
      intro v hv w hw'
      obtain ⟨hfv, hvK⟩ := hv
      obtain ⟨hfw, hwK⟩ := hw'
      have hfv' : G.Adj f v := by simpa only [SimpleGraph.mem_neighborSet] using hfv
      have hfw' : G.Adj f w := by simpa only [SimpleGraph.mem_neighborSet] using hfw
      simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hvK hwK
      rcases hvK with rfl | rfl | rfl <;> rcases hwK with rfl | rfl | rfl
      · rfl
      · exact (hzu f hfU hfv'.symm).elim
      · exact (hzu f hfU hfv'.symm).elim
      · exact (hzu f hfU hfw'.symm).elim
      · rfl
      · have hfu₁ : f = u₁ :=
          Option.some.inj (hu₁head.symm.trans ((hyu f hfU).mp hfv'.symm)) |>.symm
        exact (hhu₁ (hfu₁ ▸ hfw').symm).elim
      · exact (hzu f hfU hfw'.symm).elim
      · have hfu₁ : f = u₁ :=
          Option.some.inj (hu₁head.symm.trans ((hyu f hfU).mp hfw'.symm)) |>.symm
        exact (hhu₁ (hfu₁ ▸ hfv').symm).elim
      · rfl
    · refine bound f z ?_
      have hfq' : f = q := by simpa using hfq
      subst f
      rintro v ⟨hqv, hvK⟩
      have hqv' : G.Adj q v := by simpa only [SimpleGraph.mem_neighborSet] using hqv
      simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hvK
      rcases hvK with rfl | rfl | rfl
      · rfl
      · exact (hcon q (Or.inr (by simp [q])) hqv'.symm).elim
      · exact (hhq hqv'.symm).elim

  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1
      G hG.1 K hKtri F hFK hcatch with href | htwo
  · obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hKeq, hbF, href⟩ := href
    have hzmem : z ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hKeq]; simp [K]
    have hymem : y ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hKeq]; simp [K]
    obtain ⟨bz, hbz, by', hby, hzbz, hyby, hbzby⟩ :=
      reflection_pair href hzmem hymem hzy.ne
    have hbzF : bz ∈ F := hbF hbz
    have hbyF : by' ∈ F := hbF hby
    have hbzq : bz = q := hzUnique bz hbzF hzbz
    have hbyu : by' = u₁ := hyUnique by' hbyF hyby
    exact hqU₁ (by simpa [hbzq, hbyu] using hbzby)
  · obtain ⟨f, hfF, hf2⟩ := htwo
    have hf1 := hncard f hfF
    omega

end Workspace.ProofLemmas.Thm224HatCatchContradiction
