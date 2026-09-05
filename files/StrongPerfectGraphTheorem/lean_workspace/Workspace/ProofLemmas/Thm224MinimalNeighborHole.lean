import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.Thm224Claim6
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224MinimalNeighborHole

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

private theorem getElem_eq_of_index_eq {α : Type*} {l : List α} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i = j) :
    l[i]'hi = l[j]'hj := by
  subst j
  rfl

/-- The least `x (t + 1)`-neighbour on `u.dropLast` closes the indicated prefix
into the endgame hole of 22.4. -/
theorem thm224MinimalNeighborHole
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
    (hXt : ∀ v ∈ u.dropLast, ¬ VertexComplete G v (wheelSystemX x t)) :
    ∃ (k : ℕ) (hk : k < u.dropLast.length),
      G.Adj (x (t + 1)) (u.dropLast[k]'hk) ∧
      (∀ (j : ℕ) (hj : j < k),
        ¬ G.Adj (x (t + 1)) (u.dropLast[j]'(lt_trans hj hk))) ∧
      let H := [z, y] ++ u.take (k + 1) ++ [x (t + 1)]
      IsHoleList G H ∧
      6 ≤ holeLength H ∧
      (∀ w ∈ H, w ∉ wheelSystemX x t) ∧
      (∀ w ∈ H, VertexComplete G w (wheelSystemX x t) ↔ w = z ∨ w = y) := by
  classical
  let q := x (t + 1)
  let X := wheelSystemX x t

  /- Choose the paper's least index `i` (zero-based here) at which `q` sees
  `u.dropLast`. -/
  have hex : ∃ i : ℕ, ∃ hi : i < u.dropLast.length,
      G.Adj q (u.dropLast[i]'hi) := by
    obtain ⟨v, hv, hqv⟩ := hadj
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hv
    refine ⟨i, hi, ?_⟩
    rwa [hiv]
  let k := Nat.find hex
  obtain ⟨hk, hqk⟩ := Nat.find_spec hex
  change k < u.dropLast.length at hk
  change G.Adj q (u.dropLast[k]'hk) at hqk
  have hkmin : ∀ (j : ℕ) (hj : j < k),
      ¬ G.Adj q (u.dropLast[j]'(lt_trans hj hk)) := by
    intro j hj hqj
    exact Nat.find_min hex hj ⟨lt_trans hj hk, hqj⟩

  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons

  have hkU : k < u.length := by
    have hdropLen : u.dropLast.length = u.length - 1 := List.length_dropLast
    omega
  have hkU' : k + 1 < u.length := by
    have hdropLen : u.dropLast.length = u.length - 1 := List.length_dropLast
    omega
  have huPos : 0 < u.length := by omega
  have htakeLen : (u.take (k + 1)).length = k + 1 := by
    rw [List.length_take]
    omega
  have hupath : IsPathList G u := by
    have hdrop := PathBasics.isPathList_drop hpath (k := 2) (by simp; omega)
    simpa using hdrop
  let u₁ := u[0]'huPos
  let uᵢ := u[k]'hkU
  have huHead : u.head? = some u₁ := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem huPos]
  have hprefix : IsPathFrom G (u.take (k + 1)) u₁ uᵢ := by
    refine ⟨PathBasics.isPathList_take hupath (by omega), ?_, ?_⟩
    · rw [List.head?_take, if_neg (by omega), huHead]
    · rw [List.getLast?_take, if_neg (by omega)]
      simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hkU, Option.some_or]
      rfl
  have hqki : G.Adj q uᵢ := by
    simpa only [uᵢ, List.getElem_dropLast] using hqk
  have hyu₁ : G.Adj y u₁ :=
    (hyu u₁ (List.getElem_mem huPos)).2 huHead
  have hyq : ¬ G.Adj y q := by
    exact hcon q (Or.inr rfl)
  have hy_ne_q : y ≠ q := by
    intro hyqeq
    exact hqYy (Or.inr hyqeq.symm)
  have hy_not_u : y ∉ u :=
    (List.nodup_cons.mp (List.nodup_cons.mp hpath.2.1).2).1
  have hy_not_prefix : y ∉ u.take (k + 1) := fun hmem =>
    hy_not_u (List.take_subset _ _ hmem)
  have hzq : G.Adj z q := hzXq q (Or.inr rfl)
  have hq_not_u : q ∉ u := by
    intro hqu
    exact hzu q hqu hzq
  have hq_not_prefix : q ∉ u.take (k + 1) := fun hmem =>
    hq_not_u (List.take_subset _ _ hmem)
  have hy_other : ∀ v ∈ u.take (k + 1), v ≠ u₁ → ¬ G.Adj y v := by
    intro v hv hvne hyv
    have hvu : v ∈ u := List.take_subset _ _ hv
    have hh := (hyu v hvu).mp hyv
    have heq : u₁ = v := Option.some_injective _ (huHead.symm.trans hh)
    exact hvne heq.symm
  have hq_other : ∀ v ∈ u.take (k + 1), v ≠ uᵢ → ¬ G.Adj q v := by
    intro v hv hvne hqv
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    have hjle : j ≤ k := by
      rw [htakeLen] at hj
      omega
    have hjU : j < u.length := by omega
    have hvj : u[j]'hjU = v := by
      rw [← hjv]
      exact List.getElem_take.symm
    have hjne : j ≠ k := by
      intro heq
      subst j
      exact hvne (by simpa only [uᵢ] using hvj.symm)
    have hjlt : j < k := by omega
    exact hkmin j hjlt (by
      simpa only [List.getElem_dropLast, hvj] using hqv)

  /- The least-neighbour condition makes `y-u₁-...-uᵢ-q` induced. -/
  have hmiddle : IsPathFrom G (y :: (u.take (k + 1) ++ [q])) y q :=
    PathAttach.isPathFrom_cons_concat hprefix hyu₁ hqki hyq hy_ne_q
      hy_not_prefix hq_not_prefix hy_other hq_other
  have hz_not_y : z ≠ y := (hzYy y (Or.inr rfl)).ne
  have hz_not_q : z ≠ q := hzq.ne
  have hz_not_middle : z ∉ y :: (u.take (k + 1) ++ [q]) := by
    intro hzmem
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hzmem
    rcases hzmem with rfl | hzpre | rfl
    · exact hz_not_y rfl
    · exact (List.nodup_cons.mp hpath.2.1).1
        (List.mem_cons_of_mem y (List.take_subset _ _ hzpre))
    · exact hz_not_q rfl
  have hz_middle_anti : ∀ v ∈ interior (y :: (u.take (k + 1) ++ [q])),
      ¬ G.Adj z v := by
    intro v hv
    have hv' := (PathBasics.mem_interior_iff_of_pathFrom hmiddle).mp hv
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv'
    rcases hv'.1 with rfl | hvpre | rfl
    · exact (hv'.2.1 rfl).elim
    · exact hzu v (List.take_subset _ _ hvpre)
    · exact (hv'.2.2 rfl).elim
  have hmiddleLen : 2 ≤ pathLength (y :: (u.take (k + 1) ++ [q])) := by
    simp only [pathLength, List.length_cons, List.length_append, htakeLen]
    omega
  have hhole : IsHoleList G ([z, y] ++ u.take (k + 1) ++ [q]) := by
    have hclose := PrismBasics.isHoleList_of_path_add_vertex hmiddle hmiddleLen
      (hzYy y (Or.inr rfl)) hzq hz_not_middle hz_middle_anti
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using hclose

  /- Claim (6), together with the hypothesis from claim (7), excludes `i = 1`
  in the paper's one-based notation (that is, `k = 0` here). -/
  have hkPos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := by omega
    have hkzero : 0 < u.dropLast.length := by omega
    have hqzero : G.Adj q (u.dropLast[0]'hkzero) := by
      have heq : u.dropLast[0]'hkzero = u.dropLast[k]'hk :=
        getElem_eq_of_index_eq hkzero hk hk0.symm
      rw [heq]
      exact hqk
    have hhead : u.head? = some (u.dropLast[0]'hkzero) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem huPos]
      congr 1
      rw [List.getElem_dropLast]
    have hheadmem : u.dropLast[0]'hkzero ∈ u.head? := by
      simp only [Option.mem_def, hhead]
    have hcomplete :=
      Workspace.ProofLemmas.Thm224Claim6.claim6
        hG hopt hT hTshape hA₀ hhub hcon hu hlen
        (u.dropLast[0]'hkzero) hheadmem (by simpa only [q] using hqzero)
    exact hXt (u.dropLast[0]'hkzero) (List.getElem_mem hkzero) hcomplete

  have hholeLen : holeLength ([z, y] ++ u.take (k + 1) ++ [q]) = k + 4 := by
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil,
      htakeLen]
    omega
  have hBerge : Berge G := hG.1.1.1.1.1
  have hholeEven := hBerge.1 _ hhole
  have hholeSix : 6 ≤ holeLength ([z, y] ++ u.take (k + 1) ++ [q]) := by
    rcases hholeEven with ⟨m, hm⟩
    rw [hholeLen]
    rw [hholeLen] at hm
    omega

  have hzX : VertexComplete G z X := fun v hv => hzXq v (Or.inl hv)
  have hz_not_X : z ∉ X := fun hzmem => G.irrefl (hzX z hzmem)
  have hy_not_X : y ∉ X := fun hymem => G.irrefl (hyX y hymem)
  have hu_not_X : ∀ v ∈ u, v ∉ X := by
    intro v hv hvX
    exact hu.2.2.2.2 v hv (hXY v hvX)
  have htake_sub_drop : ∀ v ∈ u.take (k + 1), v ∈ u.dropLast := by
    intro v hv
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    have hjlt : j < k + 1 := by
      rw [htakeLen] at hj
      exact hj
    have hjdrop : j < u.dropLast.length := by omega
    have heq : (u.take (k + 1))[j]'hj = u.dropLast[j]'hjdrop := by
      rw [List.getElem_take, List.getElem_dropLast]
    rw [← hjv, heq]
    exact List.getElem_mem hjdrop
  have hmemH (v : V) :
      v ∈ ([z, y] ++ u.take (k + 1) ++ [q]) ↔
        v = z ∨ v = y ∨ v ∈ u.take (k + 1) ∨ v = q := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have houtside : ∀ v ∈ ([z, y] ++ u.take (k + 1) ++ [q]), v ∉ X := by
    intro v hv
    rcases (hmemH v).mp hv with rfl | rfl | hvpre | rfl
    · exact hz_not_X
    · exact hy_not_X
    · exact hu_not_X v (List.take_subset _ _ hvpre)
    · exact hqX
  have hcompleteIff : ∀ v ∈ ([z, y] ++ u.take (k + 1) ++ [q]),
      VertexComplete G v X ↔ v = z ∨ v = y := by
    intro v hv
    constructor
    · intro hvc
      rcases (hmemH v).mp hv with rfl | rfl | hvpre | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hXt v (htake_sub_drop v hvpre) hvc).elim
      · exact (hqXnc hvc).elim
    · rintro (rfl | rfl)
      · exact hzX
      · exact hyX

  refine ⟨k, hk, ?_, hkmin, ?_⟩
  · simpa only [q] using hqk
  · simpa only [q, X] using ⟨hhole, hholeSix, houtside, hcompleteIff⟩

end Workspace.ProofLemmas.Thm224MinimalNeighborHole
