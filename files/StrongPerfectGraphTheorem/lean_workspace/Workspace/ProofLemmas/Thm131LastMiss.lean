import Workspace.ProofLemmas.Thm131LastCase
import Workspace.ProofLemmas.Thm131Enlarge
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# The contradiction at the end of claim (7) of 13.1

PAPER (printed p. 81): *"Choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`.  Then
`b₁-a-w₁-⋯-wₙ-b` is an odd antipath, of length ≥ 5.  All its internal vertices
have neighbours in the connected set `V(R' \ wₙ) ∪ {a₂}`, and its ends do not.
By 2.1 applied in `G`, there are adjacent vertices `x, y` in
`V(R' \ wₙ) ∪ {a₂}`, such that `x-a-w₁-⋯-wₙ-y` is an odd antipath.  Since `x` is
adjacent to `wₙ`, it follows that `x` is the neighbour of `wₙ` in `R'`, and
therefore either `y` is the second neighbour of `x` in `R'`, or `R'` has length
1 and `y = a₂`.  Assume first that `R'` has length > 1, and so both `x, y`
belong to the interior of `R'`.  Hence `x, y` are both anticomplete to
`A ∪ B`, and so `((B ∪ {x}, ∅, A ∪ {y}), a-w₁-⋯-wₙ)` is a staircase in `G`,
contradicting that `(S, R₀)` is strongly maximal.  Now assume that `R'` has
length 1.  Then `x = r'` and `y = a₂`, and `((B ∪ {r'}, ∅, A ∪ {b}),
a-w₁-⋯-wₙ)` is a staircase in `G`, a contradiction as before."*

Both sub-cases are carried out below, in the printed order.
-/

namespace Workspace.ProofLemmas.Thm131LastMiss

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131EdgeCases
open Workspace.ProofLemmas.Thm131LastCase
open Workspace.ProofLemmas.Thm131ComplementStars
open Workspace.ProofLemmas.Thm131Enlarge
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132BanisterSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The end of claim (7): if the right end of the optimal banister sees every
trajectory vertex except its terminal right-star, strong maximality fails. -/
theorem terminal_miss_absurd
    {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (hx : IsRightSequence G A C B x)
    {b : V} (hb : IsRightStar G A C B b)
    {a : V} {R w : List V}
    (hopt : BOptimalBanister G A C B x a R b)
    (htraj : trajectoryOfVertex G A x a (a :: w))
    (hIH : ∀ (y : List V), y.length < x.length →
      IsRightSequence G A C B y →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (Q : List V), BOptimalBanister G A C B y c Q d →
      ∀ (z : List V), trajectoryOfVertex G A y c (c :: z) →
        TrajectoryConclusion G c Q d z)
    (hRone : pathLength R = 1)
    {last : V} (hanti : IsAntipathFrom G (a :: w) a last)
    (hodd : Odd w.length) (hwlong : 1 < w.length)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbnotw : b ∉ w)
    (hbBefore : ∀ z ∈ w, z ≠ last → G.Adj b z)
    (hbmiss : ¬ G.Adj b last)
    (hlast : IsRightStar G A C B last) : False := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hab : G.Adj a b :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hopt.1.1 hRone
  have hReq : R = [a, b] := path_eq_pair_of_length_one hopt.1.1 hRone
  have hlastw : last ∈ w := by
    have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlastW : w.getLast? = some last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
    exact Workspace.ProofLemmas.PathBasics.getLast_mem hlastW

  obtain ⟨i, hi, j, hj, habirth, hantiData, hidx⟩ :=
    trajectoryOfVertex_data hS hx hopt.1.2.2.1 htraj
  have hxjlast : x[j] = last :=
    Option.some.inj (hantiData.2.2.symm.trans hanti.2.2)
  have hji : j ≤ i := by
    obtain ⟨k, hk, hki, hxklast⟩ := hidx last hlastw
    have hkj : k = j := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      exact hxklast.trans hxjlast.symm
    omega

  -- PAPER (just before (3)): *"From the third axiom, there is a banister
  -- `r'-R'-wₙ` … and therefore we may choose this banister to be
  -- `wₙ`-optimal."*
  let y : List V := x.take j
  have hylen : y.length = j := by simp [y, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hyshort : y.length < x.length := by omega
  have hyseq : IsRightSequence G A C B y := by
    simpa [y] using rightSequence_take hx j
  have hxjanti : VertexAnticomplete G x[j] A := by
    simpa [hxjlast] using (show VertexAnticomplete G last A from
      fun z hz => hlast.2.2 z (Or.inl hz))
  obtain ⟨r₀, Q₀, hQ₀, q, hqy, hr₀q⟩ := hx.2.2 j hj hxjanti
  have hr₀nc : ¬ VertexComplete G r₀ {z : V | z ∈ y} := by
    intro hc
    exact hr₀q (hc q (by simpa [y] using hqy))
  obtain ⟨r, Q, ell, hell, hoptQ, hbirthQ, -⟩ :=
    exists_optimalBanister hyseq ⟨r₀, Q₀, hQ₀, hr₀nc⟩
  have hQlast : IsBanister G A C B r Q last := by
    simpa [hxjlast] using hoptQ.1

  -- The birth of the auxiliary left-star in `y` is also a birth in `x`.
  have hellx : ell < x.length := by rw [hylen] at hell; omega
  have hyellx : y[ell]'hell = x[ell]'hellx := by simp [y]
  have hbirthQfull : birth G A C B x r x[ell] := by
    obtain ⟨hrleft, -, ell', hell', hell'eq, hell'non, hell'before⟩ := hbirthQ
    have hell'j : ell' < j := by simpa [hylen] using hell'
    have hell'x : ell' < x.length := by omega
    have htell' : y[ell']'hell' = x[ell']'hell'x := by simp [y]
    have hell'ell : ell' = ell := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      calc
        x[ell'] = y[ell'] := htell'.symm
        _ = y[ell] := hell'eq
        _ = x[ell] := hyellx
    subst ell'
    have hrncx : ¬ VertexComplete G r {z : V | z ∈ x} := by
      intro hc
      exact hell'non (by rw [hyellx]; exact hc x[ell] (List.getElem_mem hellx))
    refine ⟨hrleft, hrncx, ell, hellx, rfl, ?_, ?_⟩
    · simpa [hyellx] using hell'non
    · intro k hk
      have hky : k < y.length := by rw [hylen]; omega
      have htk : y[k]'hky = x[k]'(by omega) := by simp [y]
      simpa [htk] using hell'before k hk
  have hearlier : Earlier x x[ell] x[i] := by
    refine ⟨ell, i, hellx, hi, rfl, rfl, ?_⟩
    rw [hylen] at hell
    omega

  -- PAPER (3): *"`R'` is disjoint from `R`, and there are no edges between
  -- `V(R \ a)` and `V(R' \ wₙ)`."*
  have hnolink := optimal_halves_not_linked hK.1.1.1.2.1.1 hopt hQlast
    hbirthQfull habirth hearlier
  have hsep := halves_anticomplete_of_not_linked hnolink
  have hdisj := banisters_disjoint_of_halves_not_linked hK.1.1.1.2.1.1
    hopt.1 hQlast hnolink

  -- PAPER (5): *"`C = ∅`."*
  have hCempty : C = ∅ := middle_empty_of_last_rightStar hG heven hK
    hopt.1.2.2.1 hlast hanti hodd hwlong hbeforeA hwB
  have hS0 : StepConnected G A (∅ : Set V) B := by simpa [hCempty] using hS
  have ha0 : IsLeftStar G A (∅ : Set V) B a := by
    simpa [hCempty] using hopt.1.2.2.1
  have hb0 : IsRightStar G A (∅ : Set V) B b := by simpa [hCempty] using hb
  have hr0 : IsLeftStar G A (∅ : Set V) B r := by
    simpa [hCempty] using hQlast.2.2.1
  have hlast0 : IsRightStar G A (∅ : Set V) B last := by
    simpa [hCempty] using hlast

  -- Structure of the auxiliary banister `Q = r-R'-wₙ`.
  have hQodd : Odd (pathLength Q) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS r last Q hQlast).2
  have hQlen : Q.length = pathLength Q + 1 :=
    Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hQlast.1.1
  have hQ2 : 2 ≤ Q.length := by obtain ⟨m, hm⟩ := hQodd; omega
  have hrQ : r ∈ Q := Workspace.ProofLemmas.PathBasics.head_mem hQlast.1.2.1
  have hlastQ : last ∈ Q := Workspace.ProofLemmas.PathBasics.getLast_mem hQlast.1.2.2
  have hrlastne : r ≠ last :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hQlast.1 (by omega)
  have hdropIff : ∀ z : V, z ∈ Q.dropLast ↔ (z ∈ Q ∧ z ≠ last) := fun z =>
    HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQlast.1
  have hrdrop : r ∈ Q.dropLast := (hdropIff r).2 ⟨hrQ, hrlastne⟩
  have hdropCase : ∀ z ∈ Q.dropLast, z = r ∨ z ∈ interior Q := by
    intro z hz
    obtain ⟨hzQ, hzl⟩ := (hdropIff z).1 hz
    by_cases hzr : z = r
    · exact Or.inl hzr
    · exact Or.inr
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQlast.1).2
          ⟨hzQ, hzr, hzl⟩)
  have hdropOut : ∀ z ∈ Q.dropLast, z ∉ A ∪ B ∪ C := fun z hz =>
    hQlast.2.1 z ((hdropIff z).1 hz).1
  have hdropAntiB : ∀ z ∈ Q.dropLast, ∀ u ∈ B, ¬ G.Adj z u := by
    intro z hz u hu
    rcases hdropCase z hz with hzr | hzint
    · exact hzr ▸ hQlast.2.2.1.2.2 u (Or.inl hu)
    · exact hQlast.2.2.2.2 z hzint u (Or.inl (Or.inr hu))

  -- PAPER: *"Choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`."*
  obtain ⟨a₁, ha₁A⟩ := hS.2.1.1
  obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have ha₂A : a₂ ∈ A := hstep.2.1.2.1
  have hb₂B : b₂ ∈ B := hstep.2.1.2.2.1
  have hra₂ : G.Adj r a₂ := hr0.2.1 a₂ ha₂A
  have ha₂b₁ : ¬ G.Adj a₂ b₁ := by
    intro hadj
    have ha₂R := Workspace.ProofLemmas.PathBasics.head_mem hstep.2.1.1.2.1
    have hb₁R := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.1.1.2.2
    rcases (hstep.2.2.2 b₁ hb₁R a₂ ha₂R).mp hadj.symm with h | h
    · exact Set.disjoint_left.mp hS.1.1 ha₁A (h.1.symm ▸ hb₁B)
    · exact Set.disjoint_left.mp hS.1.1 ha₂A (h.2.symm ▸ hb₂B)

  -- PAPER: *"`b₁-a-w₁-⋯-wₙ-b` is an odd antipath, of length ≥ 5."*
  set T : List V := a :: w with hTdef
  set U : List V := b₁ :: (T ++ [b]) with hUdef
  have hTanti : IsAntipathFrom G T a last := hanti
  have hb₁aC : Gᶜ.Adj b₁ a := by
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hopt.1.2.2.1.1 (he.symm ▸ Or.inl (Or.inr hb₁B)),
      fun hadj => hopt.1.2.2.1.2.2 b₁ (Or.inl hb₁B) hadj.symm⟩
  have hblastC : Gᶜ.Adj b last := by
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hbnotw (he ▸ hlastw), hbmiss⟩
  have hb₁b : G.Adj b₁ b := (hb.2.1 b₁ hb₁B).symm
  have hb₁not : b₁ ∉ T := by
    intro hm
    rcases List.mem_cons.mp hm with hba | hbw
    · exact hopt.1.2.2.1.1 (hba.symm ▸ Or.inl (Or.inr hb₁B))
    · exact bComplete_not_mem_strip hS (hwB b₁ hbw) (Or.inl (Or.inr hb₁B))
  have hbnot : b ∉ T := by
    intro hm
    rcases List.mem_cons.mp hm with hba | hbw
    · exact hab.ne' hba
    · exact hbnotw hbw
  have hb₁other : ∀ z ∈ T, z ≠ a → ¬ Gᶜ.Adj b₁ z := by
    intro z hz hza hadj
    have hzw : z ∈ w := (List.mem_cons.mp hz).resolve_left hza
    exact (G.compl_adj b₁ z).mp hadj |>.2 (hwB z hzw b₁ hb₁B).symm
  have hbother : ∀ z ∈ T, z ≠ last → ¬ Gᶜ.Adj b z := by
    intro z hz hzlast hadj
    apply (G.compl_adj b z).mp hadj |>.2
    rcases List.mem_cons.mp hz with hza | hzw
    · subst z; exact hab.symm
    · exact hbBefore z hzw hzlast
  have hU : IsPathFrom Gᶜ U b₁ b :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hTanti hb₁aC hblastC
      (fun hc => (G.compl_adj b₁ b).mp hc |>.2 hb₁b)
      hb₁b.ne hb₁not hbnot hb₁other hbother
  have hTlen : T.length = w.length + 1 := by simp [hTdef]
  have hwlen3 : 3 ≤ w.length := by obtain ⟨k, hk⟩ := hodd; omega
  have hUlen : U.length = T.length + 2 :=
    Workspace.ProofLemmas.PathAttach.length_cons_append_singleton b₁ b T
  have hUplen : pathLength U = T.length + 1 :=
    Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton b₁ b T
  have hUodd : Odd (pathLength U) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  have hU5 : 5 ≤ pathLength U := by omega
  have hUget : ∀ (k : ℕ) (hk : k < T.length),
      U[k + 1]'(by omega) = T[k]'hk := by
    intro k hk
    simp only [hUdef, List.getElem_cons_succ, List.getElem_append_left hk]
  have hTlastElem : T[T.length - 1]'(by omega) = last :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hTanti.2.2 (by omega)
  have hT0 : T[0]'(by omega) = a := by simp [hTdef]
  have hUpen : U[U.length - 2]'(by omega) = last := by
    have hidx : U.length - 2 = (T.length - 1) + 1 := by omega
    rw [(getElem_congr rfl hidx (by omega) :
      U[U.length - 2]'(by omega) = U[(T.length - 1) + 1]'(by omega))]
    rw [hUget (T.length - 1) (by omega)]
    exact hTlastElem
  have hU1 : U[1]'(by omega) = a := by
    rw [(getElem_congr rfl (by omega : (1:ℕ) = 0 + 1) (by omega) :
      U[1]'(by omega) = U[0 + 1]'(by omega))]
    rw [hUget 0 (by omega)]
    exact hT0
  have hTsubU : ∀ z ∈ T, z ∈ U := fun z hz => by
    rw [hUdef]; exact List.mem_cons_of_mem b₁ (List.mem_append_left _ hz)
  have hlastU : last ∈ U := hTsubU last (List.mem_cons_of_mem a hlastw)
  have hUidx : ∀ z ∈ T, ∃ (k : ℕ) (hk : k < U.length),
      1 ≤ k ∧ k ≤ U.length - 2 ∧ U[k]'hk = z := by
    intro z hz
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
    exact ⟨k + 1, by omega, by omega, by omega, (hUget k hk).trans hkz⟩

  -- PAPER: *"the connected set `V(R' \ wₙ) ∪ {a₂}`."*
  set D : Set V := {z : V | z ∈ Q.dropLast} ∪ {a₂} with hDdef
  have hDsing : ConnectedSet G ({a₂} : Set V) := by
    intro u v
    have huv : u = v := Subtype.ext (u.2.trans v.2.symm)
    subst huv
    exact SimpleGraph.Reachable.refl u
  have hDconn : ConnectedSet G D :=
    Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union
      (Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (HyperprismRungStructure.isPathList_dropLast hQlast.1.1 hQ2))
      hDsing (Or.inr ⟨r, hrdrop, a₂, rfl, hra₂⟩)
  have hDanti : AnticonnectedSet Gᶜ D := by
    simpa only [AnticonnectedSet, compl_compl] using hDconn
  have hUD : ∀ z ∈ U, z ∉ D := by
    intro z hz hzD
    have hzcase : z = b₁ ∨ z ∈ T ∨ z = b := by
      simpa [hUdef] using
        (Workspace.ProofLemmas.PathAttach.mem_cons_append_singleton (x := z)
          (s := b₁) (t := b) (p := T)).1 (by simpa [hUdef] using hz)
    rcases hzD with hzQ | hza₂
    · rcases hzcase with h | h | h
      · exact hdropOut z hzQ (h ▸ Or.inl (Or.inr hb₁B))
      · rcases List.mem_cons.mp h with hza | hzw
        · exact hdisj a (by rw [hReq]; simp) (hza ▸ ((hdropIff z).1 hzQ).1)
        · obtain ⟨b', hb'B⟩ := hS.2.1.2
          exact hdropAntiB z hzQ b' hb'B (hwB z hzw b' hb'B)
      · exact hdisj b (by rw [hReq]; simp) (h ▸ ((hdropIff z).1 hzQ).1)
    · have hza : z = a₂ := hza₂
      rcases hzcase with h | h | h
      · exact Set.disjoint_left.mp hS.1.1 ha₂A (hza ▸ h ▸ hb₁B)
      · rcases List.mem_cons.mp h with hzaa | hzw
        · exact hopt.1.2.2.1.1 (hzaa ▸ hza ▸ Or.inl (Or.inl ha₂A))
        · exact bComplete_not_mem_strip hS (hwB z hzw) (hza ▸ Or.inl (Or.inl ha₂A))
      · exact hb.1 (h ▸ hza ▸ Or.inl (Or.inl ha₂A))
  have hb₁D : VertexComplete Gᶜ b₁ D := by
    rintro z (hzQ | hza₂)
    · rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hdropOut z hzQ (he ▸ Or.inl (Or.inr hb₁B)),
        fun hadj => hdropAntiB z hzQ b₁ hb₁B hadj.symm⟩
    · have hza : z = a₂ := hza₂
      subst z
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => Set.disjoint_left.mp hS.1.1 ha₂A (he.symm ▸ hb₁B),
        fun hadj => ha₂b₁ hadj.symm⟩
  have hbD : VertexComplete Gᶜ b D := by
    rintro z (hzQ | hza₂)
    · rw [SimpleGraph.compl_adj]
      refine ⟨fun he => hdisj b (by rw [hReq]; simp) (he ▸ ((hdropIff z).1 hzQ).1), ?_⟩
      exact hsep b (by rw [hReq]; simp) z hzQ
    · have hza : z = a₂ := hza₂
      subst z
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hb.1 (he.symm ▸ Or.inl (Or.inl ha₂A)),
        fun hadj => hb.2.2 a₂ (Or.inl ha₂A) hadj⟩
  have hIntU : SPGT.interior U = T := by
    simp only [hUdef, SPGT.interior, List.tail_cons]
    exact List.dropLast_concat
  have hNoInternalComplete : ∀ z ∈ SPGT.interior U, ¬ VertexComplete Gᶜ z D := by
    intro z hz hzc
    have hzT : z ∈ T := by rw [hIntU] at hz; exact hz
    rcases List.mem_cons.mp hzT with hza | hzw
    · have hza₂G : G.Adj z a₂ := hza ▸ hopt.1.2.2.1.2.1 a₂ ha₂A
      exact (G.compl_adj z a₂).mp (hzc a₂ (Or.inr rfl)) |>.2 hza₂G
    · by_cases hzl : z = last
      · -- `wₙ` has a `G`-neighbour in `V(R' \ wₙ)`: its neighbour on `R'`.
        have hpenQ : Q[Q.length - 2]'(by omega) ∈ Q := List.getElem_mem _
        have hpenAdj : G.Adj (Q[Q.length - 2]'(by omega)) last := by
          have := Workspace.ProofLemmas.PathBasics.path_adj_succ hQlast.1.1
            (i := Q.length - 2) (by omega)
          have hidx : Q.length - 2 + 1 = Q.length - 1 := by omega
          rw [(getElem_congr rfl hidx (by omega) :
            Q[Q.length - 2 + 1]'(by omega) = Q[Q.length - 1]'(by omega))] at this
          rw [Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
            hQlast.1.2.2 (by omega)] at this
          exact this
        have hpenNe : Q[Q.length - 2]'(by omega) ≠ last := hpenAdj.ne
        have hpenDrop : Q[Q.length - 2]'(by omega) ∈ Q.dropLast :=
          (hdropIff _).2 ⟨hpenQ, hpenNe⟩
        exact (G.compl_adj z _).mp (hzc _ (Or.inl hpenDrop)) |>.2
          (hzl ▸ hpenAdj.symm)
      · exact (G.compl_adj z a₂).mp (hzc a₂ (Or.inr rfl)) |>.2
          (hbeforeA z hzw hzl a₂ ha₂A)
  have hNoCompleteEdge : ¬ ∃ u ∈ U, ∃ v ∈ U, EdgeComplete Gᶜ D u v := by
    rintro ⟨u, hu, v, hv, huv, huD, hvD⟩
    by_cases huI : u ∈ SPGT.interior U
    · exact hNoInternalComplete u huI huD
    by_cases hvI : v ∈ SPGT.interior U
    · exact hNoInternalComplete v hvI hvD
    have huEnd : u = b₁ ∨ u = b := by
      by_cases hub₁ : u = b₁
      · exact Or.inl hub₁
      right
      by_contra hub
      exact huI ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hU).2
        ⟨hu, hub₁, hub⟩)
    have hvEnd : v = b₁ ∨ v = b := by
      by_cases hvb₁ : v = b₁
      · exact Or.inl hvb₁
      right
      by_contra hvb
      exact hvI ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hU).2
        ⟨hv, hvb₁, hvb⟩)
    rcases huEnd with hub₁ | hub <;> rcases hvEnd with hvb₁ | hvb
    · exact huv.ne (hub₁.trans hvb₁.symm)
    · exact (G.compl_adj b₁ b).mp (hub₁ ▸ hvb ▸ huv) |>.2 hb₁b
    · exact (G.compl_adj b b₁).mp (hub ▸ hvb₁ ▸ huv) |>.2 hb₁b.symm
    · exact huv.ne (hub.trans hvb.symm)

  have hT3 : 3 ≤ pathLength T := by
    obtain ⟨k, hk⟩ := hodd
    simp [hTdef, pathLength]
    omega
  have hqTb : ∀ z ∈ T, (Gᶜ.Adj b z ↔ z = last) := by
    intro z hz
    constructor
    · intro hadj
      by_contra hzl
      exact hbother z hz hzl hadj
    · intro hzl
      exact hzl ▸ hblastC

  -- PAPER: *"By 2.1 applied in `G`, there are adjacent vertices `x, y` in
  -- `V(R' \ wₙ) ∪ {a₂}`, such that `x-a-w₁-⋯-wₙ-y` is an odd antipath."*
  rcases Workspace.Statements.S02.SPGT.thm_2_1 Gᶜ
      (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) D hDanti U b₁ b
      hU hUD hUodd hb₁D hbD with hedge | hleap | hshort
  · exact hNoCompleteEdge hedge
  · obtain ⟨-, u, huD, v, hvD, hleapuv⟩ := hleap
    obtain ⟨-, -, huvne, huvnadj, huadj, hvadj⟩ := hleapuv
    have huvG : G.Adj u v := by
      rw [SimpleGraph.compl_adj] at huvnadj
      push Not at huvnadj
      exact huvnadj huvne
    -- `u` is the vertex of `D` seeing `a`; it is `G`-adjacent to `wₙ`.
    have huaC : Gᶜ.Adj u a := by
      have := (huadj 1 (by omega)).2 (Or.inr (Or.inl rfl))
      rwa [hU1] at this
    have hulastG : G.Adj u last := by
      have hnot : ¬ Gᶜ.Adj u (U[U.length - 2]'(by omega)) := by
        intro hadj
        rcases (huadj (U.length - 2) (by omega)).1 hadj with h | h | h <;> omega
      rw [hUpen, SimpleGraph.compl_adj] at hnot
      push Not at hnot
      exact hnot (fun he => hUD last hlastU (he ▸ huD))
    -- PAPER: *"Since `x` is adjacent to `wₙ`, it follows that `x` is the
    -- neighbour of `wₙ` in `R'`."*
    have huQ : u ∈ Q.dropLast := by
      rcases huD with h | h
      · exact h
      · exact absurd (hlast.2.2 u (Or.inl ((h : u = a₂) ▸ ha₂A))) (by
          intro hcon; exact hcon hulastG.symm)
    have hupen : u = Q[Q.length - 2]'(by omega) :=
      (adj_last_iff_eq_penultimate hQlast.1 hQ2 ((hdropIff u).1 huQ).1).1 hulastG
    have hvlastC : Gᶜ.Adj v last := by
      have := (hvadj (U.length - 2) (by omega)).2 (Or.inr (Or.inl rfl))
      rwa [hUpen] at this
    have hpT : ∀ z ∈ T, (Gᶜ.Adj u z ↔ z = a) := by
      intro z hz
      obtain ⟨k, hk, hk1, hk2, hkz⟩ := hUidx z hz
      constructor
      · intro hadj
        rw [← hkz] at hadj
        rcases (huadj k hk).1 hadj with h | h | h
        · omega
        · rw [← hkz, (getElem_congr rfl h hk :
            U[k]'hk = U[1]'(by omega))]
          exact hU1
        · omega
      · intro hza
        rw [hza]
        exact huaC
    have hqT : ∀ z ∈ T, (Gᶜ.Adj v z ↔ z = last) := by
      intro z hz
      obtain ⟨k, hk, hk1, hk2, hkz⟩ := hUidx z hz
      constructor
      · intro hadj
        rw [← hkz] at hadj
        rcases (hvadj k hk).1 hadj with h | h | h
        · omega
        · rw [← hkz, (getElem_congr rfl h hk :
            U[k]'hk = U[U.length - 2]'(by omega))]
          exact hUpen
        · omega
      · intro hzl
        rw [hzl]
        exact hvlastC
    have hunotT : u ∉ T := fun hm => hUD u (hTsubU u hm) huD
    have hvnotT : v ∉ T := fun hm => hUD v (hTsubU v hm) hvD
    by_cases hQone : pathLength Q = 1
    · -- PAPER: *"Now assume that `R'` has length 1.  Then `x = r'` and
      -- `y = a₂`, and `((B ∪ {r'}, ∅, A ∪ {b}), a-w₁-⋯-wₙ)` is a staircase."*
      have hQeq : Q = [r, last] := path_eq_pair_of_length_one hQlast.1 hQone
      have hur : u = r := by
        have := (hdropIff u).1 huQ
        rw [hQeq] at this
        rcases (by simpa using this.1) with h | h
        · exact h
        · exact absurd h this.2
      rw [hur] at hpT hunotT
      have hrb : ¬ G.Adj r b := fun hadj =>
        hsep b (by rw [hReq]; simp) r hrdrop hadj.symm
      have hbnotT : b ∉ T := hbnot
      have hstair := staircase_compl_adjoin_pair (p := r) (q := b) hS0
        (stepConnected_compl_adjoin_stars G A B r b hS0 hr0 hb0 hrb)
        ha0 hlast0 hbeforeA hwB hTanti hT3 hpT hqTb hunotT hbnotT
      exact compl_adjoin_pair_absurd hK hCempty
        (by simpa [hCempty] using hr0.1) hstair
    · -- PAPER: *"Assume first that `R'` has length > 1, and so both `x, y`
      -- belong to the interior of `R'`.  Hence `x, y` are both anticomplete to
      -- `A ∪ B`, and so `((B ∪ {x}, ∅, A ∪ {y}), a-w₁-⋯-wₙ)` is a staircase."*
      have hQ3 : 3 ≤ pathLength Q := by obtain ⟨m, hm⟩ := hQodd; omega
      have hQ4 : 4 ≤ Q.length := by omega
      have huint : u ∈ interior Q := by
        rw [hupen]
        exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hQlast.1.1
          (by omega) (by omega) (by omega)
      have hva₂ : v ≠ a₂ := by
        intro he
        exact hQlast.2.2.2.2 u huint a₂ (Or.inl (Or.inl ha₂A)) (he ▸ huvG)
      have hvQ : v ∈ Q.dropLast := by
        rcases hvD with h | h
        · exact h
        · exact absurd (h : v = a₂) hva₂
      obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp ((hdropIff v).1 hvQ).1
      have hkval : k = Q.length - 3 := by
        have hadj : G.Adj (Q[Q.length - 2]'(by omega)) (Q[k]'hk) := by
          rw [← hupen, hkv]; exact huvG
        rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hQlast.1.1
          (by omega : Q.length - 2 < Q.length) hk).1 hadj with h | h
        · exfalso
          apply ((hdropIff v).1 hvQ).2
          rw [← hkv]
          exact (getElem_congr rfl (by omega : k = Q.length - 1) hk).trans
            (Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
              hQlast.1.2.2 (by omega))
        · omega
      have hvint : v ∈ interior Q := by
        rw [← hkv]
        exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hQlast.1.1
          hk (by omega) (by omega)
      have huAB : VertexAnticomplete G u (A ∪ B) := by
        rintro z (hzA | hzB)
        · exact hQlast.2.2.2.2 u huint z (Or.inl (Or.inl hzA))
        · exact hQlast.2.2.2.2 u huint z (Or.inl (Or.inr hzB))
      have hvAB : VertexAnticomplete G v (A ∪ B) := by
        rintro z (hzA | hzB)
        · exact hQlast.2.2.2.2 v hvint z (Or.inl (Or.inl hzA))
        · exact hQlast.2.2.2.2 v hvint z (Or.inl (Or.inr hzB))
      have huOut : u ∉ A ∪ B ∪ (∅ : Set V) := by
        have := hQlast.2.1 u (Workspace.ProofLemmas.PathBasics.interior_subset huint)
        rw [hCempty] at this
        exact this
      have hvOut : v ∉ A ∪ B ∪ (∅ : Set V) := by
        have := hQlast.2.1 v (Workspace.ProofLemmas.PathBasics.interior_subset hvint)
        rw [hCempty] at this
        exact this
      have hstair := staircase_compl_adjoin_pair (p := u) (q := v) hS0
        (stepConnected_compl_adjoin_interior_pair hS0 huOut hvOut huAB hvAB huvG)
        ha0 hlast0 hbeforeA hwB hTanti hT3 hpT hqT hunotT hvnotT
      exact compl_adjoin_pair_absurd hK hCempty
        (by rw [hCempty]; exact huOut) hstair
  · obtain ⟨hthree, -⟩ := hshort
    omega

end Workspace.ProofLemmas.Thm131LastMiss
