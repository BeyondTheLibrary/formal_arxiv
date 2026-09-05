import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.OddWheelAttachmentBase
import Workspace.Statements.S17.Thm_17_4

/-!
# The two 17.4 reductions used in the proof of 18.5

Two of the three invocations of 17.5 in the printed proof of 18.5 use much less
than the parity conclusion of 17.5.  In both places 17.4 already contradicts a
complete penultimate vertex.  Keeping the reductions here makes the remaining
dependency on the genuinely one-sided parity argument explicit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm185TripleRRReduction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem getElem_eq_of_index_eq {W : Type*} (L : List W) {i j : ℕ}
    (hij : i = j) (hi : i < L.length) (hj : j < L.length) :
    L[i]'hi = L[j]'hj := by
  subst j
  rfl

/-- The antipath implicitly chosen before the application of 17.4 in the proof
of 17.5.  If `u` is outside `X ∪ Y`, complete to the nonempty set `Y`, but not
complete to `X`, anticonnectivity of `X ∪ Y` supplies an antipath from `u` to a
vertex of `Y` whose interior lies in `X`.  Choosing the first `Y`-vertex on an
induced antipath is the small point hidden by the paper's notation. -/
theorem exists_antipath_to_Y_with_interior_in_X
    (G : SimpleGraph V) (X Y : Set V)
    (hXYa : AnticonnectedSet G (X ∪ Y)) (hYne : Y.Nonempty)
    (u : V) (huXY : u ∉ X ∪ Y)
    (huY : VertexComplete G u Y) (huX : ¬ VertexComplete G u X) :
    ∃ y ∈ Y, ∃ q : List V,
      IsAntipathFrom G q u y ∧ (∀ w ∈ SPGT.interior q, w ∈ X) ∧
        SPGT.interior q ≠ [] := by
  classical
  obtain ⟨x, hxX, hux⟩ : ∃ x ∈ X, ¬ G.Adj u x := by
    by_contra hnone
    push Not at hnone
    exact huX hnone
  let S : Set V := (X ∪ Y) ∪ {u}
  have hSanti : AnticonnectedSet G S := by
    dsimp [S]
    exact ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hXYa
      ⟨x, Or.inl hxX, ⟨fun he => huXY (he ▸ Or.inl hxX), hux⟩⟩
  obtain ⟨y₀, hy₀Y⟩ := hYne
  have huS : u ∈ S := Or.inr rfl
  have hy₀S : y₀ ∈ S := Or.inl (Or.inr hy₀Y)
  obtain ⟨r, hr, hrS⟩ :=
    InducedPathExtraction.exists_isAntipathFrom_of_anticonnected hSanti huS hy₀S
  let HitsY : ℕ → Prop := fun i => ∃ hi : i < r.length, r[i]'hi ∈ Y
  have hHit : ∃ i, HitsY i := by
    have hy₀r : y₀ ∈ r := PathBasics.getLast_mem hr.2.2
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hy₀r
    exact ⟨i, hi, hieq ▸ hy₀Y⟩
  let k : ℕ := Nat.find hHit
  obtain ⟨hk, hky⟩ := Nat.find_spec hHit
  let y : V := r[k]'hk
  have hyY : y ∈ Y := hky
  have hposr : 0 < r.length := PathBasics.path_length_pos hr.1
  have hr0 : r[0]'hposr = u := PathBasics.getElem_zero_of_head? hr.2.1 hposr
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hyval : y = r[0]'hposr := by
      dsimp [y]
      exact getElem_eq_of_index_eq r hk0 hk hposr
    have hy0 : r[0]'hposr ∈ Y := hyval ▸ hyY
    apply huXY
    apply Or.inr
    simpa [hr0] using hy0
  let q : List V := r.take (k + 1)
  have hq0 := PathBasics.isPathFrom_slice hr.1 hkpos hk
  have hq : IsAntipathFrom G q u y := by
    simpa [q, y, hr0] using hq0
  have hqint : ∀ w ∈ SPGT.interior q, w ∈ X := by
    intro w hw
    obtain ⟨i, hi, hi0, hik, hiw⟩ :=
      (PathBasics.mem_interior_slice_iff hr.1 hkpos hk).mp (by simpa [q] using hw)
    have hnotY : r[i]'hi ∉ Y := by
      intro hiY
      exact (Nat.find_min hHit hik) ⟨hi, hiY⟩
    have hiS : r[i]'hi ∈ S := hrS _ (List.getElem_mem hi)
    rcases hiS with hiXY | hiu
    · rcases hiXY with hiX | hiY
      · simpa [hiw] using hiX
      · exact False.elim (hnotY hiY)
    · rw [Set.mem_singleton_iff] at hiu
      have hieq0 : i = 0 := by
        have heq : r[i]'hi = r[0]'hposr := hiu.trans hr0.symm
        exact (PathBasics.path_nodup hr.1).getElem_inj_iff.mp heq
      omega
  have hqintne : SPGT.interior q ≠ [] := by
    intro he
    have hqlen : q.length = 2 := by
      have hqpos : 0 < q.length := PathBasics.path_length_pos hq.1
      have hintlen : (SPGT.interior q).length = q.length - 2 := PathBasics.interior_length q
      rw [he] at hintlen
      simp only [List.length_nil] at hintlen
      have hendsne : u ≠ y := by
        intro heq
        apply huXY
        exact Or.inr (by simpa [heq] using hyY)
      have hnotone : q.length ≠ 1 := by
        intro hqone
        obtain ⟨a, hqa⟩ := List.length_eq_one_iff.mp hqone
        have hau : a = u := by simpa [hqa] using hq.2.1
        have hay : a = y := by simpa [hqa] using hq.2.2
        exact hendsne (hau.symm.trans hay)
      omega
    have hqLenOne : pathLength q = 1 := by
      rw [PathBasics.pathLength_eq, hqlen]
    have hadjCompl := PathBasics.isPathFrom_ends_adj_of_length_one hq hqLenOne
    rw [SimpleGraph.compl_adj] at hadjCompl
    exact hadjCompl.2 (huY y hyY)
  exact ⟨y, hyY, q, hq, hqint, hqintne⟩

private theorem positive_pathLength_of_distinct_ends {G : SimpleGraph V}
    {p : List V} {a b : V} (hp : IsPathFrom G p a b) (hab : a ≠ b) :
    0 < pathLength p := by
  rw [PathBasics.pathLength_eq]
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  by_contra h
  have hlen : p.length = 1 := by omega
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
  have ha : x = a := by simpa using Option.some_injective _ hp.2.1
  have hb : x = b := by simpa using Option.some_injective _ hp.2.2
  exact hab (ha.symm.trans hb)

/-- If the last end of a path and a vertex of the other anticonnected side are
adjacent, but both miss the first side, 17.4 says that the penultimate path
vertex cannot be complete to the first side. -/
theorem penultimate_not_complete (G : SimpleGraph V) (hG : InF7 G)
    (p : List V) (p₁ pn1 pₙ : V) (hp : IsPathList G p)
    (hlen : 1 < pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hlast1 : p.dropLast.getLast? = some pn1)
    (X Y : Set V) (hXP : ∀ w ∈ p, w ∉ X) (hYP : ∀ w ∈ p, w ∉ Y)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hXYa : AnticonnectedSet G (X ∪ Y))
    (hp₁X : VertexComplete G p₁ X)
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pₙ))
    (z : V) (hz : z ∉ X ∪ Y) (hzP : z ∉ p)
    (hzXY : VertexComplete G z (X ∪ Y))
    (hznb : VertexAnticomplete G z {w : V | w ∈ p})
    (hpₙX : ¬ VertexComplete G pₙ X)
    (y : V) (hy : y ∈ Y) (hyX : y ∉ X)
    (hpₙmiss : ∃ x ∈ X, ¬ G.Adj pₙ x)
    (hymiss : ∃ x ∈ X, ¬ G.Adj y x)
    (hpₙy : G.Adj pₙ y) :
    ¬ VertexComplete G pn1 X := by
  obtain ⟨q, hq, hqint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hXa (hXP pₙ
      (PathBasics.getLast_mem hlast)) hyX hpₙmiss hymiss
  have hends : pₙ ≠ y := hpₙy.ne
  have hqpos : 0 < pathLength q :=
    positive_pathLength_of_distinct_ends hq hends
  have hqne1 : pathLength q ≠ 1 := by
    intro hq1
    have hadj := PathBasics.isPathFrom_ends_adj_of_length_one hq hq1
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2 hpₙy
  have hq3 : 3 ≤ q.length := by
    rw [PathBasics.pathLength_eq] at hqpos hqne1
    omega
  have hintne : SPGT.interior q ≠ [] := PathBasics.interior_ne_nil hq.1 hq3
  let x₁ : V := (SPGT.interior q).head hintne
  have hx₁ : (SPGT.interior q).head? = some x₁ :=
    List.head?_eq_some_head hintne
  have hx₁int : x₁ ∈ SPGT.interior q := List.head_mem hintne
  have h174 := _root_.Workspace.Statements.S17.SPGT.thm_17_4 G hG p p₁ pn1 pₙ hp
    hlen hhead hlast hlast1 X Y hXP hYP hXa hYa hXYa hp₁X hYuniq
    z hz hzP hzXY hznb hpₙX y x₁ hy q hq hqint hx₁
  intro hpn1X
  exact h174 (hpn1X x₁ (hqint x₁ hx₁int))

/-- The literal antipath `pₙ-v-y` makes the first interior vertex in 17.4
equal to `v`, so its conclusion is the desired nonadjacency to `v`. -/
theorem penultimate_not_adj_of_two_edge_antipath
    (G : SimpleGraph V) (hG : InF7 G)
    (p : List V) (p₁ pn1 pₙ : V) (hp : IsPathList G p)
    (hlen : 1 < pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hlast1 : p.dropLast.getLast? = some pn1)
    (X Y : Set V) (hXP : ∀ w ∈ p, w ∉ X) (hYP : ∀ w ∈ p, w ∉ Y)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hXYa : AnticonnectedSet G (X ∪ Y))
    (hp₁X : VertexComplete G p₁ X)
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pₙ))
    (z : V) (hz : z ∉ X ∪ Y) (hzP : z ∉ p)
    (hzXY : VertexComplete G z (X ∪ Y))
    (hznb : VertexAnticomplete G z {w : V | w ∈ p})
    (hpₙX : ¬ VertexComplete G pₙ X)
    (y v : V) (hy : y ∈ Y) (hvX : v ∈ X)
    (hpₙv : ¬ G.Adj pₙ v) (hvy : ¬ G.Adj v y)
    (hpₙy : G.Adj pₙ y) :
    ¬ G.Adj pn1 v := by
  have hpₙneV : pₙ ≠ v := by
    intro h
    subst pₙ
    exact hvy hpₙy
  have hvneY : v ≠ y := by
    intro h
    subst y
    exact hpₙv hpₙy
  have hpₙneY : pₙ ≠ y := hpₙy.ne
  have h₁ : Gᶜ.Adj pₙ v := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hpₙneV, hpₙv⟩
  have h₂ : Gᶜ.Adj v y := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hvneY, hvy⟩
  have h₃ : ¬ Gᶜ.Adj pₙ y := by
    rw [SimpleGraph.compl_adj]
    exact fun h => h.2 hpₙy
  have hqList : IsPathList Gᶜ [pₙ, v, y] :=
    OddWheelAttachmentBase.isPathList_three h₁ h₂ h₃ hpₙneY
  have hq : IsAntipathFrom G [pₙ, v, y] pₙ y := ⟨hqList, rfl, by simp⟩
  have hqint : ∀ w ∈ SPGT.interior [pₙ, v, y], w ∈ X := by
    intro w hw
    simpa using (show w = v from by simpa [SPGT.interior] using hw) ▸ hvX
  exact _root_.Workspace.Statements.S17.SPGT.thm_17_4 G hG p p₁ pn1 pₙ hp
    hlen hhead hlast hlast1 X Y hXP hYP hXa hYa hXYa hp₁X hYuniq
    z hz hzP hzXY hznb hpₙX y v hy [pₙ, v, y] hq hqint (by rfl)

end Workspace.ProofLemmas.Thm185TripleRRReduction
