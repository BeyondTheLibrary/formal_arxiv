/-  **13.3, the even-antipath half of the balancedness check** (printed p. 83).

    PAPER: *"Now for antipaths, let `uv` be an edge with `u, v ∈ A ∪ C`.  They both therefore
    have nonneighbours in `B`, and since `B ∪ {a₀}` is anticonnected, they are joined by an
    antipath `Q` with interior in `B ∪ {a₀}`.  It suffices to show that `Q` is even, since
    `Q* ⊆ Y ∪ B`.  If `a₀ ∉ Q*`, then `Q` is even since `b₀`-`u`-`Q`-`v`-`b₀` is an antihole.
    So `a₀` is in `Q*`.  But there are no edges between `a₀` and `B`, and so `a₀` is
    nonadjacent to every other vertex in the interior of `Q`; and since `Q` is an antipath, it
    therefore has at most 3 internal vertices, so its length is `≤ 4`.  If it is odd, then it
    has length 3, that is, there are nonadjacent vertices `u₀ ∈ Y` and `v₀ ∈ B`, joined by an
    odd path with interior in `A ∪ C`.  But we have already shown that they are joined by an
    even path, and the result follows from 4.3."*

    The interior of the antipath produced lies in `B ∪ {a₀} ⊆ X ∪ Y ∪ B`, which is the
    *"interior in `X ∪ Y ∪ B`"* that the application of 4.6 needs (`a₀ ∈ Y` by 13.2).  -/
import Mathlib
import Workspace.ProofLemmas.Thm133Setup
import Workspace.ProofLemmas.Thm133EvenPath
import Workspace.ProofLemmas.Thm75AnticonnectedUnion
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S04.Thm_4_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm133EvenAntipath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm133Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **13.3, even antipath.**  PAPER: *"any two adjacent vertices of `A ∪ C` are joined by an
even antipath with interior in `X ∪ Y ∪ B`."* -/
theorem thm133_even_antipath {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {x : List V} (c : Ctx G A C B a₀ b₀ R₀ x)
    (hskew : IsSkewPartition G (Ws G A C B x)ᶜ (Ws G A C B x))
    (hno : ¬ AdmitsBalancedSkewPartition G)
    {u v : V} (hu : u ∈ A ∪ C) (hv : v ∈ A ∪ C) (huv : G.Adj u v) :
    ∃ q : List V, IsAntipathFrom G q u v ∧ (∀ z ∈ SPGT.interior q, z ∈ Ws G A C B x) ∧
      Even (pathLength q) := by
  classical
  have hACsubStrip : A ∪ C ⊆ A ∪ B ∪ C := by
    rintro z (hzA | hzC)
    · exact Or.inl (Or.inl hzA)
    · exact Or.inr hzC
  have hACnotB : ∀ z ∈ A ∪ C, z ∉ B := by
    intro z hz hzB
    rcases hz with hzA | hzC
    · exact (Set.disjoint_left.mp c.stepConn.1.1 hzA) hzB
    · exact (Set.disjoint_left.mp c.stepConn.1.2.2 hzB) hzC
  -- Every vertex on the near side of the strip misses the far end of the other
  -- rung in a step containing it.
  have hmissB : ∀ z ∈ A ∪ C, ∃ b ∈ B, ¬ G.Adj z b := by
    intro z hz
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hzR⟩ :=
      c.stepConn.2.2.2.1 z (hACsubStrip hz)
    have hb₁R : b₁ ∈ R₁ := PathBasics.getLast_mem hs.1.1.2.2
    have hb₂R : b₂ ∈ R₂ := PathBasics.getLast_mem hs.2.1.1.2.2
    have hb₁B : b₁ ∈ B := hs.1.2.2.1
    have hb₂B : b₂ ∈ B := hs.2.1.2.2.1
    rcases hzR with hzR₁ | hzR₂
    · refine ⟨b₂, hb₂B, ?_⟩
      intro hzb₂
      rcases (hs.2.2.2 z hzR₁ b₂ hb₂R).mp hzb₂ with hleft | hright
      · exact (Set.disjoint_left.mp c.stepConn.1.1 hs.2.1.2.1) (hleft.2 ▸ hb₂B)
      · exact hACnotB z hz (hright.1.symm ▸ hb₁B)
    · refine ⟨b₁, hb₁B, ?_⟩
      intro hzb₁
      rcases (hs.2.2.2 b₁ hb₁R z hzR₂).mp hzb₁.symm with hleft | hright
      · exact (Set.disjoint_left.mp c.stepConn.1.1 hs.1.2.1) (hleft.1 ▸ hb₁B)
      · exact hACnotB z hz (hright.2.symm ▸ hb₂B)
  have hanti : Anticomplete G ({a₀} : Set V) B := by
    intro z hz b hb
    have hza : z = a₀ := by simpa using hz
    subst z
    exact c.leftStar_a₀.2.2 b (Or.inl hb)
  have hB₀anti : AnticonnectedSet G (B ∪ ({a₀} : Set V)) :=
    by
      simpa [Set.union_comm] using
        (Workspace.ProofLemmas.Thm75AnticonnectedUnion.thm75AnticonnectedUnion
          G {a₀} B hanti (Set.singleton_nonempty a₀) c.Bne)
  have hB₀subW : B ∪ ({a₀} : Set V) ⊆ Ws G A C B x := by
    rintro z (hzB | hz₀)
    · exact Or.inr hzB
    · have hza : z = a₀ := by simpa using hz₀
      exact hza ▸ Or.inl (Or.inr c.a₀_mem_Y)
  have huout : u ∉ B ∪ ({a₀} : Set V) := fun h =>
    c.AC_disjoint_W u hu (hB₀subW h)
  have hvout : v ∉ B ∪ ({a₀} : Set V) := fun h =>
    c.AC_disjoint_W v hv (hB₀subW h)
  obtain ⟨q, hq, hqint₀⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_antipath_interior_in
      hB₀anti huout hvout
        (by obtain ⟨b, hb, hn⟩ := hmissB u hu; exact ⟨b, Or.inl hb, hn⟩)
        (by obtain ⟨b, hb, hn⟩ := hmissB v hv; exact ⟨b, Or.inl hb, hn⟩)
  have hqintW : ∀ z ∈ SPGT.interior q, z ∈ Ws G A C B x :=
    fun z hz => hB₀subW (hqint₀ z hz)
  refine ⟨q, hq, hqintW, ?_⟩
  have hQlen3 : 3 ≤ q.length :=
    _root_.Workspace.Statements.S04.SPGT.Helpers43.three_le_length hq huv.ne
      (fun hc => hc.2 huv)
  have hQlenEq : q.length = pathLength q + 1 :=
    PathBasics.length_eq_pathLength_add_one hq.1
  by_cases ha₀int : a₀ ∈ SPGT.interior q
  · -- Since `a₀` is anticomplete to `B`, all other internal vertices of the
    -- antipath must be immediately beside it.
    obtain ⟨i, hi, hi1, hi2, hiEq⟩ :=
      PathBasics.exists_getElem_of_mem_interior hq.1 ha₀int
    have hinj : ∀ (j k : ℕ) (hj : j < q.length) (hk : k < q.length),
        ((q[j]'hj) = (q[k]'hk)) ↔ j = k :=
      fun j k hj hk => hq.1.2.1.getElem_inj_iff
    have hnear : ∀ (k : ℕ) (hk : k < q.length), 1 ≤ k → k + 2 ≤ q.length →
        k = i ∨ i + 1 = k ∨ k + 1 = i := by
      intro k hk hk1 hk2
      by_cases hki : k = i
      · exact Or.inl hki
      have hkB : (q[k]'hk) ∈ B := by
        rcases hqint₀ (q[k]'hk) (PathBasics.getElem_mem_interior hq.1 hk hk1 hk2) with
          hkB | hk₀
        · exact hkB
        · exfalso
          have hka : q[k]'hk = a₀ := by simpa using hk₀
          exact hki ((hinj k i hk hi).mp (hka.trans hiEq.symm))
      have hne : q[i]'hi ≠ q[k]'hk := by
        intro he
        exact hki ((hinj i k hi hk).mp he).symm
      have hnadj : ¬ G.Adj (q[i]'hi) (q[k]'hk) := by
        rw [hiEq]
        exact c.leftStar_a₀.2.2 (q[k]'hk) (Or.inl hkB)
      have hc : Gᶜ.Adj (q[i]'hi) (q[k]'hk) :=
        (G.compl_adj _ _).mpr ⟨hne, hnadj⟩
      exact Or.inr ((PathBasics.path_adj_iff hq.1 hi hk).mp hc)
    have hi_le_two : i ≤ 2 := by
      rcases hnear 1 (by omega) (by omega) (by omega) with h | h | h <;> omega
    have hQlen5 : q.length ≤ 5 := by
      rcases hnear (q.length - 2) (by omega) (by omega) (by omega) with h | h | h <;>
        omega
    by_contra hnotEven
    have hodd : Odd (pathLength q) := Nat.not_even_iff_odd.mp hnotEven
    have hoddmod : pathLength q % 2 = 1 := Nat.odd_iff.mp hodd
    have hQlen4 : q.length = 4 := by omega
    obtain ⟨x₀, x₁, x₂, x₃, rfl⟩ := PathGlue.length_eq_four hQlen4
    have h01c : Gᶜ.Adj x₀ x₁ :=
      (PathBasics.path_adj_iff hq.1 (i := 0) (j := 1) (by simp) (by simp)).mpr
        (Or.inl rfl)
    have h12c : Gᶜ.Adj x₁ x₂ :=
      (PathBasics.path_adj_iff hq.1 (i := 1) (j := 2) (by simp) (by simp)).mpr
        (Or.inl rfl)
    have h23c : Gᶜ.Adj x₂ x₃ :=
      (PathBasics.path_adj_iff hq.1 (i := 2) (j := 3) (by simp) (by simp)).mpr
        (Or.inl rfl)
    have h02ne : x₀ ≠ x₂ := by
      simpa using PathBasics.path_ne_of_ne_index hq.1 (i := 0) (j := 2)
        (by simp) (by simp) (by omega)
    have h03ne : x₀ ≠ x₃ := by
      simpa using PathBasics.path_ne_of_ne_index hq.1 (i := 0) (j := 3)
        (by simp) (by simp) (by omega)
    have h13ne : x₁ ≠ x₃ := by
      simpa using PathBasics.path_ne_of_ne_index hq.1 (i := 1) (j := 3)
        (by simp) (by simp) (by omega)
    have h02 : G.Adj x₀ x₂ := by
      by_contra hn
      have hc : Gᶜ.Adj x₀ x₂ := (G.compl_adj _ _).mpr ⟨h02ne, hn⟩
      have := (PathBasics.path_adj_iff hq.1 (i := 0) (j := 2) (by simp) (by simp)).mp hc
      omega
    have h13 : G.Adj x₁ x₃ := by
      by_contra hn
      have hc : Gᶜ.Adj x₁ x₃ := (G.compl_adj _ _).mpr ⟨h13ne, hn⟩
      have := (PathBasics.path_adj_iff hq.1 (i := 1) (j := 3) (by simp) (by simp)).mp hc
      omega
    have hx₀u : x₀ = u := by simpa using hq.2.1
    have hx₃v : x₃ = v := by simpa using hq.2.2
    have h03 : G.Adj x₀ x₃ := by simpa [hx₀u, hx₃v] using huv
    have hx₀AC : x₀ ∈ A ∪ C := hx₀u ▸ hu
    have hx₃AC : x₃ ∈ A ∪ C := hx₃v ▸ hv
    have haCases : a₀ = x₁ ∨ a₀ = x₂ := by
      simpa [SPGT.interior] using ha₀int
    rcases haCases with ha₁ | ha₂
    · have hx₂B : x₂ ∈ B := by
        rcases hqint₀ x₂ (by simp [SPGT.interior]) with hx₂B | hx₂a
        · exact hx₂B
        · have hx₂a' : x₂ = a₀ := by simpa using hx₂a
          exact False.elim (h12c.1 (ha₁.symm.trans hx₂a'.symm))
      have hx₁Y : x₁ ∈ Ys G A C B x := ha₁ ▸ c.a₀_mem_Y
      have hnd : [x₁, x₃, x₀, x₂].Nodup := by
        simp [h01c.1, h12c.1, h23c.1, h02ne, h03ne, h13ne,
          Ne.symm h01c.1, Ne.symm h12c.1, Ne.symm h23c.1,
          Ne.symm h02ne, Ne.symm h03ne, Ne.symm h13ne]
      have hpodd : IsPathFrom G [x₁, x₃, x₀, x₂] x₁ x₂ := by
        refine ⟨PathGlue.isPathList_four hnd h13 h03.symm h02 ?_ ?_ ?_, by simp, by simp⟩
        · exact fun h => h01c.2 h.symm
        · exact h12c.2
        · exact fun h => h23c.2 h.symm
      have hpoddInt : ∀ z ∈ SPGT.interior [x₁, x₃, x₀, x₂],
          z ∈ (Ws G A C B x)ᶜ := by
        intro z hz
        have hz' : z = x₃ ∨ z = x₀ := by simpa [SPGT.interior] using hz
        rcases hz' with hzx₃ | hzx₀
        · exact hzx₃.symm ▸ c.AC_disjoint_W x₃ hx₃AC
        · exact hzx₀.symm ▸ c.AC_disjoint_W x₀ hx₀AC
      obtain ⟨p, hp, hpint, hpeven⟩ :=
        Workspace.ProofLemmas.Thm133EvenPath.thm133_even_path c
          (Or.inl hx₁Y) (Or.inr hx₂B) h12c.2 h12c.1
      have hpint' : ∀ z ∈ SPGT.interior p, z ∈ (Ws G A C B x)ᶜ :=
        fun z hz => c.AC_disjoint_W z (hpint z hz)
      apply hno
      exact (_root_.Workspace.Statements.S04.SPGT.thm_4_3 G c.berge
        (Ws G A C B x)ᶜ (Ws G A C B x) hskew (Or.inl
          ⟨x₁, x₂, [x₁, x₃, x₀, x₂], p,
            Or.inl (Or.inr hx₁Y), Or.inr hx₂B, hpodd, hpoddInt,
            ⟨1, by rfl⟩, hp, hpint', hpeven⟩)).2
    · have hx₁B : x₁ ∈ B := by
        rcases hqint₀ x₁ (by simp [SPGT.interior]) with hx₁B | hx₁a
        · exact hx₁B
        · have hx₁a' : x₁ = a₀ := by simpa using hx₁a
          exact False.elim (h12c.1 (hx₁a'.trans ha₂))
      have hx₂Y : x₂ ∈ Ys G A C B x := ha₂ ▸ c.a₀_mem_Y
      have hnd : [x₂, x₀, x₃, x₁].Nodup := by
        simp [h01c.1, h12c.1, h23c.1, h02ne, h03ne, h13ne,
          Ne.symm h01c.1, Ne.symm h12c.1, Ne.symm h23c.1,
          Ne.symm h02ne, Ne.symm h03ne, Ne.symm h13ne]
      have hpodd : IsPathFrom G [x₂, x₀, x₃, x₁] x₂ x₁ := by
        refine ⟨PathGlue.isPathList_four hnd h02.symm h03 h13.symm ?_ ?_ ?_, by simp, by simp⟩
        · exact h23c.2
        · exact fun h => h12c.2 h.symm
        · exact h01c.2
      have hpoddInt : ∀ z ∈ SPGT.interior [x₂, x₀, x₃, x₁],
          z ∈ (Ws G A C B x)ᶜ := by
        intro z hz
        have hz' : z = x₀ ∨ z = x₃ := by simpa [SPGT.interior] using hz
        rcases hz' with hzx₀ | hzx₃
        · exact hzx₀.symm ▸ c.AC_disjoint_W x₀ hx₀AC
        · exact hzx₃.symm ▸ c.AC_disjoint_W x₃ hx₃AC
      obtain ⟨p, hp, hpint, hpeven⟩ :=
        Workspace.ProofLemmas.Thm133EvenPath.thm133_even_path c
          (Or.inl hx₂Y) (Or.inr hx₁B) (fun h => h12c.2 h.symm) h12c.1.symm
      have hpint' : ∀ z ∈ SPGT.interior p, z ∈ (Ws G A C B x)ᶜ :=
        fun z hz => c.AC_disjoint_W z (hpint z hz)
      apply hno
      exact (_root_.Workspace.Statements.S04.SPGT.thm_4_3 G c.berge
        (Ws G A C B x)ᶜ (Ws G A C B x) hskew (Or.inl
          ⟨x₂, x₁, [x₂, x₀, x₃, x₁], p,
            Or.inl (Or.inr hx₂Y), Or.inr hx₁B, hpodd, hpoddInt,
            ⟨1, by rfl⟩, hp, hpint', hpeven⟩)).2
  · have hqintB : ∀ z ∈ SPGT.interior q, z ∈ B := by
      intro z hz
      rcases hqint₀ z hz with hzB | hz₀
      · exact hzB
      · have hza : z = a₀ := by simpa using hz₀
        exact False.elim (ha₀int (hza ▸ hz))
    by_cases hlen4 : 4 ≤ q.length
    · have hb₀u : b₀ ≠ u := by
        intro h
        exact c.rightStar_b₀.1 (h.symm ▸ hACsubStrip hu)
      have hb₀v : b₀ ≠ v := by
        intro h
        exact c.rightStar_b₀.1 (h.symm ▸ hACsubStrip hv)
      have hb₀q : b₀ ∉ q := by
        intro hbq
        by_cases hbu : b₀ = u
        · exact hb₀u hbu
        by_cases hbv : b₀ = v
        · exact hb₀v hbv
        have hbint : b₀ ∈ SPGT.interior q :=
          (PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hbq, hbu, hbv⟩
        exact c.rightStar_b₀.1 (Or.inl (Or.inr (hqintB b₀ hbint)))
      have he := PrismBasics.even_of_antipath_closed_by_vertex' c.berge hq hlen4 hb₀q
        hb₀u hb₀v (c.rightStar_b₀.2.2 u hu) (c.rightStar_b₀.2.2 v hv)
        (fun z hz => c.rightStar_b₀.2.1 z (hqintB z hz))
      obtain ⟨k, hk⟩ := he
      refine ⟨k - 1, ?_⟩
      omega
    · have hQlen : q.length = 3 := by omega
      refine ⟨1, ?_⟩
      omega

end Workspace.ProofLemmas.Thm133EvenAntipath
