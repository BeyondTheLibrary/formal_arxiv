import Workspace.ProofLemmas.Thm93CaseTwoSaturated
import Workspace.ProofLemmas.Thm93CaseTwoPairs
import Workspace.ProofLemmas.PrismBasics

/-! The two uses of 2.1 at the end of 9.3. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoLeaps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm93CaseTwoCommon Workspace.ProofLemmas.Thm93CaseTwoSaturated
open Workspace.ProofLemmas.Thm93CaseTwoPairs

variable {V : Type*}

/-- In a leap on a path obtained by adding two ends, the leap vertices have one neighbour
each on the original path, at its respective ends. -/
theorem leap_end_neighbors {G : SimpleGraph V} {Q : List V} {x y a b f g : V}
    (hQ : IsPathFrom G Q x y) (hleap : IsLeapForPath G (b :: (Q ++ [a])) f g) :
    (∀ w ∈ Q, G.Adj f w ↔ w = x) ∧ (∀ w ∈ Q, G.Adj g w ↔ w = y) := by
  have hl : (b :: (Q ++ [a])).length = Q.length + 2 := by simp
  have hpos := PathBasics.path_length_pos hQ.1
  have hx := PathBasics.getElem_zero_of_head? hQ.2.1 hpos
  have hy := PathBasics.getElem_last_of_getLast? hQ.2.2 hpos
  constructor
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
    have h := hleap.2.2.2.2.1 (i + 1) (by simp; omega)
    rw [List.getElem_cons_succ, List.getElem_append_left hi] at h
    constructor
    · intro hadj
      have hidx := h.mp hadj
      have hi0 : i = 0 := by rw [hl] at hidx; omega
      subst i
      exact hx
    · intro heq
      have hi0 : i = 0 := hQ.1.2.1.getElem_inj_iff.mp (heq.trans hx.symm)
      exact h.mpr (Or.inr (Or.inl (by omega)))
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
    have h := hleap.2.2.2.2.2 (i + 1) (by simp; omega)
    rw [List.getElem_cons_succ, List.getElem_append_left hi] at h
    constructor
    · intro hadj
      have hidx := h.mp hadj
      have hi0 : i = Q.length - 1 := by rw [hl] at hidx; omega
      simpa only [hi0] using hy
    · intro heq
      have hi0 : i = Q.length - 1 := hQ.1.2.1.getElem_inj_iff.mp (heq.trans hy.symm)
      exact h.mpr (Or.inr (Or.inl (by rw [hl]; omega)))

/-- PAPER (9.3, p. 49): "`f₁,f₂` have no common neighbour in `Q₂` (because `R` could be
completed to an odd hole through any such common neighbour)." -/
theorem no_common_neighbor {G : SimpleGraph V} (hG : Berge G)
    {Q Q' : List V} {x y a b f g : V}
    (hQ : IsPathFrom G Q x y) (hodd : Odd (pathLength Q))
    (hF : f ∉ Q) (hGQ : g ∉ Q) (hQlen : 1 ≤ pathLength Q)
    (hleap : IsLeapForPath G (b :: (Q ++ [a])) f g)
    (hdisj : ∀ w ∈ Q', w ∉ Q)
    (hanti : Anticomplete G {v | v ∈ Q'} {v | v ∈ Q}) :
    ∀ w ∈ Q', ¬ (G.Adj f w ∧ G.Adj g w) := by
  obtain ⟨hf, hg⟩ := leap_end_neighbors hQ hleap
  have hxf := (hf x (PathBasics.isPathFrom_ends_mem hQ).1).mpr rfl
  have hyg := (hg y (PathBasics.isPathFrom_ends_mem hQ).2).mpr rfl
  have hp := PathAttach.isPathFrom_cons_concat hQ hxf hyg hleap.2.2.2.1
    hleap.2.2.1 hF hGQ (fun v hv hne h => hne ((hf v hv).mp h))
    (fun v hv hne h => hne ((hg v hv).mp h))
  intro w hw ⟨hwf, hwg⟩
  have hwP : w ∉ f :: (Q ++ [g]) := by
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
    exact ⟨hwf.ne.symm, hdisj w hw, hwg.ne.symm⟩
  have hev := PrismBasics.even_of_path_closed_by_vertex hG hp
    (by simp; unfold pathLength at hQlen; omega) hwP hwf.symm hwg.symm
    (by intro v hv; apply hanti w hw v; simpa [SPGT.interior] using hv)
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨j, hj⟩ := hev
  simp only [List.length_cons, List.length_append, List.length_nil] at hj
  unfold pathLength at hk
  omega

/-- An odd antipath between adjacent vertices, with its interior in a two-vertex set,
uses both those vertices, in one order or the other. -/
theorem antipath_two_interior {G : SimpleGraph V} {q : List V} {x y f g : V}
    (hq : IsAntipathFrom G q x y) (hodd : Odd (pathLength q)) (hxy : G.Adj x y)
    (hint : ∀ w ∈ SPGT.interior q, w ∈ ({f, g} : Set V)) :
    q = [x, f, g, y] ∨ q = [x, g, f, y] := by
  have hintlen : (SPGT.interior q).length ≤ 2 := by
    have hnd : (SPGT.interior q).Nodup := hq.1.2.1.sublist ((List.dropLast_sublist q.tail).trans (List.tail_sublist q))
    have hh : SPGT.interior q ⊆ [f, g] := by
      intro w hw
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hint w hw
    classical
    have hs : (SPGT.interior q).toFinset ⊆ ({f, g} : Finset V) := by
      intro w hw
      simpa using hh (List.mem_toFinset.mp hw)
    have hc := Finset.card_le_card hs
    rw [List.toFinset_card_of_nodup hnd] at hc
    exact hc.trans Finset.card_le_two
  rw [PathBasics.interior_length] at hintlen
  have hn1 : pathLength q ≠ 1 := by
    intro h
    exact (PathBasics.isPathFrom_ends_adj_of_length_one hq h).2 hxy
  have hlen : q.length = 4 := by
    obtain ⟨k, hk⟩ := hodd
    unfold pathLength at hk hn1
    omega
  rcases q with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, tl⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> try omega
  have htl : tl = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst tl
  have h0 : v0 = x := by simpa using hq.2.1
  have h3 : v3 = y := by simpa using hq.2.2
  subst v0
  subst v3
  have h1 : v1 = f ∨ v1 = g := hint v1 (by simp [SPGT.interior])
  have h2 : v2 = f ∨ v2 = g := hint v2 (by simp [SPGT.interior])
  have hne : v1 ≠ v2 := by
    have h := hq.1.2.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    exact h.2.1.1
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (hne rfl).elim

/-- Read the four-vertex antipath from the short-path alternative of 2.1. -/
theorem four_antipath_neighbors {G : SimpleGraph V} {x y f g : V}
    (h : IsAntipathFrom G [x, f, g, y] x y) :
    (∀ w ∈ [x, y], G.Adj g w ↔ w = x) ∧
    (∀ w ∈ [x, y], G.Adj f w ↔ w = y) := by
  have hxf : ¬ G.Adj f x :=
    (PathBasics.path_adj_succ h.1 (i := 0) (by simp)).2 ∘ SimpleGraph.Adj.symm
  have hgy : ¬ G.Adj g y := (PathBasics.path_adj_succ h.1 (i := 2) (by simp)).2
  have hnd := h.1.2.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  have hxg : G.Adj g x := by
    have hn := PathBasics.path_not_adj_of_gap h.1 (i := 0) (j := 2)
      (by simp) (by simp) (by omega) (by omega)
    by_contra hh
    exact hn ⟨hnd.1.2.1, fun h => hh h.symm⟩
  have hfy : G.Adj f y := by
    have hn := PathBasics.path_not_adj_of_gap h.1 (i := 1) (j := 3)
      (by simp) (by simp) (by omega) (by omega)
    by_contra hh
    exact hn ⟨hnd.2.1.2, hh⟩
  constructor <;> intro w hw <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  · rcases hw with rfl | rfl
    · simp [hxg]
    · exact iff_of_false hgy (Ne.symm hnd.1.2.2)
  · rcases hw with rfl | rfl
    · exact iff_of_false hxf hnd.1.2.2
    · simp [hfy]

variable [Fintype V] [DecidableEq V]

/-- PAPER (9.3, p. 49): "so by 2.1, `f₁,f₂` is also a leap for the path
`a₁-y₂-Q₂-x₂-b₁` (this path might have length 3, but still we get a leap by 2.1.3 ...)".
We record its two private neighbours, which are all the final sentence uses. -/
theorem second_pair_neighbors {G : SimpleGraph V} (hG : Berge G)
    {Q : List V} {x y a b f g : V}
    (hQ : IsPathFrom G Q x y) (hodd : Odd (pathLength Q))
    (hp : IsPathFrom G (b :: (Q ++ [a])) b a)
    (hfg : f ≠ g) (hnfg : ¬ G.Adj f g)
    (hfp : f ∉ b :: (Q ++ [a])) (hgp : g ∉ b :: (Q ++ [a]))
    (ha : VertexComplete G a ({f, g} : Set V)) (hb : VertexComplete G b ({f, g} : Set V))
    (hcommon : ∀ w ∈ Q, ¬ (G.Adj f w ∧ G.Adj g w)) :
    ((∀ w ∈ Q, G.Adj f w ↔ w = x) ∧ (∀ w ∈ Q, G.Adj g w ↔ w = y)) ∨
    ((∀ w ∈ Q, G.Adj g w ↔ w = x) ∧ (∀ w ∈ Q, G.Adj f w ↔ w = y)) := by
  have hanti : AnticonnectedSet G ({f, g} : Set V) := by
    intro u v
    have hu : (u : V) = f ∨ (u : V) = g := u.property
    have hv : (v : V) = f ∨ (v : V) = g := v.property
    by_cases heq : u = v
    · exact heq ▸ SimpleGraph.Reachable.refl u
    · apply SimpleGraph.Adj.reachable
      change Gᶜ.Adj (u : V) (v : V)
      refine ⟨fun h => heq (Subtype.ext h), ?_⟩
      rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
      · exact G.irrefl
      · exact hnfg
      · exact fun h => hnfg h.symm
      · exact G.irrefl
  have hlen : pathLength (b :: (Q ++ [a])) = pathLength Q + 2 := by
    have hpos := PathBasics.path_length_pos hQ.1
    rw [PathAttach.pathLength_cons_append_singleton]
    unfold pathLength
    omega
  have hnoedge : ¬ ∃ u ∈ b :: (Q ++ [a]), ∃ v ∈ b :: (Q ++ [a]),
      EdgeComplete G ({f, g} : Set V) u v := by
    apply no_complete_edge hp (by omega)
    intro w hw hc
    have hwQ : w ∈ Q := by simpa [SPGT.interior] using hw
    exact hcommon w hwQ ⟨(hc f (by simp)).symm, (hc g (by simp)).symm⟩
  have hoff : ∀ w ∈ b :: (Q ++ [a]), w ∉ ({f, g} : Set V) := by
    intro w hw hwfg
    rcases hwfg with rfl | rfl
    exacts [hfp hw, hgp hw]
  have hpodd : Odd (pathLength (b :: (Q ++ [a]))) := by
    rw [hlen]
    exact hodd.add_even (by decide)
  rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG ({f, g} : Set V) hanti
    (b :: (Q ++ [a])) b a hp hoff hpodd hb ha with h | ⟨_, u, hu, v, hv, hl⟩ | h
  · exact (hnoedge h).elim
  · have hu' : u = f ∨ u = g := hu
    have hv' : v = f ∨ v = g := hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact (hl.2.2.1 rfl).elim
    · exact Or.inl (leap_end_neighbors hQ hl)
    · exact Or.inr (leap_end_neighbors hQ hl)
    · exact (hl.2.2.1 rfl).elim
  · obtain ⟨h3, c, d, hint, R, hR, hRodd, hRint⟩ := h
    have hQlen : pathLength Q = 1 := by omega
    have hQeq := KnotLabels.eq_pair_of_length_one hQ hQlen
    have hcd : Q = [c, d] := by simpa [SPGT.interior] using hint
    have hc : c = x ∧ d = y := by simpa [hQeq] using hcd.symm
    rcases hc with ⟨rfl, rfl⟩
    have hxy := PathBasics.isPathFrom_ends_adj_of_length_one hQ hQlen
    rcases antipath_two_interior hR hRodd hxy hRint with hrEq | hrEq
    · rw [hrEq] at hR
      exact Or.inr (by simpa only [hQeq] using four_antipath_neighbors hR)
    · rw [hrEq] at hR
      exact Or.inl (by simpa only [hQeq] using four_antipath_neighbors hR)

/-- The common-neighbour case of 9.3 is completed by applying the second-leap argument to
the other antipath. -/
theorem pairs_from_long_leap {G : SimpleGraph V} (hG : Berge G)
    {Q₁ Q₂ : List V} {x₁ y₁ x₂ y₂ a b : V} {K F : Set V}
    (hF : F ⊆ Kᶜ)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hodd₁ : Odd (pathLength Q₁)) (hodd₂ : Odd (pathLength Q₂))
    (hp₁ : IsPathFrom Gᶜ (b :: (Q₁ ++ [a])) b a)
    (hp₂ : IsPathFrom Gᶜ (b :: (Q₂ ++ [a])) b a)
    (hQ₁K : ∀ w ∈ Q₁, w ∈ K) (hQ₂K : ∀ w ∈ Q₂, w ∈ K)
    (ha : a ∈ common G K F) (hb : b ∈ common G K F)
    (hdisj : ∀ w ∈ Q₁, w ∉ Q₂)
    (hcomp : Complete G {v | v ∈ Q₁} {v | v ∈ Q₂})
    (hleap : (∃ f ∈ F, ∃ g ∈ F, IsLeapForPath Gᶜ (b :: (Q₁ ++ [a])) f g) ∨
      (∃ f ∈ F, ∃ g ∈ F, IsLeapForPath Gᶜ (b :: (Q₂ ++ [a])) f g)) :
    ComplementPairs G Q₁ Q₂ x₁ y₁ x₂ y₂ F := by
  have hGc := HoleBasics.berge_compl.mpr hG
  have hpos₁ : 1 ≤ pathLength Q₁ := by obtain ⟨i, hi⟩ := hodd₁; omega
  have hpos₂ : 1 ≤ pathLength Q₂ := by obtain ⟨i, hi⟩ := hodd₂; omega
  have hoff : ∀ f ∈ F, ∀ Q : List V, (∀ w ∈ Q, w ∈ K) → f ∉ b :: (Q ++ [a]) := by
    intro f hf Q hQ hw
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with heq | hw | heq
    · exact hF hf (heq ▸ hb.1)
    · exact hF hf (hQ _ hw)
    · exact hF hf (heq ▸ ha.1)
  have hcomplete : ∀ f ∈ F, ∀ g ∈ F,
      VertexComplete Gᶜ a ({f, g} : Set V) ∧ VertexComplete Gᶜ b ({f, g} : Set V) := by
    intro f hf g hg
    constructor <;> intro w hw <;> rcases hw with rfl | rfl
    exacts [ha.2 _ hf, ha.2 _ hg, hb.2 _ hf, hb.2 _ hg]
  rcases hleap with ⟨f, hf, g, hg, hl⟩ | ⟨f, hf, g, hg, hl⟩
  · obtain ⟨hx, hy⟩ := leap_end_neighbors hQ₁ hl
    have hfg : G.Adj f g := by
      by_contra h
      exact hl.2.2.2.1 ⟨hl.2.2.1, h⟩
    have hcommon := no_common_neighbor hGc hQ₁ hodd₁
      (fun h => hF hf (hQ₁K f h)) (fun h => hF hg (hQ₁K g h)) hpos₁ hl
      (fun w hw h => hdisj w h hw)
      (fun w hw v hv h => h.2 (hcomp v hv w hw).symm)
    have hsecond := second_pair_neighbors hGc hQ₂ hodd₂ hp₂ hl.2.2.1 hl.2.2.2.1
      (hoff f hf Q₂ hQ₂K) (hoff g hg Q₂ hQ₂K)
      (hcomplete f hf g hg).1 (hcomplete f hf g hg).2 hcommon
    refine ⟨f, hf, g, hg, hfg, hx, hy, ?_⟩
    rcases hsecond with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  · obtain ⟨hx, hy⟩ := leap_end_neighbors hQ₂ hl
    have hfg : G.Adj f g := by
      by_contra h
      exact hl.2.2.2.1 ⟨hl.2.2.1, h⟩
    have hcommon := no_common_neighbor hGc hQ₂ hodd₂
      (fun h => hF hf (hQ₂K f h)) (fun h => hF hg (hQ₂K g h)) hpos₂ hl hdisj
      (fun w hw v hv h => h.2 (hcomp w hw v hv))
    have hsecond := second_pair_neighbors hGc hQ₁ hodd₁ hp₁ hl.2.2.1 hl.2.2.2.1
      (hoff f hf Q₁ hQ₁K) (hoff g hg Q₁ hQ₁K)
      (hcomplete f hf g hg).1 (hcomplete f hf g hg).2 hcommon
    rcases hsecond with h | h
    · exact ⟨f, hf, g, hg, hfg, h.1, h.2, Or.inl ⟨hx, hy⟩⟩
    · exact ⟨g, hg, f, hf, hfg.symm, h.1, h.2, Or.inr ⟨hy, hx⟩⟩

end Workspace.ProofLemmas.Thm93CaseTwoLeaps
