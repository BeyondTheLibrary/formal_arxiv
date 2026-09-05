import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

namespace SPGT

/-! ### Encoding infrastructure

None of the lemmas in this section has a counterpart in the paper; they are bookkeeping
for the list encoding of paths, holes and their arcs, plus the counting of `X`-complete
edges.  They belong in `Workspace/ProofLemmas/` once lifted. -/

section Helpers

variable {V : Type*}

/-- The set of `X`-complete edges spanned by a list of vertices. -/
private def Xed (G : SimpleGraph V) (X : Set V) (l : List V) : Set (Sym2 V) :=
  {e : Sym2 V | ∃ u ∈ l, ∃ v ∈ l, e = s(u, v) ∧ EdgeComplete G X u v}

private theorem head?_eq (l : List V) (h : 0 < l.length) : l.head? = some (l[0]'h) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h]

private theorem getLast?_eq (l : List V) (h : 0 < l.length) :
    l.getLast? = some (l[l.length - 1]'(by omega)) := by
  rw [List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (show l.length - 1 < l.length by omega)]

private theorem mem_take_iff {l : List V} {k : ℕ} {w : V} :
    w ∈ l.take k ↔ ∃ (i : ℕ) (h : i < l.length), i < k ∧ l[i]'h = w := by
  constructor
  · intro hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
    have hlt : i < l.length ∧ i < k := by
      simp only [List.length_take] at hi; omega
    exact ⟨i, hlt.1, hlt.2, by simp only [List.getElem_take]⟩
  · rintro ⟨i, h, hik, rfl⟩
    have hi : i < (l.take k).length := by simp only [List.length_take]; omega
    have he : (l.take k)[i]'hi = l[i]'h := by simp only [List.getElem_take]
    rw [← he]
    exact List.getElem_mem hi

private theorem mem_drop_iff {l : List V} {k : ℕ} {w : V} :
    w ∈ l.drop k ↔ ∃ (i : ℕ) (h : i < l.length), k ≤ i ∧ l[i]'h = w := by
  constructor
  · intro hw
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
    have hj' : k + j < l.length := by simp only [List.length_drop] at hj; omega
    exact ⟨k + j, hj', by omega, by simp only [List.getElem_drop]⟩
  · rintro ⟨i, h, hik, rfl⟩
    have hi : i - k < (l.drop k).length := by simp only [List.length_drop]; omega
    have hki : k + (i - k) = i := by omega
    have he : (l.drop k)[i - k]'hi = l[i]'h := by
      simp only [List.getElem_drop, hki]
    rw [← he]
    exact List.getElem_mem hi

private theorem Xed_congr {G : SimpleGraph V} {X : Set V} {l₁ l₂ : List V}
    (h : ∀ w, w ∈ l₁ ↔ w ∈ l₂) : Xed G X l₁ = Xed G X l₂ := by
  ext e
  constructor
  · rintro ⟨u, hu, v, hv, he, hE⟩
    exact ⟨u, (h u).mp hu, v, (h v).mp hv, he, hE⟩
  · rintro ⟨u, hu, v, hv, he, hE⟩
    exact ⟨u, (h u).mpr hu, v, (h v).mpr hv, he, hE⟩

private theorem Xed_eq_empty {G : SimpleGraph V} {X : Set V} {l : List V}
    (h : ∀ u ∈ l, ∀ v ∈ l, G.Adj u v → ¬ (VertexComplete G u X ∧ VertexComplete G v X)) :
    Xed G X l = ∅ := by
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨u, hu, v, hv, -, hE⟩
  exact h u hu v hv hE.1 ⟨hE.2.1, hE.2.2⟩

variable [Fintype V] [DecidableEq V]

private theorem Xed_split {G : SimpleGraph V} {X : Set V} {q q₁ q₂ : List V}
    (hs1 : ∀ w ∈ q₁, w ∈ q) (hs2 : ∀ w ∈ q₂, w ∈ q)
    (hcover : ∀ u ∈ q, ∀ v ∈ q, G.Adj u v → ((u ∈ q₁ ∧ v ∈ q₁) ∨ (u ∈ q₂ ∧ v ∈ q₂)))
    (hdisj : ∀ u ∈ q₁, ∀ v ∈ q₁, u ∈ q₂ → v ∈ q₂ → ¬ G.Adj u v) :
    (Xed G X q).ncard = (Xed G X q₁).ncard + (Xed G X q₂).ncard := by
  have hunion : Xed G X q = Xed G X q₁ ∪ Xed G X q₂ := by
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hE⟩
      rcases hcover u hu v hv hE.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨u, h1, v, h2, rfl, hE⟩
      · exact Or.inr ⟨u, h1, v, h2, rfl, hE⟩
    · rintro (⟨u, hu, v, hv, he, hE⟩ | ⟨u, hu, v, hv, he, hE⟩)
      · exact ⟨u, hs1 u hu, v, hs1 v hv, he, hE⟩
      · exact ⟨u, hs2 u hu, v, hs2 v hv, he, hE⟩
  have hd : Disjoint (Xed G X q₁) (Xed G X q₂) := by
    rw [Set.disjoint_left]
    rintro e ⟨u, hu, v, hv, rfl, hE⟩ ⟨u', hu', v', hv', he, hE'⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdisj u hu v hv hu' hv' hE.1
    · exact hdisj u hu v hv hv' hu' hE.1
  rw [hunion, Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]

/-- Index reading of hole-adjacency, with the modular arithmetic already discharged. -/
private theorem hole_adj_index {G : SimpleGraph V} {cl : List V} (hc : IsHoleList G cl)
    {i j : ℕ} (hi : i < cl.length) (hj : j < cl.length)
    (h : G.Adj ((cl)[i]'hi) ((cl)[j]'hj)) :
    j = i + 1 ∨ i = j + 1 ∨ (i = 0 ∧ j = cl.length - 1) ∨ (j = 0 ∧ i = cl.length - 1) := by
  have hres := (HoleBasics.hole_adj_iff hc hi hj).mp h
  have e1 : (i + 1) % cl.length = if i + 1 = cl.length then 0 else i + 1 := by
    by_cases h' : i + 1 = cl.length
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  have e2 : (j + 1) % cl.length = if j + 1 = cl.length then 0 else j + 1 := by
    by_cases h' : j + 1 = cl.length
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at hres
  split_ifs at hres <;> omega

/-- A hole has no triangle. -/
private theorem hole_no_triangle {G : SimpleGraph V} {cl : List V} (hc : IsHoleList G cl)
    {a b d : V} (ha : a ∈ cl) (hb : b ∈ cl) (hd : d ∈ cl)
    (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d) : False := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  have h1 := hole_adj_index hc hi hj hab
  have h2 := hole_adj_index hc hi hk had
  have h3 := hole_adj_index hc hj hk hbd
  have h4 : 4 ≤ cl.length := hc.1
  have hij : i ≠ j := by rintro rfl; exact G.irrefl hab
  have hik : i ≠ k := by rintro rfl; exact G.irrefl had
  have hjk : j ≠ k := by rintro rfl; exact G.irrefl hbd
  omega

/-- A proper arc of a hole (an initial segment shorter than the whole cycle) is a path. -/
private theorem isPathList_hole_take {G : SimpleGraph V} {cl : List V} (hc : IsHoleList G cl)
    {t : ℕ} (h1 : 1 ≤ t) (h2 : t + 1 ≤ cl.length) : IsPathList G (cl.take t) := by
  obtain ⟨hlen, hnd, hadj⟩ := hc
  have hlt : (cl.take t).length = t := by simp only [List.length_take]; omega
  refine ⟨?_, List.Nodup.sublist (List.take_sublist t cl) hnd, ?_⟩
  · intro hnil
    rw [hnil] at hlt; simp at hlt; omega
  · intro i j hi hj
    rw [hlt] at hi hj
    have hi' : i < cl.length := by omega
    have hj' : j < cl.length := by omega
    have ei : (cl.take t)[i]'(by omega) = ((cl)[i]'hi') := by simp only [List.getElem_take]
    have ej : (cl.take t)[j]'(by omega) = ((cl)[j]'hj') := by simp only [List.getElem_take]
    rw [ei, ej, hadj i j hi' hj',
      Nat.mod_eq_of_lt (show i + 1 < cl.length by omega),
      Nat.mod_eq_of_lt (show j + 1 < cl.length by omega)]
    omega

private theorem head?_take {l : List V} {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ l.length) :
    (l.take t).head? = some (l[0]'(by omega)) := by
  have hlt : (l.take t).length = t := by simp only [List.length_take]; omega
  rw [head?_eq _ (by omega)]
  congr 1
  simp only [List.getElem_take]

private theorem getLast?_take {l : List V} {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ l.length) :
    (l.take t).getLast? = some (l[t - 1]'(by omega)) := by
  have hlt : (l.take t).length = t := by simp only [List.length_take]; omega
  rw [getLast?_eq _ (by omega)]
  congr 1
  simp only [hlt, List.getElem_take]

private theorem getElem_append_mid (s q t : List V) (i : ℕ) (hi : i < q.length)
    (h : s.length + i < (s ++ q ++ t).length) :
    (s ++ q ++ t)[s.length + i]'h = q[i]'hi := by
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  have e : s.length + i - s.length = i := by omega
  simp only [e]

private theorem length_eq_two {α : Type*} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- Transport of the "no neighbour outside" property from a path `q` to a contiguous
block `q'` of it, described by an index window `[lo, hi]`. -/
private theorem sub_nbr_block {G : SimpleGraph V} {p q q' : List V} (hql : IsPathList G q)
    (hnbr : ∀ v ∈ p, v ∉ q → ∀ w ∈ SPGT.interior q, ¬ G.Adj v w)
    {lo hi : ℕ} (hhi : hi < q.length)
    (hmem' : ∀ (c : ℕ) (hc : c < q.length), lo ≤ c → c ≤ hi → (q[c]'hc) ∈ q')
    (hint' : ∀ w ∈ SPGT.interior q',
        ∃ (c : ℕ) (hc : c < q.length), lo < c ∧ c < hi ∧ (q[c]'hc) = w) :
    ∀ v ∈ p, v ∉ q' → ∀ w ∈ SPGT.interior q', ¬ G.Adj v w := by
  intro v hv hvq' w hw hadj
  obtain ⟨c, hc, hlo, hhic, rfl⟩ := hint' w hw
  by_cases hvq : v ∈ q
  · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hvq
    have hrel := (PathBasics.path_adj_iff hql hm hc).mp hadj
    exact hvq' (hmem' m hm (by omega) (by omega))
  · exact hnbr v hv hvq _ (PathBasics.getElem_mem_interior hql hc (by omega) (by omega)) hadj

variable [Fintype V] [DecidableEq V]


/-- **2.3, first assertion** — by induction on the length of `Q`, exactly as printed.

The two facts extracted from "`Q` is a subpath of the path or hole `P`" are `hsub`
(vertices of `Q` are vertices of `P`) and `hnbr` (a vertex of `P` outside `Q` has no
neighbour in `Q*`); both are inherited by the two halves of `Q`. -/
private theorem key {G : SimpleGraph V} (hG : Berge G) {X : Set V} (hX : AnticonnectedSet G X)
    {p : List V} (hpX : ∀ w ∈ p, w ∉ X) :
    ∀ (n : ℕ) (q : List V) (a b : V), q.length ≤ n →
      (∀ w ∈ q, w ∈ p) →
      (∀ v ∈ p, v ∉ q → ∀ w ∈ SPGT.interior q, ¬ G.Adj v w) →
      IsPathFrom G q a b → VertexComplete G a X → VertexComplete G b X →
      ((Xed G X q).ncard % 2 = pathLength q % 2 ∨
        (∀ w ∈ p, VertexComplete G w X → w = a ∨ w = b)) := by
  intro n
  induction n with
  | zero =>
    intro q a b hn _ _ hq _ _
    exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hn))
      (PathBasics.path_ne_nil hq.1)
  | succ n ih =>
    intro q a b hn hsub hnbr hq hca hcb
    have hql : IsPathList G q := hq.1
    have hqpos : 0 < q.length := PathBasics.path_length_pos hql
    have hq0 : (q[0]'hqpos) = a := PathBasics.getElem_zero_of_head? hq.2.1 hqpos
    have hqlast : (q[q.length - 1]'(by omega)) = b :=
      PathBasics.getElem_last_of_getLast? hq.2.2 hqpos
    have hamem : a ∈ q := (PathBasics.isPathFrom_ends_mem hq).1
    have hbmem : b ∈ q := (PathBasics.isPathFrom_ends_mem hq).2
    by_cases hint : ∃ w ∈ SPGT.interior q, VertexComplete G w X
    -- PAPER: *"If some internal vertex of `Q` is `X`-complete then the result follows
    -- from the inductive hypothesis"* — split `Q` there and add the two halves.
    · obtain ⟨w, hw, hcw⟩ := hint
      obtain ⟨i, hi, hi1, hi2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hql hw
      have hq1len : (q.take (i + 1)).length = i + 1 := by
        simp only [List.length_take]; omega
      have hq2len : (q.drop i).length = q.length - i := by simp only [List.length_drop]
      have hq1l : IsPathList G (q.take (i + 1)) := PathBasics.isPathList_take hql (by omega)
      have hq2l : IsPathList G (q.drop i) := PathBasics.isPathList_drop hql (by omega)
      have hq1from : IsPathFrom G (q.take (i + 1)) a (q[i]'hi) := by
        refine ⟨hq1l, ?_, ?_⟩
        · rw [head?_take (by omega) (by omega), hq0]
        · rw [getLast?_take (by omega) (by omega)]
          congr 1
      have hq2from : IsPathFrom G (q.drop i) (q[i]'hi) b := by
        refine ⟨hq2l, ?_, ?_⟩
        · rw [List.head?_drop, List.getElem?_eq_getElem hi]
        · rw [List.getLast?_drop, if_neg (by omega)]
          exact hq.2.2
      -- both halves inherit `hsub` and `hnbr`
      have hsub1 : ∀ z ∈ q.take (i + 1), z ∈ p := fun z hz => hsub z (List.take_subset _ _ hz)
      have hsub2 : ∀ z ∈ q.drop i, z ∈ p := fun z hz => hsub z (List.drop_subset _ _ hz)
      have hnbr1 : ∀ v ∈ p, v ∉ q.take (i + 1) →
          ∀ z ∈ SPGT.interior (q.take (i + 1)), ¬ G.Adj v z := by
        refine sub_nbr_block (lo := 0) (hi := i) hql hnbr hi ?_ ?_
        · intro c hc _ hci
          exact mem_take_iff.mpr ⟨c, hc, by omega, rfl⟩
        · intro z hz
          obtain ⟨c, hc, hc1, hc2, hce⟩ := PathBasics.exists_getElem_of_mem_interior hq1l hz
          rw [hq1len] at hc2
          have hcq : c < q.length := by omega
          refine ⟨c, hcq, by omega, by omega, ?_⟩
          rw [← hce]
          simp only [List.getElem_take]
      have hnbr2 : ∀ v ∈ p, v ∉ q.drop i → ∀ z ∈ SPGT.interior (q.drop i), ¬ G.Adj v z := by
        refine sub_nbr_block (lo := i) (hi := q.length - 1) hql hnbr (by omega) ?_ ?_
        · intro c hc hci _
          exact mem_drop_iff.mpr ⟨c, hc, by omega, rfl⟩
        · intro z hz
          obtain ⟨c, hc, hc1, hc2, hce⟩ := PathBasics.exists_getElem_of_mem_interior hq2l hz
          rw [hq2len] at hc2
          have hcq : i + c < q.length := by omega
          refine ⟨i + c, hcq, by omega, by omega, ?_⟩
          rw [← hce]
          simp only [List.getElem_drop]
      -- inductive hypothesis on each half
      have hres1 := ih (q.take (i + 1)) a (q[i]'hi) (by omega) hsub1 hnbr1 hq1from hca hcw
      have hres2 := ih (q.drop i) (q[i]'hi) b (by omega) hsub2 hnbr2 hq2from hcw hcb
      have hne1 : ¬ (∀ z ∈ p, VertexComplete G z X → z = a ∨ z = (q[i]'hi)) := by
        intro hcon
        rcases hcon b (hsub b hbmem) hcb with h | h
        · rw [← hq0, ← hqlast] at h
          exact PathBasics.path_ne_of_ne_index hql (by omega) hqpos (by omega) h
        · rw [← hqlast] at h
          exact PathBasics.path_ne_of_ne_index hql (by omega) hi (by omega) h
      have hne2 : ¬ (∀ z ∈ p, VertexComplete G z X → z = (q[i]'hi) ∨ z = b) := by
        intro hcon
        rcases hcon a (hsub a hamem) hca with h | h
        · rw [← hq0] at h
          exact PathBasics.path_ne_of_ne_index hql hqpos hi (by omega) h
        · rw [← hq0, ← hqlast] at h
          exact PathBasics.path_ne_of_ne_index hql hqpos (by omega) (by omega) h
      have hpar1 := hres1.resolve_right hne1
      have hpar2 := hres2.resolve_right hne2
      -- the `X`-complete edges of `Q` are those of the two halves, disjointly
      have hboth : ∀ u : V, u ∈ q.take (i + 1) → u ∈ q.drop i → u = (q[i]'hi) := by
        intro u h1 h2
        obtain ⟨m, hm, hmlt, hme⟩ := mem_take_iff.mp h1
        obtain ⟨m', hm', hm'ge, hm'e⟩ := mem_drop_iff.mp h2
        have hmm : m = m' := by
          by_contra hne
          exact PathBasics.path_ne_of_ne_index hql hm hm' hne (hme.trans hm'e.symm)
        subst hmm
        have hmi : m = i := by omega
        subst hmi
        exact hme.symm
      have hsplit : (Xed G X q).ncard
          = (Xed G X (q.take (i + 1))).ncard + (Xed G X (q.drop i)).ncard := by
        refine Xed_split (fun z hz => List.take_subset _ _ hz)
          (fun z hz => List.drop_subset _ _ hz) ?_ ?_
        · intro u hu v hv huv
          obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hu
          obtain ⟨m', hm', rfl⟩ := List.getElem_of_mem hv
          have hrel := (PathBasics.path_adj_iff hql hm hm').mp huv
          rcases le_or_gt (max m m') i with h | h
          · exact Or.inl ⟨mem_take_iff.mpr ⟨m, hm, by omega, rfl⟩,
              mem_take_iff.mpr ⟨m', hm', by omega, rfl⟩⟩
          · exact Or.inr ⟨mem_drop_iff.mpr ⟨m, hm, by omega, rfl⟩,
              mem_drop_iff.mpr ⟨m', hm', by omega, rfl⟩⟩
        · intro u hu1 v hv1 hu2 hv2 huv
          rw [hboth u hu1 hu2, hboth v hv1 hv2] at huv
          exact G.irrefl huv
      left
      rw [PathBasics.pathLength_eq] at hpar1 hpar2 ⊢
      rw [hq1len] at hpar1
      rw [hq2len] at hpar2
      omega
    -- PAPER: *"so we may assume not"* — no internal vertex of `Q` is `X`-complete.
    · push Not at hint
      have honly : ∀ u ∈ q, VertexComplete G u X → u = a ∨ u = b := by
        intro u hu hcu
        by_contra hcon
        push Not at hcon
        exact hint u ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hu, hcon.1, hcon.2⟩) hcu
      by_cases hab : G.Adj a b
      -- PAPER: *"If `Q` has length 1 … the theorem holds"*
      · left
        have hne : a ≠ b := G.ne_of_adj hab
        have hlen2 : q.length = 2 := by
          by_contra hcon
          have h3 : 3 ≤ q.length := by
            rcases (by omega : q.length = 1 ∨ 3 ≤ q.length) with h | h
            · exfalso
              refine hne ?_
              rw [← hq0, ← hqlast]
              congr 1
              omega
            · exact h
          refine PathBasics.path_ends_not_adj hql h3 ?_
          have e0 : (q[0]'(by omega)) = a := hq0
          have e1 : (q[q.length - 1]'(by omega)) = b := hqlast
          rw [e0, e1]; exact hab
        obtain ⟨x, y, hxy⟩ := length_eq_two hlen2
        have hxa : x = a := by
          have hh := hq.2.1; rw [hxy] at hh; simpa using hh
        have hyb : y = b := by
          have hh := hq.2.2; rw [hxy] at hh; simpa using hh
        rw [hxa, hyb] at hxy
        have hXedeq : Xed G X q = {s(a, b)} := by
          rw [hxy]
          ext e
          constructor
          · rintro ⟨u, hu, v, hv, rfl, hE⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
            rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
            · exact absurd hE.1 (G.irrefl)
            · rfl
            · exact Sym2.eq_swap
            · exact absurd hE.1 (G.irrefl)
          · intro he
            simp only [Set.mem_singleton_iff] at he
            exact ⟨a, by simp, b, by simp, he, hab, hca, hcb⟩
        rw [hXedeq, Set.ncard_singleton, PathBasics.pathLength_eq, hlen2]
      · have hXedempty : Xed G X q = ∅ := by
          refine Xed_eq_empty ?_
          intro u hu v hv huv hcuv
          have hu' := honly u hu hcuv.1
          have hv' := honly v hv hcuv.2
          rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;> rw [hu', hv'] at huv
          · exact G.irrefl huv
          · exact hab huv
          · exact hab huv.symm
          · exact G.irrefl huv
        rcases Nat.even_or_odd (pathLength q) with hev | hoddq
        · left
          rw [hXedempty, Set.ncard_empty, Nat.even_iff.mp hev]
        -- PAPER: *"We may assume that there is an `X`-complete vertex `v` … of `P` that is
        -- not an end of `Q` … it follows that `v` has no neighbour in `Q*`, contrary to 2.2."*
        · right
          intro z hzp hcz
          by_contra hcon
          push Not at hcon
          have hzq : z ∉ q := by
            intro hz
            rcases honly z hz hcz with h | h
            · exact hcon.1 h
            · exact hcon.2 h
          have hnoedge : ¬ ∃ u ∈ q, ∃ v ∈ q, EdgeComplete G X u v := by
            rintro ⟨u, hu, v, hv, hE⟩
            have hu' := honly u hu hE.2.1
            have hv' := honly v hv hE.2.2
            have huv := hE.1
            rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;> rw [hu', hv'] at huv
            · exact G.irrefl huv
            · exact hab huv
            · exact hab huv.symm
            · exact G.irrefl huv
          obtain ⟨y, hy, hadjy⟩ :=
            thm_2_2 G hG X hX q a b hq
              (fun z hz => hpX z (hsub z hz)) hoddq hca hcb hnoedge z hcz
          exact hnbr z hzp hzq y hy hadjy

private theorem getElem_eq_of_index_eq (l : List V) {c d : ℕ} (hc : c < l.length) (hd : d < l.length)
    (h : c = d) : (l[c]'hc) = (l[d]'hd) := by subst h; rfl

private theorem rotate_take_left (l : List V) {n t : ℕ} (hn : n ≤ l.length) (ht : t + n ≤ l.length) :
    (l.rotate n).take t = (l.drop n).take t := by
  rw [List.rotate_eq_drop_append_take hn,
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

private theorem rotate_take_right (l : List V) {n s : ℕ} (hn : n ≤ l.length) (hs : s ≤ n) :
    (l.rotate n).take (l.length - n + s) = l.drop n ++ l.take s := by
  rw [List.rotate_eq_drop_append_take hn, List.take_append]
  congr 1
  · exact List.take_of_length_le (by simp only [List.length_drop]; omega)
  · rw [show l.length - n + s - (l.drop n).length = s by simp only [List.length_drop]; omega,
      List.take_take, Nat.min_eq_left hs]

/-- A vertex of the path `P` outside a contiguous subpath `Q` has no neighbour in `Q*`. -/
private theorem path_infix_no_outside_nbr {G : SimpleGraph V} {p q : List V}
    (hp : IsPathList G p) (hq : IsPathList G q) (hinf : q <:+: p) :
    ∀ v ∈ p, v ∉ q → ∀ w ∈ SPGT.interior q, ¬ G.Adj v w := by
  obtain ⟨s, t, hst⟩ := hinf
  subst hst
  intro v hv hvq w hw hadj
  obtain ⟨kk, hkk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hq hw
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hv
  have hlenp : (s ++ q ++ t).length = s.length + q.length + t.length := by
    simp only [List.length_append]
  have hsk : s.length + kk < (s ++ q ++ t).length := by omega
  have eqk : (s ++ q ++ t)[s.length + kk]'hsk = (q[kk]'hkk) :=
    getElem_append_mid s q t kk hkk hsk
  rw [← eqk] at hadj
  have hrel := (PathBasics.path_adj_iff hp hm hsk).mp hadj
  obtain ⟨j, hj, hmj⟩ : ∃ (j : ℕ) (_ : j < q.length), m = s.length + j := by
    rcases hrel with h | h
    · exact ⟨kk - 1, by omega, by omega⟩
    · exact ⟨kk + 1, by omega, by omega⟩
  subst hmj
  exact hvq (by rw [getElem_append_mid s q t j hj hm]; exact List.getElem_mem hj)

/-- A vertex of the hole `C` outside an arc `Q` (an initial segment of `C`) has no
neighbour in `Q*`. -/
private theorem hole_prefix_no_outside_nbr {G : SimpleGraph V} {r q : List V}
    (hr : IsHoleList G r) (hq : IsPathList G q) (hpre : q <+: r) :
    ∀ v ∈ r, v ∉ q → ∀ w ∈ SPGT.interior q, ¬ G.Adj v w := by
  intro v hv hvq w hw hadj
  obtain ⟨kk, hkk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hq hw
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hv
  have hql : q.length ≤ r.length := hpre.length_le
  have hkr : kk < r.length := by omega
  have eqk : (q[kk]'hkk) = (r[kk]'hkr) := hpre.getElem hkk
  rw [eqk] at hadj
  have hres := hole_adj_index hr hm hkr hadj
  have h4 : 4 ≤ r.length := hr.1
  have hmq : m < q.length := by omega
  have heq : (q[m]'hmq) = (r[m]'hm) := hpre.getElem hmq
  refine hvq ?_
  rw [← heq]
  exact List.getElem_mem hmq

/-- **2.3, second assertion** — *"The second assertion follows from the first."*  Two
`X`-complete vertices of the hole cut it into two arcs, each a subpath of `P`. -/
private theorem part2 {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    {p : List V} (hphole : IsHoleList G p)
    (hfirst : ∀ (q : List V) (a b : V), (∃ k : ℕ, q <+: p.rotate k) → IsPathFrom G q a b →
        VertexComplete G a X → VertexComplete G b X →
        ((Xed G X q).ncard % 2 = pathLength q % 2 ∨
          ∀ w ∈ p, VertexComplete G w X → w = a ∨ w = b)) :
    (Even (Xed G X p).ncard ∨
      ∃ a b : V, {w : V | w ∈ p ∧ VertexComplete G w X} = {a, b} ∧ a ≠ b ∧ G.Adj a b) := by
  have hL : 4 ≤ p.length := hphole.1
  have hnd : p.Nodup := hphole.2.1
  by_cases hna : ∃ (ia : ℕ) (hia : ia < p.length) (ib : ℕ) (hib : ib < p.length), ia < ib ∧
      VertexComplete G (p[ia]'hia) X ∧ VertexComplete G (p[ib]'hib) X ∧
      ¬ G.Adj (p[ia]'hia) (p[ib]'hib)
  · obtain ⟨ia, hia, ib, hib, hlt, hca, hcb, hnab⟩ := hna
    left
    have hnotsucc : ib ≠ ia + 1 := by
      rintro rfl
      exact hnab (HoleBasics.hole_adj_succ hphole hib)
    have hnotwrap : ¬ (ia = 0 ∧ ib = p.length - 1) := by
      rintro ⟨rfl, rfl⟩
      exact hnab (HoleBasics.hole_adj_wrap hphole).symm
    have h2 : ia + 2 ≤ ib := by omega
    have h4 : ib - ia + 2 ≤ p.length := by omega
    -- if the two ends are the only `X`-complete vertices there is no `X`-complete edge
    have hXfromOnly : (∀ w ∈ p, VertexComplete G w X → w = (p[ia]'hia) ∨ w = (p[ib]'hib)) →
        Xed G X p = ∅ := by
      intro honly
      refine Xed_eq_empty ?_
      intro u hu v hv huv hcuv
      have hu' := honly u hu hcuv.1
      have hv' := honly v hv hcuv.2
      rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;> rw [hu', hv'] at huv
      · exact G.irrefl huv
      · exact hnab huv
      · exact hnab huv.symm
      · exact G.irrefl huv
    -- the two arcs
    have hA1path : IsPathList G ((p.drop ia).take (ib - ia + 1)) := by
      rw [← rotate_take_left p (by omega) (by omega)]
      exact isPathList_hole_take (HoleBasics.isHoleList_rotate hphole ia) (by omega)
        (by rw [List.length_rotate]; omega)
    have hA2path : IsPathList G (p.drop ib ++ p.take (ia + 1)) := by
      rw [← rotate_take_right p (by omega) (by omega)]
      exact isPathList_hole_take (HoleBasics.isHoleList_rotate hphole ib) (by omega)
        (by rw [List.length_rotate]; omega)
    have hA1from : IsPathFrom G ((p.drop ia).take (ib - ia + 1)) (p[ia]'hia) (p[ib]'hib) :=
      ⟨hA1path, PathBasics.head?_slice p (by omega) hib, PathBasics.getLast?_slice p (by omega) hib⟩
    have hA2from : IsPathFrom G (p.drop ib ++ p.take (ia + 1)) (p[ib]'hib) (p[ia]'hia) := by
      refine ⟨hA2path, ?_, ?_⟩
      · rw [List.head?_append, List.head?_drop, List.getElem?_eq_getElem hib]
        rfl
      · have hnenil : p.take (ia + 1) ≠ [] := by
          intro hc
          have hz : (p.take (ia + 1)).length = 0 := by rw [hc]; rfl
          simp only [List.length_take] at hz; omega
        rw [List.getLast?_append_of_ne_nil _ hnenil,
          getLast?_take (by omega) (by omega)]
        exact congrArg _ (getElem_eq_of_index_eq p (by omega) hia (by omega))
    have hpre1 : (p.drop ia).take (ib - ia + 1) <+: p.rotate ia := by
      rw [← rotate_take_left p (by omega) (by omega)]
      exact List.take_prefix _ _
    have hpre2 : p.drop ib ++ p.take (ia + 1) <+: p.rotate ib := by
      rw [← rotate_take_right p (by omega) (by omega)]
      exact List.take_prefix _ _
    -- membership in the two arcs, by index
    have hmemA1 : ∀ (c : ℕ) (hc : c < p.length), ia ≤ c → c ≤ ib →
        (p[c]'hc) ∈ (p.drop ia).take (ib - ia + 1) := by
      intro c hc h1 h2'
      exact (PathBasics.mem_slice_iff p (by omega) hib).mpr ⟨c, hc, h1, h2', rfl⟩
    have hmemA2 : ∀ (c : ℕ) (hc : c < p.length), (ib ≤ c ∨ c ≤ ia) →
        (p[c]'hc) ∈ p.drop ib ++ p.take (ia + 1) := by
      intro c hc h
      rcases h with h | h
      · exact List.mem_append_left _ (mem_drop_iff.mpr ⟨c, hc, h, rfl⟩)
      · exact List.mem_append_right _ (mem_take_iff.mpr ⟨c, hc, by omega, rfl⟩)
    have hkey1 : ∀ z, z ∈ (p.drop ia).take (ib - ia + 1) → z ∈ p.drop ib ++ p.take (ia + 1) →
        z = (p[ia]'hia) ∨ z = (p[ib]'hib) := by
      intro z hz1 hz2
      obtain ⟨c, hc, hc1, hc2, hce⟩ := (PathBasics.mem_slice_iff p (by omega) hib).mp hz1
      rcases List.mem_append.mp hz2 with h | h
      · obtain ⟨c', hc', hc'1, hc'e⟩ := mem_drop_iff.mp h
        have hcc : c = c' := by
          by_contra hne
          exact HoleBasics.hole_ne_of_ne_index hphole hc hc' hne (hce.trans hc'e.symm)
        right
        rw [← hce]
        exact getElem_eq_of_index_eq p hc hib (by omega)
      · obtain ⟨c', hc', hc'1, hc'e⟩ := mem_take_iff.mp h
        have hcc : c = c' := by
          by_contra hne
          exact HoleBasics.hole_ne_of_ne_index hphole hc hc' hne (hce.trans hc'e.symm)
        left
        rw [← hce]
        exact getElem_eq_of_index_eq p hc hia (by omega)
    have hsplit : (Xed G X p).ncard
        = (Xed G X ((p.drop ia).take (ib - ia + 1))).ncard
          + (Xed G X (p.drop ib ++ p.take (ia + 1))).ncard := by
      refine Xed_split (fun z hz => List.drop_subset _ _ (List.take_subset _ _ hz)) ?_ ?_ ?_
      · intro z hz
        rcases List.mem_append.mp hz with h | h
        · exact List.drop_subset _ _ h
        · exact List.take_subset _ _ h
      · intro u hu v hv huv
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hu
        obtain ⟨m', hm', rfl⟩ := List.getElem_of_mem hv
        have hrel := hole_adj_index hphole hm hm' huv
        by_cases hin : ia ≤ min m m' ∧ max m m' ≤ ib
        · exact Or.inl ⟨hmemA1 m hm (by omega) (by omega), hmemA1 m' hm' (by omega) (by omega)⟩
        · exact Or.inr ⟨hmemA2 m hm (by omega), hmemA2 m' hm' (by omega)⟩
      · intro u hu1 v hv1 hu2 hv2 huv
        rcases hkey1 u hu1 hu2 with h | h <;> rcases hkey1 v hv1 hv2 with h' | h' <;>
          rw [h, h'] at huv
        · exact G.irrefl huv
        · exact hnab huv
        · exact hnab huv.symm
        · exact G.irrefl huv
    have hres1 := hfirst _ _ _ ⟨ia, hpre1⟩ hA1from hca hcb
    have hres2 := hfirst _ _ _ ⟨ib, hpre2⟩ hA2from hcb hca
    rcases hres1 with hp1 | honly
    · rcases hres2 with hp2 | honly
      · have hlen1 : ((p.drop ia).take (ib - ia + 1)).length = ib - ia + 1 :=
          PathBasics.length_slice p (by omega) hib
        have hlen2 : (p.drop ib ++ p.take (ia + 1)).length = (p.length - ib) + (ia + 1) := by
          simp only [List.length_append, List.length_drop, List.length_take]; omega
        rw [PathBasics.pathLength_eq, hlen1] at hp1
        rw [PathBasics.pathLength_eq, hlen2] at hp2
        have hev : Even (holeLength p) := hG.1 p hphole
        rw [Nat.even_iff]
        have hevl : p.length % 2 = 0 := by
          have : holeLength p = p.length := rfl
          rw [Nat.even_iff, this] at hev; exact hev
        omega
      · rw [hXfromOnly (fun w hw hcw => (honly w hw hcw).symm), Set.ncard_empty]
        exact ⟨0, rfl⟩
    · rw [hXfromOnly honly, Set.ncard_empty]
      exact ⟨0, rfl⟩
  · push Not at hna
    by_cases h2 : ∃ (ia : ℕ) (hia : ia < p.length) (ib : ℕ) (hib : ib < p.length), ia < ib ∧
        VertexComplete G (p[ia]'hia) X ∧ VertexComplete G (p[ib]'hib) X
    · obtain ⟨ia, hia, ib, hib, hlt, hca, hcb⟩ := h2
      right
      refine ⟨p[ia]'hia, p[ib]'hib, ?_, HoleBasics.hole_ne_of_ne_index hphole hia hib (by omega),
        hna ia hia ib hib hlt hca hcb⟩
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hwp, hcw⟩
        by_contra hcon
        push Not at hcon
        obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hwp
        have hcia : c ≠ ia := by
          intro h; exact hcon.1 (getElem_eq_of_index_eq p hc hia h)
        have hcib : c ≠ ib := by
          intro h; exact hcon.2 (getElem_eq_of_index_eq p hc hib h)
        have hadj1 : G.Adj (p[ia]'hia) (p[ib]'hib) := hna ia hia ib hib hlt hca hcb
        have hadj2 : G.Adj (p[ia]'hia) (p[c]'hc) ∨ G.Adj (p[c]'hc) (p[ia]'hia) := by
          rcases lt_or_gt_of_ne hcia with h | h
          · exact Or.inr (hna c hc ia hia h hcw hca)
          · exact Or.inl (hna ia hia c hc h hca hcw)
        have hadj3 : G.Adj (p[ib]'hib) (p[c]'hc) ∨ G.Adj (p[c]'hc) (p[ib]'hib) := by
          rcases lt_or_gt_of_ne hcib with h | h
          · exact Or.inr (hna c hc ib hib h hcw hcb)
          · exact Or.inl (hna ib hib c hc h hcb hcw)
        refine hole_no_triangle hphole (List.getElem_mem hia) (List.getElem_mem hib)
          (List.getElem_mem hc) hadj1 ?_ ?_
        · rcases hadj2 with h | h
          · exact h
          · exact h.symm
        · rcases hadj3 with h | h
          · exact h
          · exact h.symm
      · rintro (rfl | rfl)
        · exact ⟨List.getElem_mem hia, hca⟩
        · exact ⟨List.getElem_mem hib, hcb⟩
    · push Not at h2
      left
      have : Xed G X p = ∅ := by
        refine Xed_eq_empty ?_
        intro u hu v hv huv hcuv
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hu
        obtain ⟨m', hm', rfl⟩ := List.getElem_of_mem hv
        have hmm : m ≠ m' := by rintro rfl; exact G.irrefl huv
        rcases lt_or_gt_of_ne hmm with h | h
        · exact h2 m hm m' hm' h hcuv.1 hcuv.2
        · exact h2 m' hm' m hm h hcuv.2 hcuv.1
      rw [this, Set.ncard_empty]
      exact ⟨0, rfl⟩


end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.3** (printed p. 9)

PAPER: *"Let `G` be Berge, let `X ⊆ V(G)` be anticonnected, and let `P` be a path
or hole in `G \ X`.  Let `Q` be a subpath of `P` (and hence of `G`) with both ends
`X`-complete.  Then either the number of `X`-complete edges in `Q` has the same
parity as the length of `Q`, or the ends of `Q` are the only `X`-complete vertices
in `P`.  In particular, if `P` is a hole, then either there are an even number of
`X`-complete edges in `P`, or there are exactly two `X`-complete vertices and they
are adjacent."*

The printed proof, step for step:

* *"The second assertion follows from the first."* — `part2` above.
* *"For the first, we use induction on the length of `Q`."* — `key` above.
* *"If some internal vertex of `Q` is `X`-complete then the result follows from the
  inductive hypothesis"* — the first branch of `key`: cut `Q` at that vertex and add
  the two halves (`Xed_split`).
* *"If `Q` has length 1 or even then the theorem holds"* — the `G.Adj a b` branch
  (`Q` has length `1`, one `X`-complete edge) and the even branch (no `X`-complete
  edge at all).
* *"We may assume that there is an `X`-complete vertex `v` say of `P` that is not an
  end of `Q`, and therefore does not belong to `Q`; and since `P` is a path or hole,
  it follows that `v` has no neighbour in `Q*`, contrary to 2.2."* — the last branch,
  via `path_infix_no_outside_nbr` / `hole_prefix_no_outside_nbr` and `thm_2_2`. -/
theorem thm_2_3 (G : SimpleGraph V) (hG : Berge G) (X : Set V)
    (hX : AnticonnectedSet G X) (p : List V)
    (hp : IsPathList G p ∨ IsHoleList G p) (hpX : ∀ w ∈ p, w ∉ X) :
    (∀ (q : List V) (a b : V),
        ((IsPathList G p ∧ q <:+: p) ∨ (IsHoleList G p ∧ ∃ k : ℕ, q <+: p.rotate k)) →
        IsPathFrom G q a b →
        VertexComplete G a X → VertexComplete G b X →
        ({e : Sym2 V | ∃ u ∈ q, ∃ v ∈ q, e = s(u, v) ∧ EdgeComplete G X u v}.ncard % 2
              = pathLength q % 2 ∨
          ∀ w ∈ p, VertexComplete G w X → w = a ∨ w = b)) ∧
    (IsHoleList G p →
      (Even {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G X u v}.ncard ∨
        ∃ a b : V, {w : V | w ∈ p ∧ VertexComplete G w X} = {a, b} ∧ a ≠ b ∧ G.Adj a b)) := by
  have hfirst : ∀ (q : List V) (a b : V),
      ((IsPathList G p ∧ q <:+: p) ∨ (IsHoleList G p ∧ ∃ k : ℕ, q <+: p.rotate k)) →
      IsPathFrom G q a b → VertexComplete G a X → VertexComplete G b X →
      ((Xed G X q).ncard % 2 = pathLength q % 2 ∨
        ∀ w ∈ p, VertexComplete G w X → w = a ∨ w = b) := by
    intro q a b hsubq hqfrom hca hcb
    rcases hsubq with ⟨hppath, hinf⟩ | ⟨hphole, k, hpre⟩
    · exact key hG hX hpX q.length q a b le_rfl (fun w hw => hinf.subset hw)
        (path_infix_no_outside_nbr hppath hqfrom.1 hinf) hqfrom hca hcb
    · refine key hG hX hpX q.length q a b le_rfl (fun w hw => ?_) (fun v hv hvq w hw => ?_)
        hqfrom hca hcb
      · exact HoleBasics.mem_rotate_iff.mp (hpre.subset hw)
      · exact hole_prefix_no_outside_nbr (HoleBasics.isHoleList_rotate hphole k) hqfrom.1 hpre
          v (HoleBasics.mem_rotate_iff.mpr hv) hvq w hw
  refine ⟨hfirst, ?_⟩
  intro hphole
  exact part2 hG hphole (fun q a b hpre hqfrom hca hcb =>
    hfirst q a b (Or.inr ⟨hphole, hpre⟩) hqfrom hca hcb)


end SPGT

end Workspace.Statements.S02
