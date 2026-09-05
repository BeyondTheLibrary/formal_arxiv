import Workspace.ProofLemmas.Thm192Claim6Basics
import Workspace.ProofLemmas.Thm134RegionAux
import Workspace.ProofLemmas.WheelBasics
import Workspace.Statements.S02.Thm_2_3

/-!
# Small helpers for the parity gaps of claim (7) of 19.2

Nothing here is specific to 19.2: these are list/path/parity utilities that the two
parity arguments of claim (7) need and that the project did not yet have.

* `isPathFrom_cons` / `isPathFrom_snoc` attach one vertex to an end of a path.  The
  paper uses this whenever it writes a path such as `y₁-x₂-pᵢ-⋯-pₙ-y₂`.
* `isPathFrom_drop` is the tail `pᵢ-⋯-pₙ-x₁` of a path.
* `exists_cycEdge_of_cycCount_lt` turns a strict increase of the running count of
  `Y`-complete edges of a hole into an actual `Y`-complete edge in the range.
* `even_cycCount_of_three_complete` is `WheelBasics.even_cycCount_of_wheel` with the
  wheel replaced by the weaker input that 2.3 really needs: three distinct
  `Y`-complete vertices on the rim.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm192Claim7Aux

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Attach a vertex `s` at the front of a path `p` from `u` to `v`, when `s` is
adjacent to `u` and to no other vertex of `p`. -/
theorem isPathFrom_cons {G : SimpleGraph V} {p : List V} {u v s : V}
    (hp : IsPathFrom G p u v) (hsu : G.Adj s u) (hs : s ∉ p)
    (hsint : ∀ w ∈ p, w ≠ u → ¬ G.Adj s w) :
    IsPathFrom G (s :: p) s v := by
  obtain ⟨hpl, hhd, hlst⟩ := hp
  have hpos : 0 < p.length := PathBasics.path_length_pos hpl
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hhd hpos
  refine ⟨⟨by simp, List.nodup_cons.mpr ⟨hs, hpl.2.1⟩, ?_⟩, by simp, ?_⟩
  · intro i j hi hj
    simp only [List.length_cons] at hi hj
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hj0 : j = 0
      · subst hj0
        simp only [List.getElem_cons_zero]
        exact iff_of_false G.irrefl (by omega)
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hjp : j' < p.length := by omega
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        by_cases hj1 : j' = 0
        · subst hj1
          rw [h0]
          exact iff_of_true hsu (Or.inl rfl)
        · refine iff_of_false ?_ (by omega)
          exact hsint _ (List.getElem_mem hjp)
            (fun he => hj1 (hpl.2.1.getElem_inj_iff.mp (he.trans h0.symm)))
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hip : i' < p.length := by omega
      by_cases hj0 : j = 0
      · subst hj0
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        by_cases hi1 : i' = 0
        · subst hi1
          rw [h0]
          exact iff_of_true hsu.symm (Or.inr rfl)
        · refine iff_of_false ?_ (by omega)
          intro hadj
          exact hsint _ (List.getElem_mem hip)
            (fun he => hi1 (hpl.2.1.getElem_inj_iff.mp (he.trans h0.symm))) hadj.symm
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hjp : j' < p.length := by omega
        simp only [List.getElem_cons_succ]
        rw [PathBasics.path_adj_iff hpl hip hjp]
        omega
  · rw [List.getLast?_cons_of_ne_nil (PathBasics.path_ne_nil hpl)]
    exact hlst

/-- Attach a vertex `t` at the end of a path `p` from `u` to `v`, when `t` is
adjacent to `v` and to no other vertex of `p`. -/
theorem isPathFrom_snoc {G : SimpleGraph V} {p : List V} {u v t : V}
    (hp : IsPathFrom G p u v) (htv : G.Adj t v) (ht : t ∉ p)
    (htint : ∀ w ∈ p, w ≠ v → ¬ G.Adj t w) :
    IsPathFrom G (p ++ [t]) u t := by
  have hr := PathBasics.isPathFrom_reverse hp
  have h := isPathFrom_cons hr htv (by simpa using ht)
    (fun w hw hwv => htint w (List.mem_reverse.mp hw) hwv)
  simpa using PathBasics.isPathFrom_reverse h

/-- The tail `pᵢ-⋯-pₙ` of a path. -/
theorem isPathFrom_drop {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    {i : ℕ} (hi : i + 1 < P.length) :
    IsPathFrom G (P.drop i) (P[i]'(by omega)) (P[P.length - 1]'(by omega)) := by
  have hsl := PathBasics.isPathFrom_slice hP (i := i) (j := P.length - 1) (by omega) (by omega)
  have he : (P.drop i).take (P.length - 1 - i + 1) = P.drop i := by
    refine List.take_of_length_le ?_
    simp only [List.length_drop]
    omega
  rwa [he] at hsl

/-- Every vertex of `P.drop i` is `P[k]` for some `k ≥ i`. -/
theorem mem_drop_index {P : List V} {i : ℕ} {w : V} (hw : w ∈ P.drop i) :
    ∃ k, ∃ hk : k < P.length, i ≤ k ∧ (P[k]'hk) = w := by
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
  have hik : i + k < P.length := by
    simp only [List.length_drop] at hk; omega
  exact ⟨i + k, hik, by omega, by simpa only [List.getElem_drop] using hkw⟩

/-- A pair of nonadjacent vertices is anticonnected. -/
theorem anticonnected_pair {G : SimpleGraph V} {u v : V} (hne : u ≠ v) (huv : ¬ G.Adj u v) :
    AnticonnectedSet G ({u, v} : Set V) := by
  have he : ({u, v} : Set V) = {v} ∪ {u} := by rw [Set.union_singleton]
  rw [AnticonnectedSet, he]
  exact ConnectedSetUnionAttach.connectedSet_union_singleton
    (Thm134RegionAux.connectedSet_singleton Gᶜ v) ⟨v, rfl, ⟨hne, huv⟩⟩

/-- Two equal indices give the same entry. -/
theorem getElem_idx_congr {l : List V} {a b : ℕ} (h : a = b)
    (ha : a < l.length) (hb : b < l.length) : l[a]'ha = l[b]'hb := by
  subst h; rfl

/-- The head of a rotation, in `getElem?` form. -/
theorem head?_rotate {H : List V} (hn : 0 < H.length) (k : ℕ) :
    (H.rotate k).head? = H[k % H.length]? := by
  rw [List.head?_eq_getElem?, List.getElem?_rotate hn, Nat.zero_add]

/-- The last entry of a rotation, in `getElem?` form. -/
theorem getLast?_rotate {H : List V} (hn : 0 < H.length) (k : ℕ) :
    (H.rotate k).getLast? = H[(H.length - 1 + k) % H.length]? := by
  rw [List.getLast?_eq_getElem?, List.length_rotate,
    List.getElem?_rotate (show H.length - 1 < H.length by omega)]

/-- A rotation of a duplicate-free list is determined by its first entry. -/
theorem rotate_index {H : List V} (hnd : H.Nodup) {k j : ℕ} (hj : j < H.length)
    (hhead : (H.rotate k).head? = some (H[j]'hj)) : H.rotate k = H.rotate j := by
  have hn : 0 < H.length := by omega
  rw [head?_rotate hn, List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hhead
  have he := hnd.getElem_inj_iff.mp (Option.some.inj hhead)
  rw [← List.rotate_mod H k, he]

/-- A strict increase of the running count of `Y`-complete rim edges exhibits one. -/
theorem exists_cycEdge_of_cycCount_lt {G : SimpleGraph V} {Y : Set V} {C : List V}
    {a b : ℕ} (h : WheelParity.cycCount G Y C a < WheelParity.cycCount G Y C b) :
    ∃ m, a ≤ m ∧ m < b ∧ WheelParity.CycEdge G Y C m := by
  classical
  by_contra hcon
  push_neg at hcon
  have hab : a < b := by
    by_contra hba
    have hm := WheelParity.cycCount_mono (G := G) (Y := Y) (C := C) (show b ≤ a by omega)
    omega
  have key : ∀ d : ℕ, a + d ≤ b →
      WheelParity.cycCount G Y C (a + d) = WheelParity.cycCount G Y C a := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ n ih =>
        intro hle
        rw [show a + (n + 1) = (a + n) + 1 by omega, WheelParity.cycCount_succ,
          ih (by omega), if_neg (hcon (a + n) (by omega) (by omega))]
        omega
  have := key (b - a) (by omega)
  rw [show a + (b - a) = b by omega] at this
  omega

/-- A vertex of an anticonnected set with at least two elements has a nonneighbour in
the set: otherwise it would be isolated in the complement, which is connected. -/
theorem exists_nonneighbour_of_anticonnected {G : SimpleGraph V} {Y : Set V}
    (hY : AnticonnectedSet G Y) {y : V} (hyY : y ∈ Y) (hne : (Y \ {y}).Nonempty) :
    ¬ VertexComplete G y (Y \ {y}) := by
  obtain ⟨w, hwY, hwy⟩ := hne
  obtain ⟨p⟩ := hY ⟨y, hyY⟩ ⟨w, hwY⟩
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne (by
    intro he
    exact hwy (congrArg Subtype.val he).symm)
  have hadj' : Gᶜ.Adj y ((p.snd : ↥Y) : V) := p.adj_snd hnil
  intro hc
  have h2 : ((p.snd : ↥Y) : V) ∈ Y \ {y} := by
    refine ⟨(p.snd : ↥Y).2, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    exact Gᶜ.irrefl (he ▸ hadj')
  exact ((SimpleGraph.compl_adj G _ _).mp hadj').2 (hc _ h2)

/-- The last vertex of an initial stretch. -/
theorem getLast?_take {l : List V} {k : ℕ} (h1 : 0 < k) (h2 : k ≤ l.length) :
    (l.take k).getLast? = l[k - 1]? := by
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left h2,
    List.getElem?_take, if_pos (by omega)]

/-- For a path, the *set of `Y`-complete edges* and the *set of positions carrying a
`Y`-complete edge* have the same size: the map `i ↦ {Qᵢ, Qᵢ₊₁}` is a bijection between
them.  This is the path analogue of `WheelParity.ncard_yEdges_eq_cycCount`, and it is what
lets 18.2 (which counts edges) feed the rim bookkeeping of §16 (which counts positions). -/
theorem ncard_pathEdges {G : SimpleGraph V} {Y : Set V} {Q : List V} (hQ : IsPathList G Q) :
    {e : Sym2 V | ∃ u ∈ Q, ∃ v ∈ Q, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard
      = {i : ℕ | ∃ h : i + 1 < Q.length,
          EdgeComplete G Y (Q[i]'(by omega)) (Q[i + 1]'h)}.ncard := by
  classical
  obtain ⟨u₀, hu₀⟩ : ∃ u : V, u ∈ Q := ⟨Q.head hQ.1, List.head_mem _⟩
  have hgetD : ∀ (m : ℕ) (hm : m < Q.length), Q.getD m u₀ = Q[m]'hm :=
    fun m hm => List.getD_eq_getElem Q u₀ hm
  have himg : {e : Sym2 V | ∃ u ∈ Q, ∃ v ∈ Q, e = s(u, v) ∧ EdgeComplete G Y u v}
      = (fun m => s(Q.getD m u₀, Q.getD (m + 1) u₀)) ''
        {i : ℕ | ∃ h : i + 1 < Q.length,
          EdgeComplete G Y (Q[i]'(by omega)) (Q[i + 1]'h)} := by
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hE⟩
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hv
      rcases (PathBasics.path_adj_iff hQ ha hb).mp hE.1 with h | h
      · subst h
        refine ⟨a, ⟨hb, hE⟩, ?_⟩
        show s(Q.getD a u₀, Q.getD (a + 1) u₀) = _
        rw [hgetD a (by omega), hgetD (a + 1) hb]
      · subst h
        refine ⟨b, ⟨ha, WheelParity.edgeComplete_symm hE⟩, ?_⟩
        show s(Q.getD b u₀, Q.getD (b + 1) u₀) = _
        rw [hgetD b (by omega), hgetD (b + 1) ha, Sym2.eq_swap]
    · rintro ⟨m, ⟨hm, hE⟩, rfl⟩
      refine ⟨_, List.getElem_mem (show m < Q.length by omega), _, List.getElem_mem hm, ?_, hE⟩
      show s(Q.getD m u₀, Q.getD (m + 1) u₀) = _
      rw [hgetD m (by omega), hgetD (m + 1) hm]
  have hinj : Set.InjOn (fun m => s(Q.getD m u₀, Q.getD (m + 1) u₀))
      {i : ℕ | ∃ h : i + 1 < Q.length,
        EdgeComplete G Y (Q[i]'(by omega)) (Q[i + 1]'h)} := by
    rintro a ⟨ha, -⟩ b ⟨hb, -⟩ hab
    have hab' : s(Q[a]'(show a < Q.length by omega), Q[a + 1]'ha)
        = s(Q[b]'(show b < Q.length by omega), Q[b + 1]'hb) := by
      rw [← hgetD a (by omega), ← hgetD (a + 1) ha, ← hgetD b (by omega), ← hgetD (b + 1) hb]
      exact hab
    rcases Sym2.eq_iff.mp hab' with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hQ.2.1.getElem_inj_iff.mp h1
    · have i1 := hQ.2.1.getElem_inj_iff.mp h1
      have i2 := hQ.2.1.getElem_inj_iff.mp h2
      omega
  rw [himg, Set.ncard_image_of_injOn hinj]

/-- 2.3, in the form the parity arguments of §19 use it: a hole carrying three
distinct `Y`-complete vertices has an even number of `Y`-complete edges. -/
theorem even_cycCount_of_three_complete {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hY : AnticonnectedSet G Y) (hC : IsHoleList G C)
    (hCY : ∀ w ∈ C, w ∉ Y) {a b c : V} (haC : a ∈ C) (hbC : b ∈ C) (hcC : c ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hca : VertexComplete G a Y) (hcb : VertexComplete G b Y)
    (hcc : VertexComplete G c Y) :
    Even (WheelParity.cycCount G Y C C.length) := by
  rw [← WheelParity.ncard_yEdges_eq_cycCount hC]
  rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hY C (Or.inr hC) hCY).2 hC
    with h | ⟨u, v, hset, huv, -⟩
  · exact h
  · exfalso
    have hmem : ∀ w : V, w ∈ C → VertexComplete G w Y → w = u ∨ w = v := by
      intro w hwC hwY
      have hw' : w ∈ ({u, v} : Set V) := by rw [← hset]; exact ⟨hwC, hwY⟩
      simpa using hw'
    have hsub : ({a, b, c} : Set V) ⊆ ({u, v} : Set V) := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      rcases hw with rfl | rfl | rfl
      · exact hmem _ haC hca
      · exact hmem _ hbC hcb
      · exact hmem _ hcC hcc
    have h3 : ({a, b, c} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab, hac]) (Set.toFinite _),
        Set.ncard_pair hbc]
    have h2 : ({u, v} : Set V).ncard = 2 := Set.ncard_pair huv
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega

end Workspace.ProofLemmas.Thm192Claim7Aux
