import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks

/-!
# A cycle of length `≥ 4` through a prescribed edge of a 3-connected graph

This is the first sentence of the printed proof of 8.1 (printed p. 40):

PAPER: *"Since `J` is 3-connected, there is a cycle `C` of `J` with `|V(C)| ≥ 4` and with
`uv ∈ E(C)`."*

A *cycle* of `J` is encoded exactly as in the seventh axiom of a `J`-strip system
(`Workspace.Types.StripSystems`): the list `c` of its vertices in cyclic order, with `c.Nodup`,
`3 ≤ c.length`, and every cyclically consecutive pair — i.e. every pair in `c.zip (c.rotate 1)` —
adjacent in `J`.  Here the cycle is presented in the normalized form `u :: v :: w`, which
records both `|V(C)| ≥ 4` (as `2 ≤ w.length`) and `uv ∈ E(C)` (as the first cyclically
consecutive pair).

The argument the authors leave implicit: `J` minus the two vertices `u,v` is connected (delete
fewer than three vertices from a 3-connected graph), `v` has a neighbour `x ∉ {u}`, and `u` has
a neighbour `w ∉ {v,x}`; a path from `x` to `w` inside `J \ {u,v}` closes up with the edges
`vx`, `wu` and `uv` into a cycle with at least four vertices.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm81Cycle

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

/-- The cyclically consecutive pairs of `a :: M ++ [b]`, read off a chain. -/
private theorem zip_adj_of_isChain {α : Type*} {r : α → α → Prop} :
    ∀ (M : List α) (a b : α), List.IsChain r (a :: M ++ [b]) →
      ∀ p ∈ (a :: M).zip (M ++ [b]), r p.1 p.2 := by
  intro M
  induction M with
  | nil =>
      intro a b h p hp
      simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      subst hp
      exact (List.isChain_cons_cons.mp h).1
  | cons m M ih =>
      intro a b h p hp
      rw [List.cons_append, List.zip_cons_cons, List.mem_cons] at hp
      have h' := List.isChain_cons_cons.mp h
      rcases hp with rfl | hp
      · exact h'.1
      · exact ih m b h'.2 p hp

/-- In a 3-connected graph, deleting fewer than three vertices leaves a connected graph; so a
vertex outside the deleted set `T` has a neighbour outside `T`. -/
private theorem exists_adj_outside {U : Type*} [Fintype U] {J : SimpleGraph U}
    (hJ : IsKConnected J 3) {T : Set U} (hT : T.ncard < 3) {a : U} (ha : a ∉ T) :
    ∃ z, J.Adj a z ∧ z ∉ T := by
  classical
  obtain ⟨hcard, hconn⟩ := hJ
  have hb : ∃ b, b ∉ T ∧ b ≠ a := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Set.univ : Set U) ⊆ insert a T := by
      intro z _
      rcases Classical.em (z ∈ T) with hz | hz
      · exact Set.mem_insert_of_mem _ hz
      · exact (hcon z hz) ▸ Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (insert a T).ncard ≤ T.ncard + 1 := Set.ncard_insert_le a T
    rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
    omega
  obtain ⟨b, hbT, hba⟩ := hb
  have hconnT := hconn T hT
  have hreach : (J.induce Tᶜ).Reachable ⟨a, ha⟩ ⟨b, hbT⟩ := hconnT.preconnected _ _
  obtain ⟨p⟩ := hreach
  have hne : (⟨a, ha⟩ : ↥(Tᶜ : Set U)) ≠ ⟨b, hbT⟩ := by
    intro h
    exact hba (congrArg Subtype.val h).symm
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  refine ⟨(p.snd : U), p.adj_snd hnil, ?_⟩
  exact (p.snd).2

/-- *"Since `J` is 3-connected, there is a cycle `C` of `J` with `|V(C)| ≥ 4` and with
`uv ∈ E(C)`."* -/
theorem exists_cycle_through_edge {U : Type*} [Fintype U]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) {u v : U} (huv : J.Adj u v) :
    ∃ w : List U, 2 ≤ w.length ∧ (u :: v :: w).Nodup ∧
      ∀ p ∈ (u :: v :: w).zip ((u :: v :: w).rotate 1), J.Adj p.1 p.2 := by
  classical
  obtain ⟨hcard, hconn⟩ := hJ
  have hJ' : IsKConnected J 3 := ⟨hcard, hconn⟩
  have huvne : u ≠ v := huv.ne
  -- `v` has a neighbour `x ≠ u`
  obtain ⟨x, hvx, hxu⟩ :=
    exists_adj_outside hJ' (T := ({u} : Set U)) (by simp) (a := v)
      (by simpa using huvne.symm)
  have hxu' : x ≠ u := by simpa using hxu
  have hxv : x ≠ v := hvx.ne'
  -- `u` has a neighbour `w₀ ∉ {v, x}`
  have hTcard : ({v, x} : Set U).ncard < 3 := by
    have h1 : ({v, x} : Set U).ncard ≤ ({x} : Set U).ncard + 1 := Set.ncard_insert_le v {x}
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨w₀, huw, hw₀⟩ :=
    exists_adj_outside hJ' (T := ({v, x} : Set U)) hTcard (a := u)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨huvne, fun h => hxu' h.symm⟩)
  have hw₀v : w₀ ≠ v := by
    intro h; exact hw₀ (by simp [h])
  have hw₀x : w₀ ≠ x := by
    intro h; exact hw₀ (by simp [h])
  have hw₀u : w₀ ≠ u := huw.ne'
  -- a path from `x` to `w₀` avoiding `u` and `v`
  have hTc : ({u, v} : Set U).ncard < 3 := by
    have h1 : ({u, v} : Set U).ncard ≤ ({v} : Set U).ncard + 1 := Set.ncard_insert_le u {v}
    rw [Set.ncard_singleton] at h1
    omega
  have hxT : x ∉ ({u, v} : Set U) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; push_neg; exact ⟨hxu', hxv⟩
  have hwT : w₀ ∉ ({u, v} : Set U) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; push_neg
    exact ⟨hw₀u, hw₀v⟩
  have hconnT := hconn ({u, v} : Set U) hTc
  have hreach : (J.induce ({u, v} : Set U)ᶜ).Reachable ⟨x, hxT⟩ ⟨w₀, hwT⟩ :=
    hconnT.preconnected _ _
  obtain ⟨p0⟩ := hreach
  set Q := p0.toPath.1 with hQ
  have hQpath : Q.IsPath := p0.toPath.2
  have hQne : (⟨x, hxT⟩ : ↥((({u, v} : Set U))ᶜ)) ≠ ⟨w₀, hwT⟩ := by
    intro h
    exact hw₀x (congrArg Subtype.val h).symm
  -- transport the walk into `J`
  set Pw : J.Walk x w₀ :=
    Q.map (SimpleGraph.Embedding.induce (({u, v} : Set U)ᶜ)).toHom with hPw
  set L : List U := Q.support.map Subtype.val with hL
  have hPwsupp : Pw.support = L := by
    rw [hPw, hL]
    exact SimpleGraph.Walk.support_map _ _
  -- every vertex of `L` avoids `u` and `v`
  have hLmem : ∀ z ∈ L, z ≠ u ∧ z ≠ v := by
    intro z hz
    rw [hL, List.mem_map] at hz
    obtain ⟨a, -, rfl⟩ := hz
    have ha2 : (a : U) ∈ (({u, v} : Set U))ᶜ := a.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at ha2
    push_neg at ha2
    exact ha2
  have hLnodup : L.Nodup := by
    rw [hL]
    exact hQpath.support_nodup.map Subtype.val_injective
  have hLlen : 2 ≤ L.length := by
    have h1 : L.length = Q.length + 1 := by
      rw [hL, List.length_map, SimpleGraph.Walk.length_support]
    have h2 : ¬ Q.Nil := SimpleGraph.Walk.not_nil_of_ne hQne
    have h3 : Q.length ≠ 0 := by
      intro h
      exact h2 (SimpleGraph.Walk.nil_iff_length_eq.mpr h)
    omega
  -- the closed walk `u → v → x → … → w₀ → u`
  have hcycle : List.IsChain J.Adj (u :: (v :: L) ++ [u]) := by
    have hW : List.IsChain J.Adj
        (SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvx
          (Pw.append (SimpleGraph.Walk.cons huw.symm SimpleGraph.Walk.nil)))).support :=
      SimpleGraph.Walk.isChain_adj_support _
    have hsupp : (SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvx
          (Pw.append (SimpleGraph.Walk.cons huw.symm SimpleGraph.Walk.nil)))).support
        = u :: (v :: L) ++ [u] := by
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_append, hPwsupp]
      simp
    rwa [hsupp] at hW
  refine ⟨L, hLlen, ?_, ?_⟩
  · rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hLnodup⟩
    · simp only [List.mem_cons]
      push_neg
      refine ⟨huvne, ?_⟩
      intro hu
      exact (hLmem u hu).1 rfl
    · intro hv
      exact (hLmem v hv).2 rfl
  · have hrot : (u :: v :: L).rotate 1 = (v :: L) ++ [u] := by
      simp [List.rotate_cons_succ]
    rw [hrot]
    exact zip_adj_of_isChain (v :: L) u u hcycle

end Workspace.ProofLemmas.Thm81Cycle
