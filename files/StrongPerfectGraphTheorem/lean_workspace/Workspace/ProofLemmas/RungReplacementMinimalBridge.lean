import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# Minimal bridges attach to each side at only one vertex

PAPER (proof of 7.5, printed p. 38): *"From the minimality of `F`, `r′₁` has no neighbour in
`T`."*

The paper's `F` is a **minimal** connected set that has a neighbour in `S` and a neighbour in
`T`.  The sentence quoted above is an instance of the following purely combinatorial fact,
which is what this module proves.

> If `F` is connected, has a neighbour in `S`, has a neighbour in `T`, and no proper subset of
> `F` is connected with a neighbour in both, then **at most one vertex of `F` has a neighbour
> in `T`** (and symmetrically for `S`).

The argument is short.  Pick a vertex `a ∈ F` with a neighbour in `S`, and a vertex `f₁ ∈ F`
with a neighbour in `T`.  A connected set carries an induced path between any two of its
vertices, so take a path `p` from `a` to `f₁` inside `F`.  Its vertex set is connected, is
contained in `F`, contains `a`, and contains `f₁`, so it has a neighbour on both sides; by
minimality it is all of `F`.  Now let `f₂ ∈ F` be a second vertex with a neighbour in `T`.
It occurs on `p` at some position before the last one, and the initial segment of `p` ending at
`f₂` is again connected, contained in `F`, still contains `a`, and still has a neighbour in `T`
(namely at `f₂`), but it misses `f₁`.  That contradicts minimality, so `f₂ = f₁`.

The set `Z` is a set of forbidden vertices (in 7.5 it is `X₀ ∪ X₁ ∪ Y`), carried along because
the minimality hypothesis in that application is stated only for subsets avoiding `Z`.  Every
subset of `F` inherits the condition, so it causes no difficulty.

Nothing here corresponds to a numbered result of the paper; it is the graph-theoretic content
of the phrase *"from the minimality of `F`"*.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementMinimalBridge

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- **At most one vertex of a minimal bridge has a neighbour in `T`.**

`F` is connected, avoids `Z`, has a neighbour in `S`, and is minimal among the subsets of `F`
with those three properties that also have a neighbour in `T`.  Then the vertices of `F` with a
neighbour in `T` form a subsingleton.

This is the general form of *"From the minimality of `F`, `r′₁` has no neighbour in `T`"*: if
two distinct vertices of `F` both had a neighbour in `T`, the initial segment of a path through
one of them would be a smaller admissible set. -/
theorem t_attachment_vertices_subsingleton_of_minimal_bridge
    (S T F Z : Set V)
    (hFconn : ConnectedSet G F)
    (hFZ : ∀ x ∈ F, x ∉ Z)
    (hSF : ∃ s ∈ S, ∃ f ∈ F, G.Adj s f)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ConnectedSet G F' →
      (∀ x ∈ F', x ∉ Z) → (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) →
      (∃ t ∈ T, ∃ f ∈ F', G.Adj t f) → False) :
    {f : V | f ∈ F ∧ ∃ t ∈ T, G.Adj t f}.Subsingleton := by
  classical
  rintro f₁ ⟨hf₁F, t₁, ht₁, ht₁f₁⟩ f₂ ⟨hf₂F, t₂, ht₂, ht₂f₂⟩
  by_contra hne
  obtain ⟨s, hs, a, haF, hsa⟩ := hSF
  obtain ⟨p, hp, hpF⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hFconn haF hf₁F
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have hnd : p.Nodup := PathBasics.path_nodup hp.1
  have h0 : p[0]'hpos = a := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hlast : p[p.length - 1]'(by omega) = f₁ :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hamem : a ∈ p := by rw [← h0]; exact List.getElem_mem _
  have hf₁mem : f₁ ∈ p := by rw [← hlast]; exact List.getElem_mem _
  -- the whole path is `F`, by minimality
  have hpall : {x : V | x ∈ p} = F := by
    by_contra hcontra
    exact hmin {x : V | x ∈ p} (fun x hx => hpF x hx) hcontra
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp.1)
      (fun x hx => hFZ x (hpF x hx)) ⟨s, hs, a, hamem, hsa⟩ ⟨t₁, ht₁, f₁, hf₁mem, ht₁f₁⟩
  -- `f₂` occurs on the path, strictly before its last vertex
  have hf₂mem : f₂ ∈ p := by
    have : f₂ ∈ {x : V | x ∈ p} := by rw [hpall]; exact hf₂F
    exact this
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hf₂mem
  have hilt : i < p.length - 1 := by
    rcases Nat.lt_or_ge i (p.length - 1) with h | h
    · exact h
    · exfalso
      have hieq : i = p.length - 1 := by omega
      have hstep := gidx p hieq hi (show p.length - 1 < p.length by omega)
      exact hne (((hpi.symm.trans hstep).trans hlast).symm)
  -- the initial segment of `p` ending at `f₂` is a strictly smaller admissible set
  set p' : List V := p.take (i + 1) with hp'
  have hp'len : p'.length = i + 1 := by
    simp only [hp', List.length_take]; omega
  have hp'path : IsPathList G p' := PathBasics.isPathList_take hp.1 (by omega)
  have hp'sub : ∀ x ∈ p', x ∈ p := fun x hx => (List.take_sublist (i + 1) p).mem hx
  have hamem' : a ∈ p' := by
    have : p'[0]'(by omega) = p[0]'hpos := by simp [hp']
    rw [← h0, ← this]
    exact List.getElem_mem _
  have hf₂mem' : f₂ ∈ p' := by
    have : p'[i]'(by omega) = p[i]'hi := by simp [hp']
    rw [← hpi, ← this]
    exact List.getElem_mem _
  have hf₁not : f₁ ∉ p' := by
    intro hmem
    obtain ⟨j, hj, hpj⟩ := List.mem_iff_getElem.mp hmem
    have hjp : p[j]'(by omega) = f₁ := by
      have : p'[j]'hj = p[j]'(by omega) := by simp [hp']
      rw [← this]; exact hpj
    have hjeq : j = p.length - 1 :=
      (List.Nodup.getElem_inj_iff hnd).mp (hjp.trans hlast.symm)
    omega
  refine hmin {x : V | x ∈ p'} (fun x hx => hpF x (hp'sub x hx)) ?_
    (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp'path)
    (fun x hx => hFZ x (hpF x (hp'sub x hx)))
    ⟨s, hs, a, hamem', hsa⟩ ⟨t₂, ht₂, f₂, hf₂mem', ht₂f₂⟩
  intro hEq
  apply hf₁not
  have : f₁ ∈ {x : V | x ∈ p'} := by rw [hEq]; exact hf₁F
  exact this

end Workspace.ProofLemmas.RungReplacementMinimalBridge
