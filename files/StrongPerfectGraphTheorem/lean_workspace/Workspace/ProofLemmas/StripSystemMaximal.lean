import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems

/-!
# Enlarging a `J`-strip system to a maximal one

PAPER (proof of 8.6, printed p. 45): *"Regard `L(H₀)` as a `J`-strip system in the natural way,
and enlarge it to a maximal `J`-strip system `(S,N)`."*

`Workspace.Types.StripSystems.MaximalStripSystem` transcribes the paper's notion of maximality
(printed p. 42): `(S,N)` is maximal if there is no `J`-strip system `(S',N')` with
`V(S,N) ⊂ V(S',N')`, `S'_{uv} ∩ V(S,N) = S_{uv}` for every edge `uv`, and `N_v ⊆ N'_v` for
every vertex `v`.  This module supplies the *enlargement* step: over a finite vertex type every
`J`-strip system extends to a maximal one, and the extension relation is recorded in the
conclusion so that downstream arguments can transport rungs of the original system.

The relation "*`(S',N')` enlarges `(S,N)`*" is `Enlarges`; it is reflexive and transitive, and
`stripSystemVertices J ·` is a strictly monotone `ℕ`-valued measure along its strict part, which
is all the maximisation needs.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.StripSystemMaximal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}

/-- `(S',N')` **enlarges** `(S,N)`: the (non-strict) form of the relation appearing in the
paper's definition of a maximal strip system (printed p. 42). -/
def Enlarges (J : SimpleGraph U) (S : U → U → Set V) (N : U → Set V)
    (S' : U → U → Set V) (N' : U → Set V) : Prop :=
  stripSystemVertices J S ⊆ stripSystemVertices J S' ∧
  (∀ u v : U, J.Adj u v → S' u v ∩ stripSystemVertices J S = S u v) ∧
  (∀ v : U, N v ⊆ N' v)

theorem strip_subset_vertices {S : U → U → Set V} {u v : U} (huv : J.Adj u v) :
    S u v ⊆ stripSystemVertices J S := by
  intro x hx
  simp only [stripSystemVertices, Set.mem_iUnion]
  exact ⟨u, v, huv, hx⟩

theorem enlarges_refl (S : U → U → Set V) (N : U → Set V) : Enlarges J S N S N :=
  ⟨subset_rfl, fun _ _ huv => Set.inter_eq_left.mpr (strip_subset_vertices huv), fun _ =>
    subset_rfl⟩

theorem enlarges_trans {S S' S'' : U → U → Set V} {N N' N'' : U → Set V}
    (h₁ : Enlarges J S N S' N') (h₂ : Enlarges J S' N' S'' N'') :
    Enlarges J S N S'' N'' := by
  refine ⟨h₁.1.trans h₂.1, fun u v huv => ?_, fun v => (h₁.2.2 v).trans (h₂.2.2 v)⟩
  have hkey : S'' u v ∩ stripSystemVertices J S
      = (S'' u v ∩ stripSystemVertices J S') ∩ stripSystemVertices J S := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr h₁.1]
  rw [hkey, h₂.2.1 u v huv, h₁.2.1 u v huv]

/-- Over a finite vertex type, every `J`-strip system can be enlarged to a **maximal** one.

PAPER (proof of 8.6): *"… and enlarge it to a maximal `J`-strip system `(S,N)`."* -/
theorem exists_maximal_enlargement [Fintype V] {S : U → U → Set V} {N : U → Set V}
    (h : IsJStripSystem G J S N) :
    ∃ (S' : U → U → Set V) (N' : U → Set V),
      IsJStripSystem G J S' N' ∧ Enlarges J S N S' N' ∧ MaximalStripSystem G J S' N' := by
  classical
  set T : Set ℕ :=
    {n | ∃ (S' : U → U → Set V) (N' : U → Set V),
        IsJStripSystem G J S' N' ∧ Enlarges J S N S' N' ∧
        (stripSystemVertices J S').ncard = n} with hT
  have hTne : T.Nonempty := ⟨_, S, N, h, enlarges_refl S N, rfl⟩
  have hTbdd : BddAbove T := by
    refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨S', N', -, -, rfl⟩
    calc (stripSystemVertices J S').ncard
        ≤ (Set.univ : Set V).ncard := Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
      _ = Fintype.card V := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  obtain ⟨S', N', hSN', hext', hcard'⟩ : sSup T ∈ T := Nat.sSup_mem hTne hTbdd
  refine ⟨S', N', hSN', hext', ?_⟩
  rintro ⟨S'', N'', hSN'', hlt, hinter, hNsub⟩
  have hext'' : Enlarges J S N S'' N'' :=
    enlarges_trans hext' ⟨hlt.subset, hinter, hNsub⟩
  have hmem : (stripSystemVertices J S'').ncard ∈ T := ⟨S'', N'', hSN'', hext'', rfl⟩
  have hle : (stripSystemVertices J S'').ncard ≤ sSup T := le_csSup hTbdd hmem
  have hgt : (stripSystemVertices J S').ncard < (stripSystemVertices J S'').ncard :=
    Set.ncard_lt_ncard hlt (Set.toFinite _)
  omega

end Workspace.ProofLemmas.StripSystemMaximal
