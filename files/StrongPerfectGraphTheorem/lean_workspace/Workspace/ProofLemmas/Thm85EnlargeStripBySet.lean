import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.PathBasics

/-!
# 8.5: enlarging a strip system by a connected set, contradicting maximality

The proof of 8.5 finishes three of its steps by exhibiting a strictly larger `J`-strip system
and quoting the maximality of `(S,N)`:

* end of claim (2), printed p. 42: *"But then we can add `p₁` to `N_v` and `F` to `S_uv`,
  contradicting the maximality of `(S,N)`."*
* inside claim (6), printed p. 43: *"for if `n = 1` then we can add `f₁` to `N_i`, `N_j` and
  `S_ij`, contrary to the maximality of the strip system"*
* end of claim (6), printed p. 43: *"but then we can add `f₁` to `N_i`, `f_n` to `N_j`, and `F`
  to `S_ij`, contrary to the maximality of the strip system."*

All three are the same construction: keep every strip and every neighbourhood except that the
strip of one edge `uv` absorbs `F`, and `N_u`, `N_v` absorb (at most) one vertex of `F` each.
This module verifies once and for all that the result is a `J`-strip system and that it
contradicts `MaximalStripSystem`.

**What is uniform and what is not.**  Six of the seven `IsJStripSystem` axioms — symmetry,
pairwise disjointness, `N_a ⊆ ⋃ S_ab`, anticompleteness across disjoint edges, the
`N_u`-completeness axiom for two edges sharing an end, and the parity axiom (the old special
rungs are still rungs) — follow uniformly from the hypotheses below.  The remaining axiom,
*"for each `uv ∈ E(J)`, every vertex of `S_uv` is in a `uv`-rung"*, is exactly the part that
differs between the three call sites — at the end of (2) the new rungs are old rungs with the
path through `F` grafted onto their `N_v`-end, while in (6) the set `F` is itself a new rung —
so it is taken as the hypothesis `hcover`.

The new system is not built by a `def`; it is passed in as `S'`, `N'` pinned down by equations,
so that a caller can supply whatever concrete families it has already written down.

**Status: this module is a work item — the theorem below is stated but not yet proved.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85EnlargeStripBySet

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- **"We can add `F` to `S_uv` (and one vertex of `F` to each of `N_u`, `N_v`), contradicting
the maximality of `(S,N)`."**  (Proof of 8.5, printed pp. 42–43; used at the end of claim (2)
and twice inside claim (6).)

`Au` and `Av` are the sets of vertices of `F` promoted into `N_u` and into `N_v`; at the three
call sites each is empty or a singleton, but nothing below needs that.  `hcover` is the one
axiom that has to be supplied by the caller (see the module docstring). -/
theorem thm85EnlargeStripBySet {V U : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V)
    (hSN : IsJStripSystem G J S N) (hmax : MaximalStripSystem G J S N)
    (u v : U) (huv : J.Adj u v)
    (F : Set V) (hFne : F.Nonempty) (hFdisj : Disjoint F (stripSystemVertices J S))
    (Au Av : Set V) (hAu : Au ⊆ F) (hAv : Av ⊆ F)
    (S' : U → U → Set V) (N' : U → Set V)
    (hS'uv : S' u v = S u v ∪ F) (hS'vu : S' v u = S u v ∪ F)
    (hS'other : ∀ x y : U, J.Adj x y → s(x, y) ≠ s(u, v) → S' x y = S x y)
    (hN'u : N' u = N u ∪ Au) (hN'v : N' v = N v ∪ Av)
    (hN'other : ∀ w : U, w ≠ u → w ≠ v → N' w = N w)
    -- every `G`-edge leaving `F` towards an *old* strip other than `S_uv` runs from the
    -- promoted vertices into the corresponding neighbourhood:
    (hattach : ∀ f ∈ F, ∀ w x : U, J.Adj w x → s(w, x) ≠ s(u, v) → ∀ y ∈ S w x, G.Adj f y →
      (f ∈ Au ∧ y ∈ N u) ∨ (f ∈ Av ∧ y ∈ N v))
    -- the promoted vertices are complete to the other `N`-parts at their own end:
    (hAucomplete : ∀ w : U, J.Adj u w → w ≠ v → ∀ p ∈ Au, ∀ y ∈ N u ∩ S u w, G.Adj p y)
    (hAvcomplete : ∀ w : U, J.Adj v w → w ≠ u → ∀ p ∈ Av, ∀ y ∈ N v ∩ S v w, G.Adj p y)
    -- the axiom that differs between the three call sites:
    (hcover : ∀ x ∈ S u v ∪ F, ∃ R : List V, IsUVRung G J S' N' u v R ∧ x ∈ R) :
    False := by
  classical
  -- ## Bookkeeping about `F`
  have hFnotV : ∀ f ∈ F, f ∉ stripSystemVertices J S := fun f hf hfV =>
    (Set.disjoint_left.mp hFdisj hf) hfV
  have hstripV : ∀ x y : U, J.Adj x y → S x y ⊆ stripSystemVertices J S :=
    fun x y h => StripSystemBasics.strip_subset_vertices h
  have hFstrip : ∀ x y : U, J.Adj x y → Disjoint F (S x y) := fun x y h =>
    Set.disjoint_left.mpr fun f hf hfS => hFnotV f hf (hstripV x y h hfS)
  have hFN : ∀ w : U, Disjoint F (N w) := fun w =>
    Set.disjoint_left.mpr fun f hf hfN =>
      hFnotV f hf (StripSystemBasics.N_subset_vertices hSN w hfN)
  have hnotF : ∀ (x y : U), J.Adj x y → ∀ z ∈ S x y, z ∉ F := fun x y hxy z hz hzF =>
    (Set.disjoint_left.mp (hFstrip x y hxy) hzF) hz
  -- ## Which edges are the special one
  have hSeq : ∀ x y : U, s(x, y) = s(u, v) → S x y = S u v := by
    intro x y h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (StripSystemBasics.strip_symm hSN huv).symm
  have hS'eq : ∀ x y : U, s(x, y) = s(u, v) → S' x y = S u v ∪ F := by
    intro x y h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hS'uv
    · exact hS'vu
  have hswap : ∀ x y : U, s(x, y) = s(u, v) ↔ s(y, x) = s(u, v) := by
    intro x y; rw [Sym2.eq_swap]
  have hmono : ∀ x y : U, J.Adj x y → S x y ⊆ S' x y := by
    intro x y hxy
    by_cases h : s(x, y) = s(u, v)
    · rw [hS'eq x y h, hSeq x y h]; exact Set.subset_union_left
    · rw [hS'other x y hxy h]
  have hS'symm : ∀ x y : U, J.Adj x y → S' x y = S' y x := by
    intro x y hxy
    by_cases h : s(x, y) = s(u, v)
    · rw [hS'eq x y h, hS'eq y x ((hswap x y).mp h)]
    · rw [hS'other x y hxy h, hS'other y x hxy.symm (fun hc => h ((hswap y x).mp hc))]
      exact StripSystemBasics.strip_symm hSN hxy
  have hS'small : ∀ x y : U, J.Adj x y → s(x, y) ≠ s(u, v) → Disjoint F (S' x y) := by
    intro x y hxy h; rw [hS'other x y hxy h]; exact hFstrip x y hxy
  -- ## `N'` agrees with `N` away from `F`
  have hN'mem : ∀ (w : U) (z : V), z ∉ F → (z ∈ N' w ↔ z ∈ N w) := by
    intro w z hz
    by_cases hu : w = u
    · subst hu; rw [hN'u]
      exact ⟨fun h => h.elim id fun h' => absurd (hAu h') hz, Or.inl⟩
    by_cases hv : w = v
    · subst hv; rw [hN'v]
      exact ⟨fun h => h.elim id fun h' => absurd (hAv h') hz, Or.inl⟩
    · rw [hN'other w hu hv]
  have hN'sub : ∀ w : U, N w ⊆ N' w := by
    intro w z hz
    exact (hN'mem w z (fun hzF => (Set.disjoint_left.mp (hFN w) hzF) hz)).mpr hz
  have hN'inter : ∀ (w x y : U), J.Adj x y → s(x, y) ≠ s(u, v) →
      N' w ∩ S' x y = N w ∩ S x y := by
    intro w x y hxy h
    rw [hS'other x y hxy h]
    ext z
    exact ⟨fun hz => ⟨(hN'mem w z (hnotF x y hxy z hz.2)).mp hz.1, hz.2⟩,
      fun hz => ⟨(hN'mem w z (hnotF x y hxy z hz.2)).mpr hz.1, hz.2⟩⟩
  -- ## Old rungs are rungs of the new system
  have holdrung : ∀ (x y : U) (R : List V), IsUVRung G J S N x y R → IsUVRung G J S' N' x y R := by
    rintro x y R ⟨hxy, s, t, hpath, hsub, hs, ht⟩
    exact ⟨hxy, s, t, hpath, fun z hz => hmono x y hxy (hsub z hz),
      fun z hz => by rw [hN'mem x z (hnotF x y hxy z (hsub z hz))]; exact hs z hz,
      fun z hz => by rw [hN'mem y z (hnotF x y hxy z (hsub z hz))]; exact ht z hz⟩
  -- ## Reversing a rung of the new system
  have hrevrung : ∀ (x y : U) (R : List V), J.Adj x y → IsUVRung G J S' N' x y R →
      IsUVRung G J S' N' y x R.reverse := by
    rintro x y R hxy ⟨-, s, t, hpath, hsub, hs, ht⟩
    refine ⟨hxy.symm, t, s, PathBasics.isPathFrom_reverse hpath, ?_, ?_, ?_⟩
    · intro z hz; rw [List.mem_reverse] at hz
      rw [← hS'symm x y hxy]; exact hsub z hz
    · intro z hz; rw [List.mem_reverse] at hz; exact ht z hz
    · intro z hz; rw [List.mem_reverse] at hz; exact hs z hz
  -- ## Small combinatorial helpers
  have hne4 : ∀ a b c d : U, [a, b, c, d].Nodup → a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
    intro a b c d h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp at h
  have hnodupswap : ∀ a b c d : U, [a, b, c, d].Nodup → [b, a, c, d].Nodup := fun a b c d h =>
    (List.Perm.nodup_iff (List.Perm.swap a b [c, d])).mpr h
  -- ## The new system is a `J`-strip system
  have hnew : IsJStripSystem G J S' N' := by
    refine ⟨hS'symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- pairwise disjointness
      intro x y w z hxy hwz hne
      by_cases h1 : s(x, y) = s(u, v)
      · have h2 : s(w, z) ≠ s(u, v) := fun hc => hne (h1.trans hc.symm)
        rw [hS'eq x y h1, hS'other w z hwz h2]
        refine Set.disjoint_union_left.mpr ⟨?_, hFstrip w z hwz⟩
        exact StripSystemBasics.strip_disjoint hSN huv hwz (fun hc => hne (h1.trans hc))
      · by_cases h2 : s(w, z) = s(u, v)
        · rw [hS'other x y hxy h1, hS'eq w z h2]
          refine Set.disjoint_union_right.mpr ⟨?_, (hFstrip x y hxy).symm⟩
          exact StripSystemBasics.strip_disjoint hSN hxy huv (fun hc => hne (hc.trans h2.symm))
        · rw [hS'other x y hxy h1, hS'other w z hwz h2]
          exact StripSystemBasics.strip_disjoint hSN hxy hwz hne
    · -- `N'_a ⊆ ⋃ S'_ab`
      intro a z hz
      have hold : ∀ w : U, z ∈ N w → z ∈ ⋃ (b : U) (_ : J.Adj w b), S' w b := by
        intro w hw
        have := StripSystemBasics.N_subset_iUnion hSN w hw
        simp only [Set.mem_iUnion] at this ⊢
        obtain ⟨b, hb, hzb⟩ := this
        exact ⟨b, hb, hmono w b hb hzb⟩
      by_cases hu : a = u
      · subst hu
        rw [hN'u] at hz
        rcases hz with hz | hz
        · exact hold a hz
        · simp only [Set.mem_iUnion]
          exact ⟨v, huv, by rw [hS'uv]; exact Or.inr (hAu hz)⟩
      by_cases hv : a = v
      · subst hv
        rw [hN'v] at hz
        rcases hz with hz | hz
        · exact hold a hz
        · simp only [Set.mem_iUnion]
          exact ⟨u, huv.symm, by rw [hS'vu]; exact Or.inr (hAv hz)⟩
      · rw [hN'other a hu hv] at hz; exact hold a hz
    · -- every vertex of a strip is on a rung
      intro x y hxy z hz
      by_cases h : s(x, y) = s(u, v)
      · rw [hS'eq x y h] at hz
        obtain ⟨R, hR, hzR⟩ := hcover z hz
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨R, hR, hzR⟩
        · exact ⟨R.reverse, hrevrung y x R huv hR, by rw [List.mem_reverse]; exact hzR⟩
      · rw [hS'other x y hxy h] at hz
        obtain ⟨R, hR, hzR⟩ := StripSystemBasics.exists_rung hSN hxy hz
        exact ⟨R, holdrung x y R hR, hzR⟩
    · -- anticompleteness across disjoint edges
      intro x y w z hxy hwz hnd
      obtain ⟨hxw, hxz, hyw, hyz⟩ := hne4 x y w z hnd
      have hxywz : s(x, y) ≠ s(w, z) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hxw h1
        · exact hxz h1
      by_cases hxyuv : s(x, y) = s(u, v)
      · have hwzuv : s(w, z) ≠ s(u, v) := fun h =>
          hxywz (hxyuv.trans h.symm)
        have hnduv : [u, v, w, z].Nodup := by
          rcases Sym2.eq_iff.mp hxyuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst x
            subst y
            exact hnd
          · subst x
            subst y
            exact hnodupswap v u w z hnd
        obtain ⟨huw, huz, hvw, hvz⟩ := hne4 u v w z hnduv
        have hFanti : Anticomplete G F (S w z) := by
          intro f hf y' hy' hadj
          rcases hattach f hf w z hwz hwzuv y' hy' hadj with ⟨-, hyN⟩ | ⟨-, hyN⟩
          · have hempty :=
              StripSystemBasics.strip_inter_N_eq_empty hSN hwz huw huz
            rw [Set.eq_empty_iff_forall_notMem] at hempty
            exact hempty y' ⟨hy', hyN⟩
          · have hempty :=
              StripSystemBasics.strip_inter_N_eq_empty hSN hwz hvw hvz
            rw [Set.eq_empty_iff_forall_notMem] at hempty
            exact hempty y' ⟨hy', hyN⟩
        rw [hS'eq x y hxyuv, hS'other w z hwz hwzuv]
        intro a ha b hb hab
        rcases ha with ha | ha
        · exact StripSystemBasics.strip_anticomplete hSN huv hwz hnduv a ha b hb hab
        · exact hFanti a ha b hb hab
      · by_cases hwzuv : s(w, z) = s(u, v)
        · have hxyuv : s(x, y) ≠ s(u, v) := fun h =>
            hxywz (h.trans hwzuv.symm)
          have hndxyuv : [x, y, u, v].Nodup := by
            rcases Sym2.eq_iff.mp hwzuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · subst w
              subst z
              exact hnd
            · subst w
              subst z
              have hxyne : x ≠ y := hxy.ne
              have huvne : u ≠ v := huv.ne
              simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
                or_false, not_or]
              tauto
          obtain ⟨hxu, hxv, hyu, hyv⟩ := hne4 x y u v hndxyuv
          have hFanti : Anticomplete G (S x y) F := by
            intro a ha f hf hadj
            rcases hattach f hf x y hxy hxyuv a ha hadj.symm with ⟨-, haN⟩ | ⟨-, haN⟩
            · have hempty :=
                StripSystemBasics.strip_inter_N_eq_empty hSN hxy (Ne.symm hxu) (Ne.symm hyu)
              rw [Set.eq_empty_iff_forall_notMem] at hempty
              exact hempty a ⟨ha, haN⟩
            · have hempty :=
                StripSystemBasics.strip_inter_N_eq_empty hSN hxy (Ne.symm hxv) (Ne.symm hyv)
              rw [Set.eq_empty_iff_forall_notMem] at hempty
              exact hempty a ⟨ha, haN⟩
          rw [hS'other x y hxy hxyuv, hS'eq w z hwzuv]
          intro a ha b hb hab
          rcases hb with hb | hb
          · exact StripSystemBasics.strip_anticomplete hSN hxy huv hndxyuv a ha b hb hab
          · exact hFanti a ha b hb hab
        · rw [hS'other x y hxy hxyuv, hS'other w z hwz hwzuv]
          exact StripSystemBasics.strip_anticomplete hSN hxy hwz hnd
    · -- completeness and endpoint condition at a shared end
      intro x y w hxy hxw hyw
      have hxyw : s(x, y) ≠ s(x, w) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
        · exact hyw h2
        · exact hyw (h2.trans h1)
      by_cases hxyuv : s(x, y) = s(u, v)
      · have hxwuv : s(x, w) ≠ s(u, v) := fun h =>
          hxyw (hxyuv.trans h.symm)
        rcases Sym2.eq_iff.mp hxyuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst x
          subst y
          rw [hN'inter u u w hxw hxwuv]
          constructor
          · intro p hp q hq
            rcases hp with ⟨hpN, hpS⟩
            rw [hN'u] at hpN
            rw [hS'uv] at hpS
            rcases hpN with hpN | hpAu
            · have hpSuv : p ∈ S u v := by
                rcases hpS with hpS | hpF
                · exact hpS
                · exact False.elim ((Set.disjoint_left.mp (hFN u) hpF) hpN)
              exact StripSystemBasics.Nuv_complete hSN huv hxw hyw p ⟨hpN, hpSuv⟩ q hq
            · exact hAucomplete w hxw (Ne.symm hyw) p hpAu q hq
          · intro p hp q hq hadj
            rw [hS'uv] at hp
            rw [hS'other u w hxw hxwuv] at hq
            rcases hp with hp | hp
            · obtain ⟨hpNu, hqNu⟩ :=
                StripSystemBasics.mem_N_of_adj hSN huv hxw hyw hp hq hadj
              exact ⟨hN'sub u hpNu, hN'sub u hqNu⟩
            · rcases hattach p hp u w hxw hxwuv q hq hadj with ⟨hpAu, hqNu⟩ | ⟨hpAv, hqNv⟩
              · rw [hN'u]
                exact ⟨Or.inr hpAu, Or.inl hqNu⟩
              · have hempty :=
                  StripSystemBasics.strip_inter_N_eq_empty hSN hxw huv.ne' hyw
                rw [Set.eq_empty_iff_forall_notMem] at hempty
                exact False.elim (hempty q ⟨hq, hqNv⟩)
        · subst x
          subst y
          rw [hN'inter v v w hxw hxwuv]
          constructor
          · intro p hp q hq
            rcases hp with ⟨hpN, hpS⟩
            rw [hN'v] at hpN
            rw [hS'vu] at hpS
            rcases hpN with hpN | hpAv
            · have hpSvu : p ∈ S v u := by
                rcases hpS with hpS | hpF
                · rw [← StripSystemBasics.strip_symm hSN huv]
                  exact hpS
                · exact False.elim ((Set.disjoint_left.mp (hFN v) hpF) hpN)
              exact StripSystemBasics.Nuv_complete hSN huv.symm hxw hyw p ⟨hpN, hpSvu⟩ q hq
            · exact hAvcomplete w hxw (Ne.symm hyw) p hpAv q hq
          · intro p hp q hq hadj
            rw [hS'vu] at hp
            rw [hS'other v w hxw hxwuv] at hq
            rcases hp with hp | hp
            · have hpSvu : p ∈ S v u := by
                rw [← StripSystemBasics.strip_symm hSN huv]
                exact hp
              obtain ⟨hpNv, hqNv⟩ :=
                StripSystemBasics.mem_N_of_adj hSN huv.symm hxw hyw hpSvu hq hadj
              exact ⟨hN'sub v hpNv, hN'sub v hqNv⟩
            · rcases hattach p hp v w hxw hxwuv q hq hadj with ⟨hpAu, hqNu⟩ | ⟨hpAv, hqNv⟩
              · have hempty :=
                  StripSystemBasics.strip_inter_N_eq_empty hSN hxw huv.ne hyw
                rw [Set.eq_empty_iff_forall_notMem] at hempty
                exact False.elim (hempty q ⟨hq, hqNu⟩)
              · rw [hN'v]
                exact ⟨Or.inr hpAv, Or.inl hqNv⟩
      · by_cases hxwuv : s(x, w) = s(u, v)
        · have hxyuv : s(x, y) ≠ s(u, v) := fun h =>
            hxyw (h.trans hxwuv.symm)
          rcases Sym2.eq_iff.mp hxwuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst x
            subst w
            rw [hN'inter u u y hxy hxyuv]
            constructor
            · intro p hp q hq
              rcases hq with ⟨hqN, hqS⟩
              rw [hN'u] at hqN
              rw [hS'uv] at hqS
              rcases hqN with hqN | hqAu
              · have hqSuv : q ∈ S u v := by
                  rcases hqS with hqS | hqF
                  · exact hqS
                  · exact False.elim ((Set.disjoint_left.mp (hFN u) hqF) hqN)
                exact StripSystemBasics.Nuv_complete hSN hxy huv hyw p hp q ⟨hqN, hqSuv⟩
              · exact (hAucomplete y hxy hyw q hqAu p hp).symm
            · intro p hp q hq hadj
              rw [hS'other u y hxy hxyuv] at hp
              rw [hS'uv] at hq
              rcases hq with hq | hq
              · obtain ⟨hpNu, hqNu⟩ :=
                  StripSystemBasics.mem_N_of_adj hSN hxy huv hyw hp hq hadj
                exact ⟨hN'sub u hpNu, hN'sub u hqNu⟩
              · rcases hattach q hq u y hxy hxyuv p hp hadj.symm with
                  ⟨hqAu, hpNu⟩ | ⟨hqAv, hpNv⟩
                · rw [hN'u]
                  exact ⟨Or.inl hpNu, Or.inr hqAu⟩
                · have hempty :=
                    StripSystemBasics.strip_inter_N_eq_empty hSN hxy huv.ne' (Ne.symm hyw)
                  rw [Set.eq_empty_iff_forall_notMem] at hempty
                  exact False.elim (hempty p ⟨hp, hpNv⟩)
          · subst x
            subst w
            rw [hN'inter v v y hxy hxyuv]
            constructor
            · intro p hp q hq
              rcases hq with ⟨hqN, hqS⟩
              rw [hN'v] at hqN
              rw [hS'vu] at hqS
              rcases hqN with hqN | hqAv
              · have hqSvu : q ∈ S v u := by
                  rcases hqS with hqS | hqF
                  · rw [← StripSystemBasics.strip_symm hSN huv]
                    exact hqS
                  · exact False.elim ((Set.disjoint_left.mp (hFN v) hqF) hqN)
                exact StripSystemBasics.Nuv_complete hSN hxy huv.symm hyw p hp q ⟨hqN, hqSvu⟩
              · exact (hAvcomplete y hxy hyw q hqAv p hp).symm
            · intro p hp q hq hadj
              rw [hS'other v y hxy hxyuv] at hp
              rw [hS'vu] at hq
              rcases hq with hq | hq
              · have hqSvu : q ∈ S v u := by
                  rw [← StripSystemBasics.strip_symm hSN huv]
                  exact hq
                obtain ⟨hpNv, hqNv⟩ :=
                  StripSystemBasics.mem_N_of_adj hSN hxy huv.symm hyw hp hqSvu hadj
                exact ⟨hN'sub v hpNv, hN'sub v hqNv⟩
              · rcases hattach q hq v y hxy hxyuv p hp hadj.symm with
                  ⟨hqAu, hpNu⟩ | ⟨hqAv, hpNv⟩
                · have hempty :=
                    StripSystemBasics.strip_inter_N_eq_empty hSN hxy huv.ne (Ne.symm hyw)
                  rw [Set.eq_empty_iff_forall_notMem] at hempty
                  exact False.elim (hempty p ⟨hp, hpNu⟩)
                · rw [hN'v]
                  exact ⟨Or.inl hpNv, Or.inr hqAv⟩
        · rw [hN'inter x x y hxy hxyuv, hN'inter x x w hxw hxwuv]
          constructor
          · exact StripSystemBasics.Nuv_complete hSN hxy hxw hyw
          · intro p hp q hq hadj
            rw [hS'other x y hxy hxyuv] at hp
            rw [hS'other x w hxw hxwuv] at hq
            obtain ⟨hpN, hqN⟩ :=
              StripSystemBasics.mem_N_of_adj hSN hxy hxw hyw hp hq hadj
            exact ⟨hN'sub x hpN, hN'sub x hqN⟩
    · obtain ⟨R₀, hR₀rung, hR₀par⟩ := StripSystemBasics.exists_special_rungs hSN
      exact ⟨R₀, fun x y hxy => holdrung x y (R₀ x y) (hR₀rung x y hxy), hR₀par⟩
  -- ## The enlargement contradicts maximality
  refine hmax ⟨S', N', hnew, ⟨?_, ?_⟩, ?_, hN'sub⟩
  · intro z hz
    rw [StripSystemBasics.mem_stripSystemVertices_iff] at hz ⊢
    obtain ⟨x, y, hxy, hzxy⟩ := hz
    exact ⟨x, y, hxy, hmono x y hxy hzxy⟩
  · obtain ⟨f, hf⟩ := hFne
    intro hsub
    refine hFnotV f hf ?_
    exact hsub (by
      rw [StripSystemBasics.mem_stripSystemVertices_iff]
      exact ⟨u, v, huv, by rw [hS'uv]; exact Or.inr hf⟩)
  · intro x y hxy
    by_cases h : s(x, y) = s(u, v)
    · rw [hS'eq x y h, hSeq x y h, Set.union_inter_distrib_right]
      have h1 : S u v ∩ stripSystemVertices J S = S u v :=
        Set.inter_eq_left.mpr (hstripV u v huv)
      have h2 : F ∩ stripSystemVertices J S = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro z hz
        exact hFnotV z hz.1 hz.2
      rw [h1, h2, Set.union_empty]
    · rw [hS'other x y hxy h]
      exact Set.inter_eq_left.mpr (hstripV x y hxy)

end Workspace.ProofLemmas.Thm85EnlargeStripBySet
