import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# (C) Composing a `K₄`-subdivision datum with a subdivision

`Workspace.ProofLemmas.SubdivisionDatum` introduced `IsK4Datum` / `HasK4Datum`: the six *local*
clauses of `IsSubdivision (⊤ : SimpleGraph (Fin 4)) D`, with the two *exactness* clauses (cover,
edge-set) dropped.  This module proves the composition step

```
HasK4Datum J  →  IsSubdivision J H  →  HasK4Datum H
```

which is step (C) of the chain that supplies the opening sentence of the proof of 5.3,
*"There is a subgraph of `H` which is a subdivision of `K₄`"*.  Dirac's theorem
(`Workspace.PriorWork.DiracK4Subdivision`) can only be applied to the 3-connected graph `J` that
`H` subdivides, never to `H` itself, since the internal vertices of `H`'s tracks have degree `2`.

The construction is the obvious one: a `K₄`-track `R a b = [x₀, …, x_m]` of `J` is a list of
vertices with consecutive entries `J`-adjacent, and the subdivision replaces each `J`-edge
`x_i x_{i+1}` by an `H`-track `T x_i x_{i+1}`; concatenating those `H`-tracks along their shared
ends gives the `H`-track joining `ι (κ a)` to `ι (κ b)`.  This is `expandTracks`.

The work is entirely in the two disjointness statements:

* `expandTracks_nodup` — the concatenation has no repeated vertex.  A vertex shared by the first
  block `T x₀ x₁` and the rest is either an old vertex `ι x` (and then `x₀ ∉ [x₁, …, x_m]`
  because `R a b` is `Nodup`) or an internal vertex of some later `T x_i x_{i+1}` (and then
  the subdivision's own disjointness clause applies, because `x₀` lies on `s(x₀,x₁)` but not on
  `s(x_i,x_{i+1})`).
* clause 5 of the composed datum — two *different* `K₄`-edges give vertex-disjoint expansions
  away from the four branch vertices.  This needs the interior-disjointness of the `T`'s **and**
  of the `R`'s at the same time: `key` below says that two different `K₄`-tracks of `J` never
  use a common `J`-edge, because a common `J`-edge would have both of its ends on both tracks,
  hence (interiors being disjoint) both ends would be branch vertices of both tracks, forcing
  `s(a,b) = s(a',b')`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.SubdivisionCompose

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionDatum

variable {U W : Type*}

/-! ### Ends and interior of a list -/

/-- An internal vertex of a track is a vertex of the track. -/
theorem mem_of_mem_trackInterior {l : List W} {w : W} (h : w ∈ trackInterior l) : w ∈ l :=
  List.tail_subset _ (List.dropLast_subset _ h)

/-- An internal vertex of a `Nodup` track is not its first vertex. -/
theorem ne_head_of_mem_trackInterior {l : List W} {u w : W} (hnd : l.Nodup)
    (hh : l.head? = some u) (hw : w ∈ trackInterior l) : w ≠ u := by
  intro hwu
  have hcons : u :: l.tail = l := List.cons_head?_tail hh
  have hnd' : (u :: l.tail).Nodup := by rw [hcons]; exact hnd
  refine (List.nodup_cons.mp hnd').1 ?_
  rw [← hwu]
  exact List.dropLast_subset _ hw

/-- An internal vertex of a `Nodup` track is not its last vertex. -/
theorem ne_getLast_of_mem_trackInterior {l : List W} {v w : W} (hnd : l.Nodup)
    (hl : l.getLast? = some v) (hw : w ∈ trackInterior l) : w ≠ v := by
  intro hwv
  have hcons : l.dropLast ++ [v] = l := List.dropLast_append_getLast? v hl
  have hnd' : (l.dropLast ++ [v]).Nodup := by rw [hcons]; exact hnd
  refine (List.nodup_append.mp hnd').2.2 v ?_ v (List.mem_singleton_self v) rfl
  rw [← hwv]
  have h1 : w ∈ l.dropLast.tail := by rw [List.tail_dropLast]; exact hw
  exact List.tail_subset _ h1

/-- A vertex of a track which is not internal is one of the two named ends.
(`head?`/`getLast?` form of `DegenerateK4Tracks.mem_ends_of_notMem_interior`.) -/
theorem mem_ends_of_mem {l : List W} {u v w : W} (hh : l.head? = some u)
    (hl : l.getLast? = some v) (hw : w ∈ l) (hnot : w ∉ trackInterior l) : w = u ∨ w = v := by
  have h0 : 0 < l.length := List.length_pos_of_mem hw
  have e1 : l[0]'h0 = u := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at hh
    exact Option.some_injective _ hh
  have e2 : l[l.length - 1]'(by omega) = v := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl
    exact Option.some_injective _ hl
  rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hw hnot h0 with h | h
  · exact Or.inl (h.trans e1)
  · exact Or.inr (h.trans e2)

/-- Reversing a chain for a symmetric relation. -/
theorem isChain_reverse_symm {α : Type*} {R : α → α → Prop} (hsymm : ∀ a b : α, R a b → R b a)
    {l : List α} (h : List.IsChain R l) : List.IsChain R l.reverse :=
  List.isChain_reverse.mpr (h.imp (by intro a b hab; exact hsymm a b hab))

/-! ### The witness of a subdivision -/

/-- The six *local* clauses of `IsSubdivision J H` for a witness pair `(ι, T)`.  The two
*exactness* clauses of `IsSubdivision` (the cover clause and the edge-set clause) are omitted:
nothing below uses them. -/
structure SubdivWitness (J : SimpleGraph U) (H : SimpleGraph W) (ι : U → W)
    (T : U → U → List W) : Prop where
  /-- the branch vertices of `J` are embedded injectively -/
  inj : Function.Injective ι
  /-- each edge of `J` carries a track of `H` between the images of its ends -/
  track : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v)
  /-- each such track has at least one edge -/
  len : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v)
  /-- reversing the edge reverses the track -/
  rev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse
  /-- distinct edges give tracks meeting only in their ends -/
  disj : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
    ∀ w ∈ trackInterior (T u v), w ∉ T u' v'
  /-- the new vertices really are new -/
  new : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι

theorem exists_subdivWitness {J : SimpleGraph U} {H : SimpleGraph W} (h : IsSubdivision J H) :
    ∃ (ι : U → W) (T : U → U → List W), SubdivWitness J H ι T := by
  obtain ⟨ι, T, h1, h2, h3, h4, h5, h6, -, -⟩ := h
  exact ⟨ι, T, ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-! ### Expanding a `J`-track into an `H`-track -/

/-- Replace every edge of a list of `J`-vertices by the `H`-track the subdivision attaches to it,
and concatenate the results along their shared ends. -/
def expandTracks (ι : U → W) (T : U → U → List W) : List U → List W
  | [] => []
  | [x] => [ι x]
  | x :: y :: rest => (T x y).dropLast ++ expandTracks ι T (y :: rest)

variable {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

@[simp] theorem expandTracks_nil : expandTracks ι T ([] : List U) = [] := rfl

@[simp] theorem expandTracks_singleton (x : U) : expandTracks ι T [x] = [ι x] := rfl

theorem expandTracks_cons_cons (x y : U) (rest : List U) :
    expandTracks ι T (x :: y :: rest) = (T x y).dropLast ++ expandTracks ι T (y :: rest) := rfl

/-! ### Basic facts about the tracks of a subdivision -/

theorem two_le_track_length (hS : SubdivWitness J H ι T) {u v : U} (huv : J.Adj u v) :
    2 ≤ (T u v).length := by
  have h1 := hS.len u v huv
  simp only [trackLength] at h1
  omega

theorem track_nodup (hS : SubdivWitness J H ι T) {u v : U} (huv : J.Adj u v) :
    (T u v).Nodup := (hS.track u v huv).1.2.1

theorem track_head? (hS : SubdivWitness J H ι T) {u v : U} (huv : J.Adj u v) :
    (T u v).head? = some (ι u) := (hS.track u v huv).2.1

theorem track_getLast? (hS : SubdivWitness J H ι T) {u v : U} (huv : J.Adj u v) :
    (T u v).getLast? = some (ι v) := (hS.track u v huv).2.2

theorem track_isChain (hS : SubdivWitness J H ι T) {u v : U} (huv : J.Adj u v) :
    List.IsChain H.Adj (T u v) :=
  List.isChain_iff_getElem.mpr (hS.track u v huv).1.2.2

/-! ### The expansion is a track -/

theorem expandTracks_head? (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → (expandTracks ι T p).head? = p.head?.map ι := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons x t _ =>
    cases t with
    | nil => intro _; rfl
    | cons y rest =>
      intro hch
      have hxy : J.Adj x y := hch.rel_head
      have hA : ((T x y).dropLast).head? = some (ι x) := by
        rw [List.head?_dropLast, if_pos (by have := two_le_track_length hS hxy; omega)]
        exact track_head? hS hxy
      rw [expandTracks_cons_cons, List.head?_append, hA]
      rfl

theorem expandTracks_ne_nil (hS : SubdivWitness J H ι T) {p : List U}
    (hch : List.IsChain J.Adj p) (hp : p ≠ []) : expandTracks ι T p ≠ [] := by
  cases p with
  | nil => exact absurd rfl hp
  | cons x t =>
    intro hcon
    have h := expandTracks_head? hS (x :: t) hch
    rw [hcon] at h
    simp at h

theorem expandTracks_getLast? (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → (expandTracks ι T p).getLast? = p.getLast?.map ι := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons x t ih =>
    cases t with
    | nil => intro _; rfl
    | cons y rest =>
      intro hch
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      have hBne : expandTracks ι T (y :: rest) ≠ [] :=
        expandTracks_ne_nil hS htail (by simp)
      rw [expandTracks_cons_cons, List.getLast?_append_of_ne_nil _ hBne, ih htail,
        List.getLast?_cons_of_ne_nil (by simp : (y :: rest) ≠ [])]

theorem two_le_expandTracks_length (hS : SubdivWitness J H ι T) {p : List U}
    (hch : List.IsChain J.Adj p) (hp : 2 ≤ p.length) : 2 ≤ (expandTracks ι T p).length := by
  cases p with
  | nil => simp at hp
  | cons x t =>
    cases t with
    | nil => simp at hp
    | cons y rest =>
      have hxy : J.Adj x y := hch.rel_head
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      have h1 : 1 ≤ ((T x y).dropLast).length := by
        rw [List.length_dropLast]
        have := two_le_track_length hS hxy
        omega
      have h2 : 0 < (expandTracks ι T (y :: rest)).length :=
        List.length_pos_iff.mpr (expandTracks_ne_nil hS htail (by simp))
      rw [expandTracks_cons_cons, List.length_append]
      omega

theorem expandTracks_isChain (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → List.IsChain H.Adj (expandTracks ι T p) := by
  intro p
  induction p with
  | nil => intro _; exact List.isChain_nil
  | cons x t ih =>
    cases t with
    | nil => intro _; exact List.isChain_singleton _
    | cons y rest =>
      intro hch
      have hxy : J.Adj x y := hch.rel_head
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      have hTch : List.IsChain H.Adj (T x y) := track_isChain hS hxy
      rw [expandTracks_cons_cons]
      refine List.isChain_append.mpr ⟨hTch.dropLast, ih htail, ?_⟩
      intro c hc d hd
      have hBh : (expandTracks ι T (y :: rest)).head? = some (ι y) := by
        rw [expandTracks_head? hS (y :: rest) htail]; rfl
      have hdy : d = ι y := by
        rw [Option.mem_def, hBh] at hd
        exact (Option.some_injective _ hd).symm
      have heq : (T x y).dropLast ++ [ι y] = T x y :=
        List.dropLast_append_getLast? (ι y) (track_getLast? hS hxy)
      have hch2 : List.IsChain H.Adj ((T x y).dropLast ++ [ι y]) := by rw [heq]; exact hTch
      rw [hdy]
      exact (List.isChain_append.mp hch2).2.2 c hc (ι y) rfl

/-! ### Which vertices the expansion uses -/

/-- Every vertex of the expansion is either an image `ι x` of a vertex of `p`, or an internal
vertex of one of the tracks attached to an edge with both ends on `p`. -/
theorem mem_expandTracks (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → ∀ w : W, w ∈ expandTracks ι T p →
      (∃ x ∈ p, w = ι x) ∨
      (∃ x y : U, x ∈ p ∧ y ∈ p ∧ J.Adj x y ∧ w ∈ trackInterior (T x y)) := by
  intro p
  induction p with
  | nil => intro _ w hw; simp at hw
  | cons x t ih =>
    cases t with
    | nil =>
      intro _ w hw
      rw [expandTracks_singleton] at hw
      exact Or.inl ⟨x, List.mem_singleton_self x, by simpa using hw⟩
    | cons y rest =>
      intro hch w hw
      have hxy : J.Adj x y := hch.rel_head
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      rw [expandTracks_cons_cons] at hw
      rcases List.mem_append.mp hw with hw1 | hw2
      · have hwT : w ∈ T x y := List.dropLast_subset _ hw1
        by_cases hint : w ∈ trackInterior (T x y)
        · exact Or.inr ⟨x, y, List.mem_cons_self,
            List.mem_cons_of_mem _ List.mem_cons_self, hxy, hint⟩
        · rcases mem_ends_of_mem (track_head? hS hxy) (track_getLast? hS hxy) hwT hint with h | h
          · exact Or.inl ⟨x, List.mem_cons_self, h⟩
          · exact Or.inl ⟨y, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
      · rcases ih htail w hw2 with ⟨x', hx'mem, hx'eq⟩ | ⟨x', y', hx'mem, hy'mem, hx'y', hint⟩
        · exact Or.inl ⟨x', List.mem_cons_of_mem _ hx'mem, hx'eq⟩
        · exact Or.inr ⟨x', y', List.mem_cons_of_mem _ hx'mem,
            List.mem_cons_of_mem _ hy'mem, hx'y', hint⟩

/-! ### The expansion has no repeated vertex -/

theorem expandTracks_nodup (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → p.Nodup → (expandTracks ι T p).Nodup := by
  intro p
  induction p with
  | nil => intro _ _; rw [expandTracks_nil]; exact List.nodup_nil
  | cons x t ih =>
    cases t with
    | nil => intro _ _; rw [expandTracks_singleton]; exact List.nodup_singleton _
    | cons y rest =>
      intro hch hnd
      have hxy : J.Adj x y := hch.rel_head
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      have hxnotin : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
      rw [expandTracks_cons_cons]
      refine List.nodup_append.mpr
        ⟨List.Nodup.sublist (List.dropLast_sublist _) (track_nodup hS hxy),
          ih htail (List.nodup_cons.mp hnd).2, ?_⟩
      intro c hc d hd hcd
      rw [← hcd] at hd
      have hcT : c ∈ T x y := List.dropLast_subset _ hc
      have hcny : c ≠ ι y := by
        intro hcy
        have hlast : (T x y).dropLast ++ [ι y] = T x y :=
          List.dropLast_append_getLast? (ι y) (track_getLast? hS hxy)
        have hnd2 : ((T x y).dropLast ++ [ι y]).Nodup := by
          rw [hlast]; exact track_nodup hS hxy
        refine (List.nodup_append.mp hnd2).2.2 (ι y) ?_ (ι y) (List.mem_singleton_self _) rfl
        rw [← hcy]; exact hc
      rcases mem_expandTracks hS (y :: rest) htail c hd with
        ⟨x', hx'mem, hx'eq⟩ | ⟨x', y', hx'mem, hy'mem, hx'y', hint⟩
      · by_cases hci : c ∈ trackInterior (T x y)
        · exact hS.new x y hxy c hci ⟨x', hx'eq.symm⟩
        · rcases mem_ends_of_mem (track_head? hS hxy) (track_getLast? hS hxy) hcT hci with h | h
          · refine hxnotin ?_
            have : x' = x := hS.inj (hx'eq.symm.trans h)
            rw [← this]; exact hx'mem
          · exact hcny h
      · have hsne : s(x', y') ≠ s(x, y) := by
          intro he
          rcases Sym2.eq_iff.mp he with ⟨p1, p2⟩ | ⟨p1, p2⟩
          · refine hxnotin ?_; rw [← p1]; exact hx'mem
          · refine hxnotin ?_; rw [← p2]; exact hy'mem
        exact hS.disj x' y' x y hx'y' hxy hsne c hint hcT

/-! ### The expansion commutes with reversal -/

theorem expandTracks_append_singleton (hS : SubdivWitness J H ι T) :
    ∀ (q : List U) (z x : U), q.getLast? = some z → List.IsChain J.Adj (q ++ [x]) →
      expandTracks ι T (q ++ [x]) = expandTracks ι T q ++ (T z x).tail := by
  intro q
  induction q with
  | nil => intro z x hz _; simp at hz
  | cons a t ih =>
    cases t with
    | nil =>
      intro z x hz hch
      have hza : z = a := by
        rw [List.getLast?_singleton] at hz
        exact (Option.some_injective _ hz).symm
      rw [hza]
      simp only [List.cons_append, List.nil_append] at hch ⊢
      have hax : J.Adj a x := hch.rel_head
      rw [expandTracks_cons_cons, expandTracks_singleton, expandTracks_singleton,
        List.dropLast_append_getLast? (ι x) (track_getLast? hS hax)]
      exact (List.cons_head?_tail (track_head? hS hax)).symm
    | cons b t' =>
      intro z x hz hch
      have hz' : (b :: t').getLast? = some z := by
        rw [← hz, List.getLast?_cons_of_ne_nil (by simp : (b :: t') ≠ [])]
      simp only [List.cons_append] at hch ⊢
      have htail : List.IsChain J.Adj ((b :: t') ++ [x]) := by
        simpa only [List.cons_append] using hch.tail
      have hIH := ih z x hz' htail
      simp only [List.cons_append] at hIH
      rw [expandTracks_cons_cons, expandTracks_cons_cons, hIH, List.append_assoc]

theorem expandTracks_reverse (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p →
      expandTracks ι T p.reverse = (expandTracks ι T p).reverse := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons x t ih =>
    cases t with
    | nil => intro _; rfl
    | cons y rest =>
      intro hch
      have hxy : J.Adj x y := hch.rel_head
      have htail : List.IsChain J.Adj (y :: rest) := hch.tail
      have hrevch : List.IsChain J.Adj ((y :: rest).reverse ++ [x]) := by
        have := isChain_reverse_symm (fun a b (h : J.Adj a b) => h.symm) hch
        simpa only [List.reverse_cons] using this
      have hlast : ((y :: rest).reverse).getLast? = some y := by
        rw [List.getLast?_reverse]; rfl
      rw [List.reverse_cons, expandTracks_append_singleton hS _ y x hlast hrevch, ih htail,
        expandTracks_cons_cons, List.reverse_append]
      congr 1
      rw [hS.rev x y hxy, List.tail_reverse]

/-! ### (C): composing a datum with a subdivision -/

/-- **(C)** If `J` carries a `K₄`-subdivision datum and `H` is a subdivision of `J`, then `H`
carries a `K₄`-subdivision datum.

Each `K₄`-track `R a b` of `J` is expanded by replacing every `J`-edge along it with the
`H`-track the subdivision attaches to that edge. -/
theorem hasK4Datum_of_subdivision {J : SimpleGraph U} {H : SimpleGraph W}
    (hdat : HasK4Datum J) (hsub : IsSubdivision J H) : HasK4Datum H := by
  obtain ⟨κ, R, hκ, hRtrack, hRlen, hRrev, hRdisj, hRnew⟩ := hdat
  obtain ⟨ι, T, hS⟩ := exists_subdivWitness hsub
  -- basic facts about the `K₄`-tracks of `J`
  have hRchain : ∀ a b : Fin 4, a ≠ b → List.IsChain J.Adj (R a b) := fun a b h =>
    List.isChain_iff_getElem.mpr (hRtrack a b h).1.2.2
  have hRnd : ∀ a b : Fin 4, a ≠ b → (R a b).Nodup := fun a b h => (hRtrack a b h).1.2.1
  have hRne : ∀ a b : Fin 4, a ≠ b → R a b ≠ [] := fun a b h => (hRtrack a b h).1.1
  have hRhead : ∀ a b : Fin 4, a ≠ b → (R a b).head? = some (κ a) := fun a b h =>
    (hRtrack a b h).2.1
  have hRlast : ∀ a b : Fin 4, a ≠ b → (R a b).getLast? = some (κ b) := fun a b h =>
    (hRtrack a b h).2.2
  have hRlen2 : ∀ a b : Fin 4, a ≠ b → 2 ≤ (R a b).length := by
    intro a b h
    have h1 := hRlen a b h
    simp only [trackLength] at h1
    omega
  -- basic facts about the expansions
  have hEhead : ∀ a b : Fin 4, a ≠ b →
      (expandTracks ι T (R a b)).head? = some (ι (κ a)) := by
    intro a b h
    rw [expandTracks_head? hS (R a b) (hRchain a b h), hRhead a b h]; rfl
  have hElast : ∀ a b : Fin 4, a ≠ b →
      (expandTracks ι T (R a b)).getLast? = some (ι (κ b)) := by
    intro a b h
    rw [expandTracks_getLast? hS (R a b) (hRchain a b h), hRlast a b h]; rfl
  have hEnd : ∀ a b : Fin 4, a ≠ b → (expandTracks ι T (R a b)).Nodup := fun a b h =>
    expandTracks_nodup hS (R a b) (hRchain a b h) (hRnd a b h)
  -- two distinct `K₄`-edges never have a common vertex outside the branch vertices
  have key : ∀ a b a' b' : Fin 4, a ≠ b → a' ≠ b' → s(a, b) ≠ s(a', b') →
      ∀ x y : U, x ≠ y → x ∈ R a b → y ∈ R a b → x ∈ R a' b' → y ∈ R a' b' → False := by
    intro a b a' b' hab ha'b' hs x y hxy hx hy hx' hy'
    have hxi : x ∉ trackInterior (R a b) := fun hc => hRdisj a b a' b' hab ha'b' hs x hc hx'
    have hyi : y ∉ trackInterior (R a b) := fun hc => hRdisj a b a' b' hab ha'b' hs y hc hy'
    have hxi' : x ∉ trackInterior (R a' b') := fun hc =>
      hRdisj a' b' a b ha'b' hab (Ne.symm hs) x hc hx
    have hyi' : y ∉ trackInterior (R a' b') := fun hc =>
      hRdisj a' b' a b ha'b' hab (Ne.symm hs) y hc hy
    have hx1 := mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hx hxi
    have hy1 := mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hy hyi
    have hx2 := mem_ends_of_mem (hRhead a' b' ha'b') (hRlast a' b' ha'b') hx' hxi'
    have hy2 := mem_ends_of_mem (hRhead a' b' ha'b') (hRlast a' b' ha'b') hy' hyi'
    have hc1 : (x = κ a ∧ y = κ b) ∨ (x = κ b ∧ y = κ a) := by
      rcases hx1 with h1 | h1 <;> rcases hy1 with h2 | h2
      · exact absurd (h1.trans h2.symm) hxy
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hxy
    have hc2 : (x = κ a' ∧ y = κ b') ∨ (x = κ b' ∧ y = κ a') := by
      rcases hx2 with h1 | h1 <;> rcases hy2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hxy
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hxy
    apply hs
    rcases hc1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hc2 with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hκ (e1.symm.trans e3), hκ (e2.symm.trans e4)⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hκ (e1.symm.trans e3), hκ (e2.symm.trans e4)⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hκ (e2.symm.trans e4), hκ (e1.symm.trans e3)⟩)
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hκ (e2.symm.trans e4), hκ (e1.symm.trans e3)⟩)
  -- consequently, distinct `K₄`-edges use disjoint sets of `J`-edges
  have hedge : ∀ a b a' b' : Fin 4, a ≠ b → a' ≠ b' → s(a, b) ≠ s(a', b') →
      ∀ x y x' y' : U, J.Adj x y → x ∈ R a b → y ∈ R a b → x' ∈ R a' b' → y' ∈ R a' b' →
        s(x, y) ≠ s(x', y') := by
    intro a b a' b' hab ha'b' hs x y x' y' hxy hx hy hx' hy' heq
    rcases Sym2.eq_iff.mp heq with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · exact key a b a' b' hab ha'b' hs x y hxy.ne hx hy
        (by rw [p1]; exact hx') (by rw [p2]; exact hy')
    · exact key a b a' b' hab ha'b' hs x y hxy.ne hx hy
        (by rw [p1]; exact hy') (by rw [p2]; exact hx')
  refine ⟨fun a => ι (κ a), fun a b => expandTracks ι T (R a b), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- injectivity of the composed embedding
    intro a b hab
    exact hκ (hS.inj hab)
  · -- the expansion is a track with the right ends
    intro a b hab
    show IsTrackFrom H (expandTracks ι T (R a b)) (ι (κ a)) (ι (κ b))
    refine ⟨⟨expandTracks_ne_nil hS (hRchain a b hab) (hRne a b hab), hEnd a b hab, ?_⟩,
      hEhead a b hab, hElast a b hab⟩
    exact List.isChain_iff_getElem.mp (expandTracks_isChain hS (R a b) (hRchain a b hab))
  · -- the expansion has at least one edge
    intro a b hab
    show 1 ≤ trackLength (expandTracks ι T (R a b))
    have := two_le_expandTracks_length hS (hRchain a b hab) (hRlen2 a b hab)
    simp only [trackLength]
    omega
  · -- reversing the `K₄`-edge reverses the expansion
    intro a b hab
    show expandTracks ι T (R b a) = (expandTracks ι T (R a b)).reverse
    rw [hRrev a b hab]
    exact expandTracks_reverse hS (R a b) (hRchain a b hab)
  · -- interiors of the expansions of distinct `K₄`-edges are disjoint from the other expansion
    intro a b a' b' hab ha'b' hs
    show ∀ w ∈ trackInterior (expandTracks ι T (R a b)), w ∉ expandTracks ι T (R a' b')
    intro w hw hmem
    have hwmem : w ∈ expandTracks ι T (R a b) := mem_of_mem_trackInterior hw
    have hwa : w ≠ ι (κ a) :=
      ne_head_of_mem_trackInterior (hEnd a b hab) (hEhead a b hab) hw
    have hwb : w ≠ ι (κ b) :=
      ne_getLast_of_mem_trackInterior (hEnd a b hab) (hElast a b hab) hw
    rcases mem_expandTracks hS (R a b) (hRchain a b hab) w hwmem with
      ⟨x, hxR, hxeq⟩ | ⟨x, y, hxR, hyR, hxy, hint⟩
    · rcases mem_expandTracks hS (R a' b') (hRchain a' b' ha'b') w hmem with
        ⟨x', hx'R, hx'eq⟩ | ⟨x', y', hx'R, hy'R, hx'y', hint'⟩
      · have hxx' : x = x' := hS.inj (hxeq.symm.trans hx'eq)
        have hxi : x ∉ trackInterior (R a b) := fun hc =>
          hRdisj a b a' b' hab ha'b' hs x hc (by rw [hxx']; exact hx'R)
        rcases mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hxR hxi with h | h
        · exact hwa (by rw [hxeq, h])
        · exact hwb (by rw [hxeq, h])
      · exact hS.new x' y' hx'y' w hint' ⟨x, hxeq.symm⟩
    · rcases mem_expandTracks hS (R a' b') (hRchain a' b' ha'b') w hmem with
        ⟨x', hx'R, hx'eq⟩ | ⟨x', y', hx'R, hy'R, hx'y', hint'⟩
      · exact hS.new x y hxy w hint ⟨x', hx'eq.symm⟩
      · exact hS.disj x y x' y' hxy hx'y'
          (hedge a b a' b' hab ha'b' hs x y x' y' hxy hxR hyR hx'R hy'R) w hint
          (mem_of_mem_trackInterior hint')
  · -- interior vertices of an expansion are not branch vertices
    intro a b hab
    show ∀ w ∈ trackInterior (expandTracks ι T (R a b)), w ∉ Set.range fun c => ι (κ c)
    rintro w hw ⟨c, hc⟩
    have hwmem : w ∈ expandTracks ι T (R a b) := mem_of_mem_trackInterior hw
    have hwa : w ≠ ι (κ a) :=
      ne_head_of_mem_trackInterior (hEnd a b hab) (hEhead a b hab) hw
    have hwb : w ≠ ι (κ b) :=
      ne_getLast_of_mem_trackInterior (hEnd a b hab) (hElast a b hab) hw
    rcases mem_expandTracks hS (R a b) (hRchain a b hab) w hwmem with
      ⟨x, hxR, hxeq⟩ | ⟨x, y, hxR, hyR, hxy, hint⟩
    · have hxc : x = κ c := hS.inj (hxeq.symm.trans hc.symm)
      by_cases hxi : x ∈ trackInterior (R a b)
      · exact hRnew a b hab x hxi ⟨c, hxc.symm⟩
      · rcases mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hxR hxi with h | h
        · exact hwa (by rw [hxeq, h])
        · exact hwb (by rw [hxeq, h])
    · exact hS.new x y hxy w hint ⟨κ c, hc⟩

end Workspace.ProofLemmas.SubdivisionCompose
