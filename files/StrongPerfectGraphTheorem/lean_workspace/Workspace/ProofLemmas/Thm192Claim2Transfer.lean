import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Prisms
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes

/-!
# Transporting the objects of §1 along an induced injection

Every class `F₁, …, F₇` is defined by forbidding *induced subgraphs* of a certain
shape, in `G` or in `Ḡ`.  To know that these classes are inherited by induced
subgraphs, one only has to know that each of the shapes travels along a map that
is injective and *reflects and preserves adjacency*, that is, along an induced
injection.  This module collects those transports once and for all, for a map

`f : W → V` with `hf : Function.Injective f` and
`hadj : ∀ a b, G'.Adj a b ↔ G.Adj (f a) (f b)`,

and the corresponding statement for the complements comes for free
(`compl_adj`), so each shape only has to be transported once even though the
class definitions mention `Ḡ` as well.

Everything here is bookkeeping; nothing corresponds to a step of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm192Claim2Transfer

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} {f : W → V}

section
variable (hf : Function.Injective f) (hadj : ∀ a b : W, G'.Adj a b ↔ G.Adj (f a) (f b))
include hf hadj

/-- An induced injection is an induced injection for the complements too. -/
theorem compl_adj : ∀ a b : W, G'ᶜ.Adj a b ↔ Gᶜ.Adj (f a) (f b) := by
  intro a b
  simp only [SimpleGraph.compl_adj, ne_eq]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun he => hne (hf he), fun hc => h ((hadj a b).mpr hc)⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun he => hne (by rw [he]), fun hc => h ((hadj a b).mp hc)⟩

/-! ### Lists -/

theorem isPathList_map (p : List W) : IsPathList G' p ↔ IsPathList G (p.map f) := by
  constructor
  · rintro ⟨hne, hnd, hp⟩
    refine ⟨by simpa using hne, hnd.map hf, ?_⟩
    intro i j hi hj
    simp only [List.getElem_map]
    rw [← hadj]
    exact hp i j (by simpa using hi) (by simpa using hj)
  · rintro ⟨hne, hnd, hp⟩
    refine ⟨by simpa using hne, hnd.of_map, ?_⟩
    intro i j hi hj
    have hh := hp i j (by simpa using hi) (by simpa using hj)
    simp only [List.getElem_map] at hh
    rw [← hadj] at hh
    exact hh

theorem isHoleList_map (c : List W) : IsHoleList G' c ↔ IsHoleList G (c.map f) := by
  constructor
  · rintro ⟨h4, hnd, hc⟩
    refine ⟨by simpa using h4, hnd.map hf, ?_⟩
    intro i j hi hj
    simp only [List.getElem_map, List.length_map]
    rw [← hadj]
    exact hc i j (by simpa using hi) (by simpa using hj)
  · rintro ⟨h4, hnd, hc⟩
    refine ⟨by simpa using h4, hnd.of_map, ?_⟩
    intro i j hi hj
    have hh := hc i j (by simpa using hi) (by simpa using hj)
    simp only [List.getElem_map, List.length_map] at hh
    rw [← hadj] at hh
    exact hh

theorem head?_map_iff (p : List W) (u : W) :
    p.head? = some u ↔ (p.map f).head? = some (f u) := by
  rw [List.head?_map]
  rcases p with _ | ⟨a, t⟩
  · simp
  · simp only [List.head?_cons, Option.map_some, Option.some.injEq]
    exact ⟨fun h => by rw [h], fun h => hf h⟩

theorem getLast?_map_iff (p : List W) (v : W) :
    p.getLast? = some v ↔ (p.map f).getLast? = some (f v) := by
  rw [List.getLast?_map]
  rcases h : p.getLast? with _ | a
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun hh => by rw [hh], fun hh => hf hh⟩

theorem isPathFrom_map (p : List W) (u v : W) :
    IsPathFrom G' p u v ↔ IsPathFrom G (p.map f) (f u) (f v) :=
  and_congr (isPathList_map hf hadj p)
    (and_congr (head?_map_iff hf hadj p u) (getLast?_map_iff hf hadj p v))

/-! ### Completeness -/

theorem vertexComplete_map (v : W) (Y : Set W) :
    VertexComplete G' v Y ↔ VertexComplete G (f v) (f '' Y) := by
  constructor
  · rintro h u ⟨w, hw, rfl⟩
    exact (hadj v w).mp (h w hw)
  · intro h w hw
    exact (hadj v w).mpr (h (f w) ⟨w, hw, rfl⟩)

theorem edgeComplete_map (u v : W) (Y : Set W) :
    EdgeComplete G' Y u v ↔ EdgeComplete G (f '' Y) (f u) (f v) := by
  unfold EdgeComplete
  rw [hadj, vertexComplete_map hf hadj, vertexComplete_map hf hadj]

/-! ### Connectedness -/

/-- The induced injection restricts to an isomorphism from `G'|Y` onto `G|f(Y)`. -/
noncomputable def imgIso (Y : Set W) : G'.induce Y ≃g G.induce (f '' Y) := by
  refine ⟨Equiv.ofBijective (fun w => ⟨f w.1, ⟨w.1, w.2, rfl⟩⟩) ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  · rintro ⟨v, w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  · intro a b
    show G.Adj (f a.1) (f b.1) ↔ G'.Adj a.1 b.1
    exact (hadj a.1 b.1).symm

theorem connectedSet_map (Y : Set W) :
    ConnectedSet G' Y ↔ ConnectedSet G (f '' Y) := by
  unfold ConnectedSet
  constructor
  · intro h u v
    obtain ⟨u', rfl⟩ := (imgIso hf hadj Y).surjective u
    obtain ⟨v', rfl⟩ := (imgIso hf hadj Y).surjective v
    exact ((h u' v').map (imgIso hf hadj Y).toHom)
  · intro h u v
    have := h ((imgIso hf hadj Y) u) ((imgIso hf hadj Y) v)
    have h2 := this.map (imgIso hf hadj Y).symm.toHom
    simpa using h2

theorem anticonnectedSet_map (Y : Set W) :
    AnticonnectedSet G' Y ↔ AnticonnectedSet G (f '' Y) :=
  connectedSet_map hf (compl_adj hf hadj) Y

/-! ### Wheels -/

theorem isWheel_map {C : List W} {Y : Set W} (h : IsWheel G' C Y) :
    IsWheel G (C.map f) (f '' Y) := by
  obtain ⟨⟨hhole, hlen⟩, ⟨hne, hanti, hdisj⟩, a, b, c, d, ha, hb, hc, hd, hab, hcd,
    hac, had, hbc, hbd⟩ := h
  refine ⟨⟨(isHoleList_map hf hadj C).mp hhole, by simpa [holeLength] using hlen⟩,
    ⟨hne.image f, (anticonnectedSet_map hf hadj Y).mp hanti, ?_⟩,
    f a, f b, f c, f d, List.mem_map_of_mem ha, List.mem_map_of_mem hb,
    List.mem_map_of_mem hc, List.mem_map_of_mem hd,
    (edgeComplete_map hf hadj a b Y).mp hab, (edgeComplete_map hf hadj c d Y).mp hcd,
    fun h => hac (hf h), fun h => had (hf h), fun h => hbc (hf h), fun h => hbd (hf h)⟩
  rintro v hv ⟨w, hw, hwv⟩
  obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
  exact hdisj v' hv' (by rwa [hf hwv] at hw)

/-- A block of a mapped list is a mapped block. -/
theorem prefix_map_pull {M : List W} {T : List V} (h : T <+: M.map f) :
    ∃ T' : List W, T'.map f = T ∧ T' <+: M := by
  refine ⟨M.take T.length, ?_, List.take_prefix _ _⟩
  rw [List.map_take, ← List.prefix_iff_eq_take.mp h]

theorem isSegment_map {C : List W} {Y : Set W} {S : List W} (h : IsSegment G' C Y S) :
    IsSegment G (C.map f) (f '' Y) (S.map f) := by
  obtain ⟨⟨hpath, ⟨k, hk⟩, hmem⟩, hmax⟩ := h
  refine ⟨⟨(isPathList_map hf hadj S).mp hpath, ⟨k, ?_⟩, ?_⟩, ?_⟩
  · rw [← List.map_rotate]
    rcases hk with hk | hk
    · exact Or.inl (hk.map f)
    · exact Or.inr (by rw [← List.map_reverse]; exact hk.map f)
  · intro w hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact ⟨List.mem_map_of_mem (hmem w' hw').1,
      (vertexComplete_map hf hadj w' Y).mp (hmem w' hw').2⟩
  · intro T hT hTblock hTmem hST
    obtain ⟨k', hk'⟩ := hTblock
    -- pull `T` back along `f`
    obtain ⟨T', hT'eq, hT'pre⟩ : ∃ T' : List W, T'.map f = T ∧
        (T' <+: C.rotate k' ∨ T'.reverse <+: C.rotate k') := by
      rcases hk' with hk' | hk'
      · rw [← List.map_rotate] at hk'
        obtain ⟨T', h1, h2⟩ := prefix_map_pull hf hadj hk'
        exact ⟨T', h1, Or.inl h2⟩
      · rw [← List.map_rotate] at hk'
        obtain ⟨T', h1, h2⟩ := prefix_map_pull hf hadj hk'
        refine ⟨T'.reverse, by rw [List.map_reverse, h1, List.reverse_reverse], Or.inr ?_⟩
        rwa [List.reverse_reverse]
    subst hT'eq
    have hT'path : IsPathList G' T' := (isPathList_map hf hadj T').mpr hT
    have hT'mem : ∀ w ∈ T', w ∈ C ∧ VertexComplete G' w Y := by
      intro w hw
      obtain ⟨h1, h2⟩ := hTmem (f w) (List.mem_map_of_mem hw)
      obtain ⟨w', hw', hwe⟩ := List.mem_map.mp h1
      exact ⟨by rwa [hf hwe] at hw', (vertexComplete_map hf hadj w Y).mpr h2⟩
    have hST' : ∀ w ∈ S, w ∈ T' := by
      intro w hw
      obtain ⟨w', hw', hwe⟩ := List.mem_map.mp (hST (f w) (List.mem_map_of_mem hw))
      rwa [hf hwe] at hw'
    intro w hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact List.mem_map_of_mem (hmax T' hT'path ⟨k', hT'pre⟩ hT'mem hST' w' hw')

theorem isOddWheel_map {C : List W} {Y : Set W} (h : IsOddWheel G' C Y) :
    IsOddWheel G (C.map f) (f '' Y) := by
  obtain ⟨hw, S, hS, hodd⟩ := h
  exact ⟨isWheel_map hf hadj hw, S.map f, isSegment_map hf hadj hS,
    by simpa [pathLength] using hodd⟩

/-! ### Prisms and the double diamond -/

theorem formPrism_map {a b : Fin 3 → W} {P₁ P₂ P₃ : List W}
    (h : FormPrism G' a b P₁ P₂ P₃) :
    FormPrism G (fun i => f (a i)) (fun i => f (b i)) (P₁.map f) (P₂.map f) (P₃.map f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨fun i j hij => (hadj _ _).mp (h1 i j hij),
    fun i j hij => (hadj _ _).mp (h2 i j hij),
    fun i j he => h3 i j (hf he),
    (isPathFrom_map hf hadj _ _ _).mp h4, (isPathFrom_map hf hadj _ _ _).mp h5,
    (isPathFrom_map hf hadj _ _ _).mp h6, ?_, ?_, ?_⟩
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
    rw [← hadj, h7 u' hu' v' hv']
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact Or.inl ⟨by rw [h], by rw [h']⟩
      · exact Or.inr ⟨by rw [h], by rw [h']⟩
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact Or.inl ⟨hf h, hf h'⟩
      · exact Or.inr ⟨hf h, hf h'⟩
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
    rw [← hadj, h8 u' hu' v' hv']
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact Or.inl ⟨by rw [h], by rw [h']⟩
      · exact Or.inr ⟨by rw [h], by rw [h']⟩
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact Or.inl ⟨hf h, hf h'⟩
      · exact Or.inr ⟨hf h, hf h'⟩
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
    rw [← hadj, h9 u' hu' v' hv']
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact Or.inl ⟨by rw [h], by rw [h']⟩
      · exact Or.inr ⟨by rw [h], by rw [h']⟩
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact Or.inl ⟨hf h, hf h'⟩
      · exact Or.inr ⟨hf h, hf h'⟩

theorem isLongPrism_map {a b : Fin 3 → W} {P₁ P₂ P₃ : List W}
    (h : IsLongPrism G' a b P₁ P₂ P₃) :
    IsLongPrism G (fun i => f (a i)) (fun i => f (b i))
      (P₁.map f) (P₂.map f) (P₃.map f) := by
  refine ⟨formPrism_map hf hadj h.1, ?_⟩
  simpa [pathLength] using h.2

theorem isEvenPrism_map {a b : Fin 3 → W} {P₁ P₂ P₃ : List W}
    (h : IsEvenPrism G' a b P₁ P₂ P₃) :
    IsEvenPrism G (fun i => f (a i)) (fun i => f (b i))
      (P₁.map f) (P₂.map f) (P₃.map f) := by
  exact ⟨formPrism_map hf hadj h.1, by simpa [pathLength] using h.2.1,
    by simpa [pathLength] using h.2.2.1, by simpa [pathLength] using h.2.2.2⟩

theorem isDoubleDiamond_map {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : W}
    (h : IsDoubleDiamond G' a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄) :
    IsDoubleDiamond G (f a₁) (f a₂) (f a₃) (f a₄) (f b₁) (f b₂) (f b₃) (f b₄) := by
  obtain ⟨hnd, hA, hB, hAB, hno⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : ([a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄].map f).Nodup := hnd.map hf
    simpa using this
  · exact ⟨(hadj _ _).mp hA.1, (hadj _ _).mp hA.2.1, (hadj _ _).mp hA.2.2.1,
      (hadj _ _).mp hA.2.2.2.1, (hadj _ _).mp hA.2.2.2.2.1,
      fun hc => hA.2.2.2.2.2 ((hadj _ _).mpr hc)⟩
  · exact ⟨(hadj _ _).mp hB.1, (hadj _ _).mp hB.2.1, (hadj _ _).mp hB.2.2.1,
      (hadj _ _).mp hB.2.2.2.1, (hadj _ _).mp hB.2.2.2.2.1,
      fun hc => hB.2.2.2.2.2 ((hadj _ _).mpr hc)⟩
  · exact ⟨(hadj _ _).mp hAB.1, (hadj _ _).mp hAB.2.1, (hadj _ _).mp hAB.2.2.1,
      (hadj _ _).mp hAB.2.2.2⟩
  · obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hno
    exact ⟨fun hc => n1 ((hadj _ _).mpr hc), fun hc => n2 ((hadj _ _).mpr hc),
      fun hc => n3 ((hadj _ _).mpr hc), fun hc => n4 ((hadj _ _).mpr hc),
      fun hc => n5 ((hadj _ _).mpr hc), fun hc => n6 ((hadj _ _).mpr hc),
      fun hc => n7 ((hadj _ _).mpr hc), fun hc => n8 ((hadj _ _).mpr hc),
      fun hc => n9 ((hadj _ _).mpr hc), fun hc => n10 ((hadj _ _).mpr hc),
      fun hc => n11 ((hadj _ _).mpr hc), fun hc => n12 ((hadj _ _).mpr hc)⟩

end

end Workspace.ProofLemmas.Thm192Claim2Transfer
