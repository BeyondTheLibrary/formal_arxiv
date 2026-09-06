import Workspace.ProofLemmas.TwoConnectedDisjointPaths
import Workspace.ProofLemmas.Connectivity58CycleBuild
import Workspace.ProofLemmas.TrackSlice

/-!
# Dividing a vertex into two adjacent vertices, and the two paths of 5.8 (6)

PAPER (proof of 5.8 (6), printed p. 28): *"(To see this, divide `u` into two adjacent vertices,
one incident with the edges in `A` and the other with those in `B`, and use Menger's theorem to
deduce that there are two vertex-disjoint paths between these two vertices and `{v₁,v₂}`.)"*

This file carries out that sentence literally, in the host graph `H` (not in its skeleton).
The vertex `u` of `H` is divided into `u_A`, which keeps the edges of `H` at `u` running to
`A`, and `u_B`, which keeps those running to `B = N(u) \ A`; the two are made adjacent.  Two
further vertices are added to turn *"two vertex-disjoint paths between `{u_A,u_B}` and
`{v₁,v₂}`"* into the two internally disjoint tracks between a single pair of vertices that
`TwoConnectedDisjointPaths.exists_two_tracks` delivers: a source joined to `u_A` and `u_B`, and
a sink joined to `v₁` and `v₂`.  (This super-source/super-sink reduction is the standard way
Menger's theorem is applied to a pair of vertex sets.)

The graph so built has no cutvertex as soon as `H` has none and both `A` and `B` meet `N(u)`:
deleting `u_A` leaves `H - u` with `u_B` hanging on a `B`-edge, deleting any other vertex `z`
leaves the division of the connected graph `H - z`, and the two added vertices are attached at
two places each.  Its two tracks from source to sink therefore leave the source one through
`u_A` and one through `u_B`, so reading them back in `H` gives two paths out of `u`, meeting
only at `u`, one leaving along an edge into `A` and one along an edge into `B`, and ending at
`v₁` and `v₂` in one order or the other.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.SplitVertexTwoPaths

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.TwoConnectedDisjointPaths

/-- The three vertices added to `H`: the second half `u_B` of the divided vertex, the
super-source and the super-sink. -/
inductive Extra
  | uB
  | src
  | snk
  deriving DecidableEq

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The vertices of the divided graph: those of `H` (the vertex `u` itself playing the role of
`u_A`) together with the three added ones. -/
abbrev SV (W : Type*) : Type _ := W ⊕ Extra

/-- Which vertices of `H` each added vertex is joined to. -/
def extraAdj (H : SimpleGraph W) (u : W) (A : Set W) (v₁ v₂ : W) : Extra → W → Prop
  | Extra.uB, p => p = u ∨ (H.Adj u p ∧ p ∉ A)
  | Extra.src, p => p = u
  | Extra.snk, p => p = v₁ ∨ p = v₂

/-- Adjacency of the divided graph. -/
def splitAdj (H : SimpleGraph W) (u : W) (A : Set W) (v₁ v₂ : W) : SV W → SV W → Prop
  | Sum.inl p, Sum.inl r => H.Adj p r ∧ (p = u → r ∈ A) ∧ (r = u → p ∈ A)
  | Sum.inl p, Sum.inr k => extraAdj H u A v₁ v₂ k p
  | Sum.inr k, Sum.inl p => extraAdj H u A v₁ v₂ k p
  | Sum.inr k, Sum.inr l =>
      (k = Extra.uB ∧ l = Extra.src) ∨ (k = Extra.src ∧ l = Extra.uB)

/-- **The divided graph.**  `H` with `u` divided into `u_A` (the vertex `u` itself, keeping the
edges into `A`) and `u_B` (keeping those into `B`), the two joined by an edge, plus the source
joined to both halves and the sink joined to `v₁` and `v₂`. -/
def splitGraph (H : SimpleGraph W) (u : W) (A : Set W) (v₁ v₂ : W) : SimpleGraph (SV W) where
  Adj := splitAdj H u A v₁ v₂
  symm := by
    rintro (p | k) (r | l) h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩
    · exact h
    · exact h
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
  loopless := by
    constructor
    rintro (p | k) h
    · exact h.1.ne rfl
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact absurd (h1.symm.trans h2) (by decide)

variable {H : SimpleGraph W} {u v₁ v₂ : W} {A : Set W}

theorem adj_inl_inl {p r : W} :
    (splitGraph H u A v₁ v₂).Adj (Sum.inl p) (Sum.inl r) ↔
      (H.Adj p r ∧ (p = u → r ∈ A) ∧ (r = u → p ∈ A)) := Iff.rfl

theorem adj_inl_inr {p : W} {k : Extra} :
    (splitGraph H u A v₁ v₂).Adj (Sum.inl p) (Sum.inr k) ↔
      extraAdj H u A v₁ v₂ k p := Iff.rfl

theorem adj_inr_inl {p : W} {k : Extra} :
    (splitGraph H u A v₁ v₂).Adj (Sum.inr k) (Sum.inl p) ↔
      extraAdj H u A v₁ v₂ k p := Iff.rfl

theorem adj_inr_inr {k l : Extra} :
    (splitGraph H u A v₁ v₂).Adj (Sum.inr k) (Sum.inr l) ↔
      ((k = Extra.uB ∧ l = Extra.src) ∨ (k = Extra.src ∧ l = Extra.uB)) := Iff.rfl

theorem extra_ne {k l : Extra} (h : k ≠ l) : (Sum.inr k : SV W) ≠ Sum.inr l := by
  intro hc; exact h (Sum.inr_injective hc)

/-! ### The divided graph has no cutvertex -/

/-- Walks of `H` avoiding one vertex lift to the divided graph: an edge at `u` that the
division has moved to `u_B` is replaced by the two-edge detour through `u_B`. -/
private theorem lift_reach
    (hcut : ∀ z : W, ConnectedSet H ({z}ᶜ : Set W))
    {X : Set (SV W)} (w : W)
    (hXinl : ∀ z : W, z ≠ w → (Sum.inl z : SV W) ∈ X)
    (huB : w = u ∨ (Sum.inr Extra.uB : SV W) ∈ X)
    {p r : W} (hp : p ≠ w) (hr : r ≠ w) :
    RchIn (splitGraph H u A v₁ v₂) X (Sum.inl p) (Sum.inl r) := by
  classical
  have hne : ∀ z : ↥(({w} : Set W)ᶜ), (z : W) ≠ w := by
    intro z hh
    exact z.2 (Set.mem_singleton_iff.mpr hh)
  have hpm : p ∈ ({w} : Set W)ᶜ := fun hh => hp (Set.mem_singleton_iff.mp hh)
  have hrm : r ∈ ({w} : Set W)ᶜ := fun hh => hr (Set.mem_singleton_iff.mp hh)
  obtain ⟨wk⟩ := hcut w ⟨p, hpm⟩ ⟨r, hrm⟩
  refine rchIn_of_walk (K := H.induce (({w} : Set W)ᶜ))
    (fun z => (Sum.inl z.val : SV W))
    (fun z => hXinl z.val (hne z)) ?_ wk
  intro z z' hzz'
  have hadj : H.Adj (z : W) (z' : W) := hzz'
  have hzX : (Sum.inl (z : W) : SV W) ∈ X := hXinl _ (hne z)
  have hz'X : (Sum.inl (z' : W) : SV W) ∈ X := hXinl _ (hne z')
  by_cases hzu : (z : W) = u
  · have hz'u : (z' : W) ≠ u := fun hh => hadj.ne (hzu.trans hh.symm)
    by_cases hz'A : (z' : W) ∈ A
    · exact RchIn.of_adj hzX hz'X ⟨hadj, fun _ => hz'A, fun hh => absurd hh hz'u⟩
    · have huBX : (Sum.inr Extra.uB : SV W) ∈ X := by
        rcases huB with hwu | hh
        · exact absurd (hzu.trans hwu.symm) (hne z)
        · exact hh
      refine (RchIn.of_adj hzX huBX ?_).trans (RchIn.of_adj huBX hz'X ?_)
      · exact Or.inl hzu
      · exact Or.inr ⟨hzu ▸ hadj, hz'A⟩
  · by_cases hz'u : (z' : W) = u
    · by_cases hzA : (z : W) ∈ A
      · exact RchIn.of_adj hzX hz'X ⟨hadj, fun hh => absurd hh hzu, fun _ => hzA⟩
      · have huBX : (Sum.inr Extra.uB : SV W) ∈ X := by
          rcases huB with hwu | hh
          · exact absurd (hz'u.trans hwu.symm) (hne z')
          · exact hh
        refine (RchIn.of_adj hzX huBX ?_).trans (RchIn.of_adj huBX hz'X ?_)
        · exact Or.inr ⟨hz'u ▸ hadj.symm, hzA⟩
        · exact Or.inl hz'u
    · exact RchIn.of_adj hzX hz'X
        ⟨hadj, fun hh => absurd hh hzu, fun hh => absurd hh hz'u⟩

/-- **The divided graph has no cutvertex.** -/
theorem split_nocut
    (hcut : ∀ z : W, ConnectedSet H ({z}ᶜ : Set W))
    (hv : v₁ ≠ v₂) (hu1 : u ≠ v₁) (hu2 : u ≠ v₂)
    (ha : ∃ x, H.Adj u x ∧ x ∈ A) (hb : ∃ x, H.Adj u x ∧ x ∉ A) :
    NoCutvertex (splitGraph H u A v₁ v₂) := by
  classical
  obtain ⟨a₀, ha₀adj, ha₀A⟩ := ha
  obtain ⟨b₀, hb₀adj, hb₀A⟩ := hb
  have ha₀u : a₀ ≠ u := ha₀adj.ne'
  have hb₀u : b₀ ≠ u := hb₀adj.ne'
  intro Z Pv Rv hPZ hRZ
  set Γ := splitGraph H u A v₁ v₂ with hΓ
  set X : Set (SV W) := ({Z}ᶜ : Set (SV W)) with hX
  have hmemX : ∀ V : SV W, V ≠ Z → V ∈ X := fun V h => h
  suffices hkey : ∃ α : SV W, ∀ V : SV W, V ≠ Z → RchIn Γ X V α by
    obtain ⟨α, hk⟩ := hkey
    exact (hk Pv hPZ).trans (hk Rv hRZ).symm
  -- the source and the sink are attached in two places each
  have hsrcuB : Γ.Adj (Sum.inr Extra.src) (Sum.inr Extra.uB) := Or.inr ⟨rfl, rfl⟩
  have hsrcu : Γ.Adj (Sum.inr Extra.src) (Sum.inl u) := rfl
  have huuB : Γ.Adj (Sum.inl u) (Sum.inr Extra.uB) := Or.inl rfl
  have hsnk₁ : Γ.Adj (Sum.inr Extra.snk) (Sum.inl v₁) := Or.inl rfl
  have hsnk₂ : Γ.Adj (Sum.inr Extra.snk) (Sum.inl v₂) := Or.inr rfl
  have hb₀uB : Γ.Adj (Sum.inl b₀) (Sum.inr Extra.uB) := Or.inr ⟨hb₀adj, hb₀A⟩
  have ha₀u' : Γ.Adj (Sum.inl a₀) (Sum.inl u) :=
    ⟨ha₀adj.symm, fun hh => absurd hh ha₀u, fun _ => ha₀A⟩
  rcases Z with w | e
  · -- a vertex of `H` is deleted
    have hXinl : ∀ z : W, z ≠ w → (Sum.inl z : SV W) ∈ X := by
      intro z hz
      exact hmemX _ (by simpa using hz)
    have huBX : (Sum.inr Extra.uB : SV W) ∈ X := hmemX _ (by simp)
    have hsrcX : (Sum.inr Extra.src : SV W) ∈ X := hmemX _ (by simp)
    refine ⟨Sum.inr Extra.uB, ?_⟩
    intro V hV
    have step : ∀ p : W, p ≠ w → RchIn Γ X (Sum.inl p) (Sum.inr Extra.uB) := by
      intro p hp
      by_cases hwu : w = u
      · subst hwu
        refine (lift_reach hcut w hXinl (Or.inl rfl) hp hb₀u).trans ?_
        exact RchIn.of_adj (hXinl _ hb₀u) huBX hb₀uB
      · refine (lift_reach hcut w hXinl (Or.inr huBX) hp (fun hh => hwu hh.symm)).trans ?_
        exact RchIn.of_adj (hXinl _ (fun hh => hwu hh.symm)) huBX huuB
    rcases V with p | k
    · exact step p (by simpa using hV)
    · match k with
      | Extra.uB => exact RchIn.refl huBX
      | Extra.src => exact RchIn.of_adj hsrcX huBX hsrcuB
      | Extra.snk =>
        have hsnkX : (Sum.inr Extra.snk : SV W) ∈ X := hmemX _ (by simp)
        by_cases h1 : v₁ = w
        · have h2 : v₂ ≠ w := fun hh => hv (h1.trans hh.symm)
          exact (RchIn.of_adj hsnkX (hXinl _ h2) hsnk₂).trans (step v₂ h2)
        · exact (RchIn.of_adj hsnkX (hXinl _ h1) hsnk₁).trans (step v₁ h1)
  · -- one of the three added vertices is deleted
    have hXinl : ∀ z : W, (Sum.inl z : SV W) ∈ X := by
      intro z; exact hmemX _ (by simp)
    match e with
    | Extra.uB =>
      refine ⟨Sum.inl u, ?_⟩
      intro V hV
      have step : ∀ p : W, RchIn Γ X (Sum.inl p) (Sum.inl u) := by
        intro p
        by_cases hp : p = u
        · exact hp ▸ RchIn.refl (hXinl p)
        · refine (lift_reach hcut u (fun z _ => hXinl z) (Or.inl rfl) hp ha₀u).trans ?_
          exact RchIn.of_adj (hXinl a₀) (hXinl u) ha₀u'
      rcases V with p | k
      · exact step p
      · match k with
        | Extra.uB => exact absurd rfl hV
        | Extra.src =>
          exact RchIn.of_adj (hmemX _ (extra_ne (by decide))) (hXinl u) hsrcu
        | Extra.snk =>
          exact (RchIn.of_adj (hmemX _ (extra_ne (by decide))) (hXinl v₁) hsnk₁).trans
            (step v₁)
    | Extra.src =>
      have huBX : (Sum.inr Extra.uB : SV W) ∈ X := hmemX _ (extra_ne (by decide))
      refine ⟨Sum.inr Extra.uB, ?_⟩
      intro V hV
      have step : ∀ p : W, RchIn Γ X (Sum.inl p) (Sum.inr Extra.uB) := by
        intro p
        by_cases hp : p = u
        · exact hp ▸ RchIn.of_adj (hXinl u) huBX huuB
        · refine (lift_reach hcut u (fun z _ => hXinl z) (Or.inl rfl) hp hb₀u).trans ?_
          exact RchIn.of_adj (hXinl b₀) huBX hb₀uB
      rcases V with p | k
      · exact step p
      · match k with
        | Extra.uB => exact RchIn.refl huBX
        | Extra.src => exact absurd rfl hV
        | Extra.snk =>
          exact (RchIn.of_adj (hmemX _ (extra_ne (by decide))) (hXinl v₁) hsnk₁).trans
            (step v₁)
    | Extra.snk =>
      have huBX : (Sum.inr Extra.uB : SV W) ∈ X := hmemX _ (extra_ne (by decide))
      refine ⟨Sum.inr Extra.uB, ?_⟩
      intro V hV
      have step : ∀ p : W, RchIn Γ X (Sum.inl p) (Sum.inr Extra.uB) := by
        intro p
        by_cases hp : p = u
        · exact hp ▸ RchIn.of_adj (hXinl u) huBX huuB
        · refine (lift_reach hcut u (fun z _ => hXinl z) (Or.inl rfl) hp hb₀u).trans ?_
          exact RchIn.of_adj (hXinl b₀) huBX hb₀uB
      rcases V with p | k
      · exact step p
      · match k with
        | Extra.uB => exact RchIn.refl huBX
        | Extra.src =>
          exact RchIn.of_adj (hmemX _ (extra_ne (by decide))) huBX hsrcuB
        | Extra.snk => exact absurd rfl hV

/-! ### Every vertex of the divided graph has two distinct neighbours -/

private theorem pick_ne {Y : Type*} {Γ : SimpleGraph Y} {x z₁ z₂ Yv : Y} (hne : z₁ ≠ z₂)
    (h1 : Γ.Adj x z₁) (h2 : Γ.Adj x z₂) : ∃ p, Γ.Adj x p ∧ p ≠ Yv := by
  by_cases hh : z₁ = Yv
  · exact ⟨z₂, h2, fun hc => hne (hh.trans hc.symm)⟩
  · exact ⟨z₁, h1, hh⟩

theorem split_hdeg
    (hdeg2 : ∀ z : W, 2 ≤ (H.neighborSet z).ncard)
    (hv : v₁ ≠ v₂)
    (ha : ∃ x, H.Adj u x ∧ x ∈ A) (hb : ∃ x, H.Adj u x ∧ x ∉ A) :
    ∀ Xv Yv : SV W, ∃ p, (splitGraph H u A v₁ v₂).Adj Xv p ∧ p ≠ Yv := by
  classical
  obtain ⟨a₀, ha₀adj, ha₀A⟩ := ha
  obtain ⟨b₀, hb₀adj, hb₀A⟩ := hb
  have ha₀u : a₀ ≠ u := ha₀adj.ne'
  have hb₀u : b₀ ≠ u := hb₀adj.ne'
  intro Xv Yv
  rcases Xv with p | k
  · by_cases hp : p = u
    · subst hp
      refine pick_ne (z₁ := (Sum.inr Extra.uB : SV W)) (z₂ := (Sum.inr Extra.src : SV W))
        (extra_ne (by decide)) (Or.inl rfl) rfl
    · -- a vertex of `H` other than the divided one keeps its two neighbours
      have hnt : (H.neighborSet p).Nontrivial :=
        Set.one_lt_ncard_iff_nontrivial.mp (by have := hdeg2 p; omega)
      obtain ⟨y₁, hy₁, y₂, hy₂, hyne⟩ := hnt
      have hnbr : ∀ y : W, H.Adj p y →
          ∃ z : SV W, (splitGraph H u A v₁ v₂).Adj (Sum.inl p) z ∧
            (y ≠ u → z = Sum.inl y) ∧
            (y = u → z = Sum.inl u ∨ z = Sum.inr Extra.uB) := by
        intro y hy
        by_cases hyu : y = u
        · subst hyu
          by_cases hpA : p ∈ A
          · exact ⟨Sum.inl y, ⟨hy, fun hh => absurd hh hp, fun _ => hpA⟩,
              fun hh => absurd rfl hh, fun _ => Or.inl rfl⟩
          · exact ⟨Sum.inr Extra.uB, Or.inr ⟨hy.symm, hpA⟩,
              fun hh => absurd rfl hh, fun _ => Or.inr rfl⟩
        · exact ⟨Sum.inl y, ⟨hy, fun hh => absurd hh hp, fun hh => absurd hh hyu⟩,
            fun _ => rfl, fun hh => absurd hh hyu⟩
      obtain ⟨z₁, hz₁adj, hz₁ne, hz₁u⟩ := hnbr y₁ hy₁
      obtain ⟨z₂, hz₂adj, hz₂ne, hz₂u⟩ := hnbr y₂ hy₂
      refine pick_ne ?_ hz₁adj hz₂adj
      by_cases h1 : y₁ = u
      · have h2 : y₂ ≠ u := fun hh => hyne (h1.trans hh.symm)
        rw [hz₂ne h2]
        rcases hz₁u h1 with hh | hh <;> rw [hh]
        · simpa using fun hc => h2 hc.symm
        · simp
      · rw [hz₁ne h1]
        by_cases h2 : y₂ = u
        · rcases hz₂u h2 with hh | hh <;> rw [hh]
          · simpa using h1
          · simp
        · rw [hz₂ne h2]; simpa using hyne
  · match k with
    | Extra.uB =>
      refine pick_ne (z₁ := (Sum.inl u : SV W)) (z₂ := (Sum.inl b₀ : SV W))
        (by simpa using fun hc => hb₀u hc.symm) (Or.inl rfl) (Or.inr ⟨hb₀adj, hb₀A⟩)
    | Extra.src =>
      refine pick_ne (z₁ := (Sum.inl u : SV W)) (z₂ := (Sum.inr Extra.uB : SV W))
        (by simp) rfl (Or.inr ⟨rfl, rfl⟩)
    | Extra.snk =>
      refine pick_ne (z₁ := (Sum.inl v₁ : SV W)) (z₂ := (Sum.inl v₂ : SV W))
        (by simpa using hv) (Or.inl rfl) (Or.inr rfl)

/-! ### Reading a source-to-sink track back in `H` -/

/-- Undo the division: `u_B` becomes `u` again. -/
private def collapse (u : W) : SV W → W
  | Sum.inl p => p
  | Sum.inr _ => u
/-- Index bookkeeping: the successor form of `getElem`. -/
private theorem succ_get {α : Type*} (l : List α) {i j : ℕ} (h : i + 1 = j)
    (hi : i + 1 < l.length) (hj : j < l.length) : l[i + 1]'hi = l[j]'hj :=
  Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq l h hi hj

private theorem four_le_length
    (hu1 : u ≠ v₁) (hu2 : u ≠ v₂) {Pp : List (SV W)}
    (hP : IsTrackFrom (splitGraph H u A v₁ v₂) Pp
      (Sum.inr Extra.src) (Sum.inr Extra.snk)) :
    4 ≤ Pp.length := by
  classical
  have hne : 0 < Pp.length := List.length_pos_of_ne_nil hP.1.1
  have hP0 : Pp[0]'hne = Sum.inr Extra.src :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hP hne
  have hPl : Pp[Pp.length - 1]'(by omega) = Sum.inr Extra.snk := by
    have h' := hP.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : Pp.length - 1 < Pp.length)] at h'
    exact Option.some_injective _ h'
  have h2 : 2 ≤ Pp.length := by
    by_contra hc
    have h0 : (0 : ℕ) = Pp.length - 1 := by omega
    rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Pp h0 hne
      (by omega), hPl] at hP0
    exact absurd hP0 (extra_ne (by decide))
  have h3 : 3 ≤ Pp.length := by
    by_contra hc
    have hh := hP.1.2.2 0 (by omega)
    rw [hP0, succ_get Pp (show 0 + 1 = Pp.length - 1 by omega) (by omega) (by omega),
      hPl] at hh
    rcases hh with ⟨h1', -⟩ | ⟨-, h2'⟩
    · exact absurd h1' (by decide)
    · exact absurd h2' (by decide)
  by_contra hc
  have hlen : Pp.length = 3 := by omega
  have hstart := hP.1.2.2 0 (by omega)
  have hend := hP.1.2.2 1 (by omega)
  rw [hP0, succ_get Pp (show 0 + 1 = 1 by norm_num) (by omega) (by omega)] at hstart
  rw [succ_get Pp (show 1 + 1 = Pp.length - 1 by omega) (by omega) (by omega), hPl] at hend
  cases hx : Pp[1]'(by omega) with
  | inl p =>
    rw [hx] at hstart hend
    have hpu : p = u := hstart
    rcases hend with hh | hh
    · exact hu1 (hpu ▸ hh)
    · exact hu2 (hpu ▸ hh)
  | inr k =>
    rw [hx] at hend
    rcases hend with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- **Reading one of the two source-to-sink tracks back in `H`.**  A track of the divided graph
from the source to the sink which does not use both halves of the divided vertex becomes a
track of `H` out of `u`, leaving along an edge into `A` or into `B` according to which half it
uses, and ending at `v₁` or at `v₂`. -/
private theorem decode
    (hu1 : u ≠ v₁) (hu2 : u ≠ v₂) {Pp : List (SV W)}
    (hP : IsTrackFrom (splitGraph H u A v₁ v₂) Pp
      (Sum.inr Extra.src) (Sum.inr Extra.snk))
    (hmix : (Sum.inl u : SV W) ∉ Pp ∨ (Sum.inr Extra.uB : SV W) ∉ Pp) :
    ∃ (t : List W) (wend x : W),
      IsTrackFrom H t u wend ∧ 2 ≤ t.length ∧ (wend = v₁ ∨ wend = v₂) ∧
      t[1]? = some x ∧ H.Adj u x ∧
      ((Sum.inr Extra.uB : SV W) ∉ Pp → x ∈ A) ∧
      ((Sum.inl u : SV W) ∉ Pp → x ∉ A) ∧
      (∀ z ∈ t, z = u ∨ (Sum.inl z : SV W) ∈ Pp) ∧
      (Sum.inl wend : SV W) ∈ Pp := by
  classical
  have hlen4 : 4 ≤ Pp.length := four_le_length hu1 hu2 hP
  have hne : 0 < Pp.length := by omega
  have hnd : Pp.Nodup := hP.1.2.1
  have hP0 : Pp[0]'hne = Sum.inr Extra.src :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head hP hne
  have hPl : Pp[Pp.length - 1]'(by omega) = Sum.inr Extra.snk := by
    have h' := hP.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : Pp.length - 1 < Pp.length)] at h'
    exact Option.some_injective _ h'
  -- interior positions carry either a vertex of `H` or the second half of `u`
  have hmid : ∀ (k : ℕ) (hk : k < Pp.length), 1 ≤ k → k ≤ Pp.length - 2 →
      (∃ p : W, Pp[k]'hk = Sum.inl p) ∨ Pp[k]'hk = Sum.inr Extra.uB := by
    intro k hk hk1 hk2
    cases hx : Pp[k]'hk with
    | inl p => exact Or.inl ⟨p, rfl⟩
    | inr e =>
      match e with
      | Extra.uB => exact Or.inr rfl
      | Extra.src =>
        exfalso
        have := (hnd.getElem_inj_iff (hi := hk) (hj := hne)).mp (by rw [hx, hP0])
        omega
      | Extra.snk =>
        exfalso
        have := (hnd.getElem_inj_iff (hi := hk)
          (hj := (by omega : Pp.length - 1 < Pp.length))).mp (by rw [hx, hPl])
        omega
  -- the two halves of the divided vertex cannot both occur
  have hnotboth : ¬ ((Sum.inl u : SV W) ∈ Pp ∧ (Sum.inr Extra.uB : SV W) ∈ Pp) := by
    rintro ⟨h1, h2⟩
    rcases hmix with hh | hh
    · exact hh h1
    · exact hh h2
  -- the second vertex is one of the two halves
  have hh0 := hP.1.2.2 0 (by omega)
  rw [hP0, succ_get Pp (show 0 + 1 = 1 by norm_num) (by omega) (by omega)] at hh0
  have hP1 : Pp[1]'(by omega) = Sum.inl u ∨ Pp[1]'(by omega) = Sum.inr Extra.uB := by
    cases hx : Pp[1]'(by omega) with
    | inl p =>
      rw [hx] at hh0
      exact Or.inl (congrArg Sum.inl (hh0 : p = u))
    | inr e =>
      rw [hx] at hh0
      rcases hh0 with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by decide)
      · exact Or.inr (congrArg Sum.inr h)
  -- the last but one vertex is an end of the branch
  have hPend : ∃ v : W, Pp[Pp.length - 2]'(by omega) = Sum.inl v ∧ (v = v₁ ∨ v = v₂) := by
    have hh := hP.1.2.2 (Pp.length - 2) (by omega)
    rw [succ_get Pp (show Pp.length - 2 + 1 = Pp.length - 1 by omega) (by omega)
      (by omega), hPl] at hh
    cases hx : Pp[Pp.length - 2]'(by omega) with
    | inl p =>
      rw [hx] at hh
      exact ⟨p, rfl, hh⟩
    | inr e =>
      exfalso
      rw [hx] at hh
      rcases hh with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  obtain ⟨vend, hvend, hvend'⟩ := hPend
  -- the collapsed interior
  set t : List W := (trackInterior Pp).map (collapse u) with ht
  have htlen : t.length = Pp.length - 2 := by
    rw [ht, List.length_map,
      Workspace.ProofLemmas.Connectivity58CycleBuild.trackInterior_length]
  have htlen2 : 2 ≤ t.length := by omega
  have htget : ∀ (i : ℕ) (hi : i < t.length),
      t[i]'hi = collapse u (Pp[i + 1]'(by omega)) := by
    intro i hi
    have h1 : i < (trackInterior Pp).length := by
      rw [Workspace.ProofLemmas.Connectivity58CycleBuild.trackInterior_length]; omega
    have h2 : ((trackInterior Pp).map (collapse u))[i]'(by simpa using h1)
        = collapse u ((trackInterior Pp)[i]'h1) := List.getElem_map _
    rw [Workspace.ProofLemmas.Connectivity58CycleBuild.trackInterior_getElem] at h2
    exact h2
  have htget' : ∀ (i j : ℕ) (hi : i < t.length) (hj : j < Pp.length), i + 1 = j →
      t[i]'hi = collapse u (Pp[j]'hj) := by
    intro i j hi hj hij
    rw [htget i hi, succ_get Pp hij (by omega) hj]
  have hmid' : ∀ (i : ℕ) (hi : i < t.length),
      (∃ p : W, Pp[i + 1]'(by omega) = Sum.inl p) ∨
        Pp[i + 1]'(by omega) = Sum.inr Extra.uB :=
    fun i hi => hmid (i + 1) (by omega) (by omega) (by omega)
  -- every interior entry is a vertex of `H` or the second half of `u`
  have hform : ∀ c ∈ trackInterior Pp, (∃ p : W, c = Sum.inl p) ∨ c = Sum.inr Extra.uB := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ :=
      (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff Pp c).mp hc
    exact hmid (j + 1) (by omega) (by omega) (by omega)
  have hintsub : ∀ c ∈ trackInterior Pp, c ∈ Pp :=
    fun c hc => Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hc
  have hintnd : (trackInterior Pp).Nodup :=
    List.Nodup.sublist ((List.dropLast_sublist _).trans (List.tail_sublist _)) hnd
  have htnd : t.Nodup := by
    rw [ht]
    refine List.Nodup.map_on ?_ hintnd
    intro a ha b hb hab
    rcases hform a ha with ⟨p, rfl⟩ | rfl <;> rcases hform b hb with ⟨r, rfl⟩ | rfl
    · exact congrArg Sum.inl hab
    · exfalso
      have hpu : p = u := hab
      exact hnotboth ⟨by rw [← hpu]; exact hintsub _ ha, hintsub _ hb⟩
    · exfalso
      have hru : u = r := hab
      exact hnotboth ⟨by rw [hru]; exact hintsub _ hb, hintsub _ ha⟩
    · rfl
  have htadj : ∀ (i : ℕ) (hi : i + 1 < t.length),
      H.Adj (t[i]'(by omega)) (t[i + 1]'hi) := by
    intro i hi
    have hh := hP.1.2.2 (i + 1) (by omega)
    rw [htget i (by omega), htget (i + 1) hi]
    rcases hmid' i (by omega) with ⟨p, hp⟩ | hp <;>
      rcases hmid' (i + 1) hi with ⟨r, hr⟩ | hr
    · rw [hp, hr] at hh ⊢
      exact hh.1
    · rw [hp, hr] at hh ⊢
      have hpu : p ≠ u := by
        intro hc
        exact hnotboth ⟨by rw [← hc, ← hp]; exact List.getElem_mem _,
          by rw [← hr]; exact List.getElem_mem _⟩
      rcases (hh : p = u ∨ (H.Adj u p ∧ p ∉ A)) with hc | hc
      · exact absurd hc hpu
      · exact hc.1.symm
    · rw [hp, hr] at hh ⊢
      have hru : r ≠ u := by
        intro hc
        exact hnotboth ⟨by rw [← hc, ← hr]; exact List.getElem_mem _,
          by rw [← hp]; exact List.getElem_mem _⟩
      rcases (hh : r = u ∨ (H.Adj u r ∧ r ∉ A)) with hc | hc
      · exact absurd hc hru
      · exact hc.1
    · exfalso
      have heq : Pp[i + 1]'(by omega) = Pp[i + 1 + 1]'(by omega) := by rw [hp, hr]
      have := (hnd.getElem_inj_iff (hi := (by omega : i + 1 < Pp.length))
        (hj := (by omega : i + 1 + 1 < Pp.length))).mp heq
      omega
  have ht0 : t[0]'(by omega) = u := by
    rw [htget' 0 1 (by omega) (by omega) (by norm_num)]
    rcases hP1 with hh | hh <;> rw [hh] <;> rfl
  have htlast : t[t.length - 1]'(by omega) = vend := by
    rw [htget' (t.length - 1) (Pp.length - 2) (by omega) (by omega) (by omega), hvend]
    rfl
  have htrack : IsTrackFrom H t u vend := by
    refine ⟨⟨List.ne_nil_of_length_pos (by omega), htnd, htadj⟩, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < t.length), ht0]
    · rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : t.length - 1 < t.length), htlast]
  -- the second vertex of `t`
  have hPtwo : ∃ x : W, Pp[2]'(by omega) = Sum.inl x := by
    rcases hmid 2 (by omega) (by omega) (by omega) with ⟨p, hp⟩ | hp
    · exact ⟨p, hp⟩
    · exfalso
      rcases hP1 with hh | hh
      · exact hnotboth ⟨by rw [← hh]; exact List.getElem_mem _,
          by rw [← hp]; exact List.getElem_mem _⟩
      · have heq : Pp[1]'(by omega) = Pp[2]'(by omega) := by rw [hh, hp]
        have := (hnd.getElem_inj_iff (hi := (by omega : 1 < Pp.length))
          (hj := (by omega : 2 < Pp.length))).mp heq
        omega
  obtain ⟨x, hx⟩ := hPtwo
  have ht1 : t[1]'(by omega) = x := by
    rw [htget' 1 2 (by omega) (by omega) (by norm_num), hx]; rfl
  have hedge := hP.1.2.2 1 (by omega)
  rw [succ_get Pp (show 1 + 1 = 2 by norm_num) (by omega) (by omega), hx] at hedge
  have hxu : H.Adj u x ∧ ((Sum.inr Extra.uB : SV W) ∉ Pp → x ∈ A) ∧
      ((Sum.inl u : SV W) ∉ Pp → x ∉ A) := by
    rcases hP1 with hh | hh
    · rw [hh] at hedge
      have huP : (Sum.inl u : SV W) ∈ Pp := by rw [← hh]; exact List.getElem_mem _
      exact ⟨(hedge : H.Adj u x ∧ _ ∧ _).1, fun _ => hedge.2.1 rfl, fun hc => absurd huP hc⟩
    · rw [hh] at hedge
      have huBP : (Sum.inr Extra.uB : SV W) ∈ Pp := by rw [← hh]; exact List.getElem_mem _
      have hxu' : x ≠ u := by
        intro hc
        exact hnotboth ⟨by rw [← hc, ← hx]; exact List.getElem_mem _, huBP⟩
      rcases (hedge : x = u ∨ (H.Adj u x ∧ x ∉ A)) with hc | hc
      · exact absurd hc hxu'
      · exact ⟨hc.1, fun hcc => absurd huBP hcc, fun _ => hc.2⟩
  refine ⟨t, vend, x, htrack, htlen2, hvend', ?_, hxu.1, hxu.2.1, hxu.2.2, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem (by omega : 1 < t.length), ht1]
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    rw [htget i hi]
    rcases hmid' i hi with ⟨p, hp⟩ | hp
    · have hmem : (Sum.inl p : SV W) ∈ Pp := by rw [← hp]; exact List.getElem_mem _
      rw [hp]
      exact Or.inr hmem
    · rw [hp]; exact Or.inl rfl
  · rw [← hvend]; exact List.getElem_mem _

/-! ### The two paths -/

/-- **The two vertex-disjoint paths of 5.8 (6).**  PAPER: *"divide `u` into two adjacent
vertices, one incident with the edges in `A` and the other with those in `B`, and use Menger's
theorem to deduce that there are two vertex-disjoint paths between these two vertices and
`{v₁,v₂}`."*  Read back in `H`, the two paths become two tracks out of `u` meeting only at
`u`, one leaving along an edge into `A` and the other along an edge into `B`, and ending at
`v₁` and `v₂` in one order or the other. -/
theorem exists_split_paths
    (hcut : ∀ z : W, ConnectedSet H ({z}ᶜ : Set W))
    (hdeg2 : ∀ z : W, 2 ≤ (H.neighborSet z).ncard)
    (hv : v₁ ≠ v₂) (hu1 : u ≠ v₁) (hu2 : u ≠ v₂)
    (ha : ∃ x, H.Adj u x ∧ x ∈ A) (hb : ∃ x, H.Adj u x ∧ x ∉ A) :
    ∃ (tA tB : List W) (xA xB w₁ w₂ : W),
      IsTrackFrom H tA u w₁ ∧ IsTrackFrom H tB u w₂ ∧
      2 ≤ tA.length ∧ 2 ≤ tB.length ∧
      tA[1]? = some xA ∧ tB[1]? = some xB ∧
      H.Adj u xA ∧ xA ∈ A ∧ H.Adj u xB ∧ xB ∉ A ∧
      (∀ z ∈ tA, z ∈ tB → z = u) ∧
      ((w₁ = v₁ ∧ w₂ = v₂) ∨ (w₁ = v₂ ∧ w₂ = v₁)) := by
  classical
  obtain ⟨Pp, Rr, hPt, hRt, hdisj⟩ :=
    exists_two_tracks (split_nocut hcut hv hu1 hu2 ha hb)
      (split_hdeg hdeg2 hv ha hb)
      (u := (Sum.inr Extra.src : SV W)) (v := (Sum.inr Extra.snk : SV W))
      (extra_ne (by decide))
  -- the two tracks leave the source through different halves of the divided vertex
  have second : ∀ (Qq : List (SV W)),
      IsTrackFrom (splitGraph H u A v₁ v₂) Qq (Sum.inr Extra.src) (Sum.inr Extra.snk) →
      ∃ hq : 1 < Qq.length, (Qq[1]'hq = Sum.inl u ∨ Qq[1]'hq = Sum.inr Extra.uB) ∧
        Qq[1]'hq ≠ Sum.inr Extra.src ∧ Qq[1]'hq ≠ Sum.inr Extra.snk := by
    intro Qq hQ
    have hlen4 : 4 ≤ Qq.length := four_le_length hu1 hu2 hQ
    have hnd : Qq.Nodup := hQ.1.2.1
    have hQ0 : Qq[0]'(by omega) = Sum.inr Extra.src :=
      Workspace.ProofLemmas.SubdivisionCounting.track_head hQ (by omega)
    have hQl : Qq[Qq.length - 1]'(by omega) = Sum.inr Extra.snk := by
      have h' := hQ.2.2
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : Qq.length - 1 < Qq.length)] at h'
      exact Option.some_injective _ h'
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have hh := hQ.1.2.2 0 (by omega)
      rw [hQ0, succ_get Qq (show 0 + 1 = 1 by norm_num) (by omega) (by omega)] at hh
      cases hx : Qq[1]'(by omega) with
      | inl p =>
        rw [hx] at hh
        exact Or.inl (congrArg Sum.inl (hh : p = u))
      | inr e =>
        rw [hx] at hh
        rcases hh with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by decide)
        · exact Or.inr (congrArg Sum.inr h)
    · intro hc
      have := (hnd.getElem_inj_iff (hi := (by omega : 1 < Qq.length))
        (hj := (by omega : 0 < Qq.length))).mp (by rw [hc, hQ0])
      omega
    · intro hc
      have := (hnd.getElem_inj_iff (hi := (by omega : 1 < Qq.length))
        (hj := (by omega : Qq.length - 1 < Qq.length))).mp (by rw [hc, hQl])
      omega
  obtain ⟨hPlen, hPhalf, hPsrc, hPsnk⟩ := second Pp hPt
  obtain ⟨hRlen, hRhalf, hRsrc, hRsnk⟩ := second Rr hRt
  have hPmem : Pp[1]'hPlen ∈ Pp := List.getElem_mem _
  have hRmem : Rr[1]'hRlen ∈ Rr := List.getElem_mem _
  have hne12 : Pp[1]'hPlen ≠ Rr[1]'hRlen := by
    intro hc
    rcases hdisj _ hPmem (hc ▸ hRmem) with hh | hh
    · exact hPsrc hh
    · exact hPsnk hh
  -- so one track uses only `u_A` and the other only `u_B`
  have hsplit : ((Sum.inr Extra.uB : SV W) ∉ Pp ∧ (Sum.inl u : SV W) ∉ Rr) ∨
      ((Sum.inr Extra.uB : SV W) ∉ Rr ∧ (Sum.inl u : SV W) ∉ Pp) := by
    have key : ∀ (Q1 Q2 : List (SV W)) (h1 : 1 < Q1.length) (h2 : 1 < Q2.length),
        Q1[1]'h1 = Sum.inl u → Q2[1]'h2 = Sum.inr Extra.uB →
        (∀ x ∈ Q1, x ∈ Q2 → x = Sum.inr Extra.src ∨ x = Sum.inr Extra.snk) →
        (Sum.inr Extra.uB : SV W) ∉ Q1 ∧ (Sum.inl u : SV W) ∉ Q2 := by
      intro Q1 Q2 h1 h2 e1 e2 hd
      constructor
      · intro hc
        have hm : (Sum.inr Extra.uB : SV W) ∈ Q2 := by rw [← e2]; exact List.getElem_mem _
        rcases hd _ hc hm with hh | hh
        · exact extra_ne (by decide) hh
        · exact extra_ne (by decide) hh
      · intro hc
        have hm : (Sum.inl u : SV W) ∈ Q1 := by rw [← e1]; exact List.getElem_mem _
        rcases hd _ hm hc with hh | hh
        · exact Sum.inl_ne_inr hh
        · exact Sum.inl_ne_inr hh
    rcases hPhalf with hh | hh
    · rcases hRhalf with hh' | hh'
      · exact absurd (hh.trans hh'.symm) hne12
      · exact Or.inl (key Pp Rr hPlen hRlen hh hh' hdisj)
    · rcases hRhalf with hh' | hh'
      · exact Or.inr (key Rr Pp hRlen hPlen hh' hh (fun x hx hx' => hdisj x hx' hx))
      · exact absurd (hh.trans hh'.symm) hne12
  -- decode, in whichever order
  have main : ∀ (Q1 Q2 : List (SV W)),
      IsTrackFrom (splitGraph H u A v₁ v₂) Q1 (Sum.inr Extra.src) (Sum.inr Extra.snk) →
      IsTrackFrom (splitGraph H u A v₁ v₂) Q2 (Sum.inr Extra.src) (Sum.inr Extra.snk) →
      (∀ x ∈ Q1, x ∈ Q2 → x = Sum.inr Extra.src ∨ x = Sum.inr Extra.snk) →
      (Sum.inr Extra.uB : SV W) ∉ Q1 → (Sum.inl u : SV W) ∉ Q2 →
      ∃ (tA tB : List W) (xA xB w₁ w₂ : W),
        IsTrackFrom H tA u w₁ ∧ IsTrackFrom H tB u w₂ ∧
        2 ≤ tA.length ∧ 2 ≤ tB.length ∧
        tA[1]? = some xA ∧ tB[1]? = some xB ∧
        H.Adj u xA ∧ xA ∈ A ∧ H.Adj u xB ∧ xB ∉ A ∧
        (∀ z ∈ tA, z ∈ tB → z = u) ∧
        ((w₁ = v₁ ∧ w₂ = v₂) ∨ (w₁ = v₂ ∧ w₂ = v₁)) := by
    intro Q1 Q2 hQ1 hQ2 hd h1 h2
    obtain ⟨tA, w₁, xA, htA, hlA, hwA, hxAget, hxAadj, hxAmem, -, hAsub, hAend⟩ :=
      decode hu1 hu2 hQ1 (Or.inr h1)
    obtain ⟨tB, w₂, xB, htB, hlB, hwB, hxBget, hxBadj, -, hxBmem, hBsub, hBend⟩ :=
      decode hu1 hu2 hQ2 (Or.inl h2)
    have hmeet : ∀ z ∈ tA, z ∈ tB → z = u := by
      intro z hz hz'
      by_contra hzu
      rcases hAsub z hz with hh | hh
      · exact hzu hh
      rcases hBsub z hz' with hh' | hh'
      · exact hzu hh'
      rcases hd _ hh hh' with hc | hc <;> exact absurd hc (by simp)
    have hwne : w₁ ≠ w₂ := by
      intro hc
      have hBend' : (Sum.inl w₁ : SV W) ∈ Q2 := by rw [hc]; exact hBend
      rcases hd _ hAend hBend' with hh | hh <;> exact absurd hh (by simp)
    refine ⟨tA, tB, xA, xB, w₁, w₂, htA, htB, hlA, hlB, hxAget, hxBget, hxAadj,
      hxAmem h1, hxBadj, hxBmem h2, hmeet, ?_⟩
    rcases hwA with hh | hh <;> rcases hwB with hh' | hh'
    · exact absurd (hh.trans hh'.symm) hwne
    · exact Or.inl ⟨hh, hh'⟩
    · exact Or.inr ⟨hh, hh'⟩
    · exact absurd (hh.trans hh'.symm) hwne
  rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact main Pp Rr hPt hRt hdisj h1 h2
  · exact main Rr Pp hRt hPt (fun x hx hx' => hdisj x hx' hx) h1 h2

end Workspace.ProofLemmas.SplitVertexTwoPaths
