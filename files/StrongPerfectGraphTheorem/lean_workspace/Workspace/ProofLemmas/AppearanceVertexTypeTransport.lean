import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.Thm75Setup

/-!
# Transporting an appearance along an isomorphism of the subdivision

`Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath` (and `thm_5_8`, and
`Thm85Five8Transported`) are all stated with `H : SimpleGraph (Fin n)`, whereas §7.5 works with
`H : SimpleGraph W` for an arbitrary finite `W` (that is how `Thm75Claim1`, `Thm75Claim2`,
`Thm75Claim3`, `Thm75Endgame` and `Thm75Setup` are all phrased).  Nothing can be cited across
that gap without transporting the appearance vocabulary along a graph isomorphism.

`Thm85Five8Transported` did exactly this for the vertex type of `J`; this file does it for the
vertex type of `H`, which is harder because `H`'s vertex type occurs inside `H.lineGraph` and
hence inside the appearance isomorphism `φ`.

Everything here is proved; nothing is `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Thm75Claim2Transport

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {α β : Type*}

/-! ### `Sym2` along a graph isomorphism -/

theorem map_mem_edgeSet {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (e : Sym2 α) (he : e ∈ A.edgeSet) : Sym2.map ψ e ∈ B.edgeSet := by
  revert he
  induction e using Sym2.ind with
  | _ x y =>
    intro he
    rw [Sym2.map_pair_eq]
    exact ψ.map_adj_iff.mpr he

theorem sym2_map_symm {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) (e : Sym2 α) :
    Sym2.map ψ.symm (Sym2.map ψ e) = e := by
  induction e using Sym2.ind with
  | _ x y => simp [Sym2.map_pair_eq]

theorem sym2_map_symm' {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) (e : Sym2 β) :
    Sym2.map ψ (Sym2.map ψ.symm e) = e := by
  induction e using Sym2.ind with
  | _ x y => simp [Sym2.map_pair_eq]

theorem sym2_map_inj {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) {e f : Sym2 α}
    (h : Sym2.map ψ e = Sym2.map ψ f) : e = f := by
  have := congrArg (Sym2.map (⇑ψ.symm)) h
  rwa [sym2_map_symm ψ, sym2_map_symm ψ] at this

/-! ### The induced isomorphism of line graphs -/

/-- An isomorphism `A ≃g B` induces an isomorphism `L(A) ≃g L(B)`. -/
def lineGraphIso {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) :
    A.lineGraph ≃g B.lineGraph where
  toFun e := ⟨Sym2.map ψ e.1, map_mem_edgeSet ψ e.1 e.2⟩
  invFun e := ⟨Sym2.map ψ.symm e.1, map_mem_edgeSet ψ.symm e.1 e.2⟩
  left_inv e := Subtype.ext (sym2_map_symm ψ e.1)
  right_inv e := Subtype.ext (sym2_map_symm' ψ e.1)
  map_rel_iff' {e f} := by
    show B.lineGraph.Adj ⟨Sym2.map ψ e.1, _⟩ ⟨Sym2.map ψ f.1, _⟩ ↔ A.lineGraph.Adj e f
    rw [SimpleGraph.lineGraph_adj_iff_exists, SimpleGraph.lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨hne, v, hv1, hv2⟩
      refine ⟨fun h => hne (Subtype.ext (by rw [h])), ?_⟩
      obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.mp hv1
      obtain ⟨b, hb, hab⟩ := Sym2.mem_map.mp hv2
      have hba : b = a := (EquivLike.injective ψ) hab
      subst hba
      exact ⟨b, ha, hb⟩
    · rintro ⟨hne, v, hv1, hv2⟩
      refine ⟨fun h => hne (Subtype.ext (sym2_map_inj ψ (congrArg Subtype.val h))), ?_⟩
      exact ⟨ψ v, Sym2.mem_map.mpr ⟨v, hv1, rfl⟩, Sym2.mem_map.mpr ⟨v, hv2, rfl⟩⟩

@[simp] theorem lineGraphIso_apply {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (e : A.edgeSet) : ((lineGraphIso ψ) e : Sym2 β) = Sym2.map ψ (e : Sym2 α) := rfl

@[simp] theorem lineGraphIso_symm_apply {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (e : B.edgeSet) : (((lineGraphIso ψ).symm e : A.edgeSet) : Sym2 α)
      = Sym2.map ψ.symm (e : Sym2 β) := rfl

/-! ### `incidentEdges`, `branchVertices`, `IsBranch` along an isomorphism -/

theorem mem_incidentEdges_map {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (v : α) (e : Sym2 α) :
    Sym2.map ψ e ∈ incidentEdges B (ψ v) ↔ e ∈ incidentEdges A v := by
  constructor
  · rintro ⟨he, hv⟩
    refine ⟨?_, ?_⟩
    · by_contra hcon
      revert he hcon
      induction e using Sym2.ind with
      | _ x y =>
        intro he hcon
        rw [Sym2.map_pair_eq] at he
        exact hcon (ψ.map_adj_iff.mp he)
    · obtain ⟨a, ha, hav⟩ := Sym2.mem_map.mp hv
      have : a = v := (EquivLike.injective ψ) hav
      rwa [← this]
  · rintro ⟨he, hv⟩
    exact ⟨map_mem_edgeSet ψ e he, Sym2.mem_map.mpr ⟨v, hv, rfl⟩⟩

theorem trackEdges_map_iso {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (q : List α) : trackEdges (q.map ψ) = Sym2.map ψ '' trackEdges q :=
  Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map (⇑ψ) q

theorem isTrackList_map {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) {q : List α}
    (h : IsTrackList A q) : IsTrackList B (q.map ψ) := by
  refine ⟨by simpa using h.1, h.2.1.map (EquivLike.injective ψ), ?_⟩
  intro i hi
  have hi' : i + 1 < q.length := by simpa using hi
  simp only [List.getElem_map]
  exact ψ.map_adj_iff.mpr (h.2.2 i hi')

/-- `IsBranch` transports along an isomorphism. -/
theorem isBranch_map {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) {q : List α}
    (h : IsBranch A q) : IsBranch B (q.map ψ) := by
  refine ⟨isTrackList_map ψ h.1, ?_, ?_⟩
  · intro v hv
    rw [Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [Workspace.ProofLemmas.SubdivisionCounting.branchVertices_image_of_iso ψ]
    rintro ⟨z, hz, hzw⟩
    exact h.2.1 w hw (by rwa [(EquivLike.injective ψ) hzw] at hz)
  · intro q' hq' hint hsub hmem
    -- pull `q'` back along `ψ`
    have hq'' : IsTrackList A (q'.map ψ.symm) := by
      have := isTrackList_map ψ.symm hq'
      exact this
    have hint' : ∀ v ∈ trackInterior (q'.map ⇑ψ.symm), v ∉ branchVertices A := by
      intro v hv
      rw [Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      intro hcon
      refine hint w hw ?_
      rw [Workspace.ProofLemmas.SubdivisionCounting.branchVertices_image_of_iso ψ]
      exact ⟨ψ.symm w, hcon, by simp⟩
    have hsub' : trackEdges q ⊆ trackEdges (q'.map ⇑ψ.symm) := by
      intro e he
      have h1 : Sym2.map ψ e ∈ trackEdges (q.map ⇑ψ) := by
        rw [trackEdges_map_iso ψ]
        exact ⟨e, he, rfl⟩
      have h2 : Sym2.map ψ e ∈ trackEdges q' := hsub h1
      have h3 : Sym2.map ψ.symm (Sym2.map ψ e) ∈ trackEdges (q'.map ⇑ψ.symm) := by
        rw [trackEdges_map_iso ψ.symm]
        exact ⟨_, h2, rfl⟩
      rwa [sym2_map_symm ψ] at h3
    have hmem' : ∀ v ∈ q, v ∈ q'.map ⇑ψ.symm := by
      intro v hv
      have : ψ v ∈ q' := hmem (ψ v) (List.mem_map.mpr ⟨v, hv, rfl⟩)
      exact List.mem_map.mpr ⟨ψ v, this, by simp⟩
    have hres := h.2.2 (q'.map ⇑ψ.symm) hq'' hint' hsub' hmem'
    -- push the resulting equality forward again
    have : Sym2.map ⇑ψ '' trackEdges (q'.map ⇑ψ.symm) = Sym2.map ⇑ψ '' trackEdges q := by
      rw [hres]
    rw [← trackEdges_map_iso ψ, ← trackEdges_map_iso ψ] at this
    have hqq : (q'.map ⇑ψ.symm).map ⇑ψ = q' := by
      simp [List.map_map]
    rwa [hqq] at this

/-! ### `LocalForLineGraph` and `SaturatesLineGraph` along an isomorphism -/

theorem image_map_symm_image {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (X : Set (Sym2 α)) : Sym2.map ψ.symm '' (Sym2.map ψ '' X) = X := by
  ext e
  simp only [Set.mem_image]
  constructor
  · rintro ⟨_, ⟨e0, he0, rfl⟩, rfl⟩
    rwa [sym2_map_symm ψ]
  · intro he
    exact ⟨Sym2.map ψ e, ⟨e, he, rfl⟩, sym2_map_symm ψ e⟩

theorem localForLineGraph_map {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    {X : Set (Sym2 α)} (h : LocalForLineGraph A X) :
    LocalForLineGraph B (Sym2.map ψ '' X) := by
  rcases h with ⟨v, hv, hsub⟩ | ⟨q, hq, hsub⟩
  · refine Or.inl ⟨ψ v, ?_, ?_⟩
    · rw [Workspace.ProofLemmas.SubdivisionCounting.branchVertices_image_of_iso ψ]
      exact ⟨v, hv, rfl⟩
    · rintro e ⟨e0, he0, rfl⟩
      exact (mem_incidentEdges_map ψ v e0).mpr (hsub he0)
  · refine Or.inr ⟨q.map ψ, isBranch_map ψ hq, ?_⟩
    rintro e ⟨e0, he0, rfl⟩
    rw [trackEdges_map_iso ψ]
    exact ⟨e0, hsub he0, rfl⟩

theorem saturatesLineGraph_map {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    {X : Set (Sym2 α)} (h : SaturatesLineGraph A X) :
    SaturatesLineGraph B (Sym2.map ψ '' X) := by
  intro v hv
  rw [Workspace.ProofLemmas.SubdivisionCounting.branchVertices_image_of_iso ψ] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  intro x hx y hy
  have hback : ∀ z : Sym2 β, z ∈ incidentEdges B (ψ w) \ Sym2.map ψ '' X →
      Sym2.map ψ.symm z ∈ incidentEdges A w \ X := by
    intro z hz
    refine ⟨?_, ?_⟩
    · refine (mem_incidentEdges_map ψ w (Sym2.map ψ.symm z)).mp ?_
      rw [sym2_map_symm' ψ]
      exact hz.1
    · intro hcon
      exact hz.2 ⟨Sym2.map ψ.symm z, hcon, sym2_map_symm' ψ z⟩
  have heq := h w hw (hback x hx) (hback y hy)
  have hmap := congrArg (Sym2.map (⇑ψ)) heq
  rwa [sym2_map_symm' ψ, sym2_map_symm' ψ] at hmap

/-! ### Transporting an appearance -/

section Appearance

variable {V U : Type*}

/-- The appearance isomorphism transported along `ψ : H ≃g H'`. -/
theorem phi_bridge {H : SimpleGraph α} {H' : SimpleGraph β} (ψ : H ≃g H')
    {G : SimpleGraph V} {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    (e : Sym2 α) (he : e ∈ H.edgeSet) :
    (↑(((lineGraphIso ψ).symm.trans φ) ⟨Sym2.map ψ e, map_mem_edgeSet ψ e he⟩) : V)
      = (↑(φ ⟨e, he⟩) : V) := by
  have hkey : ((lineGraphIso ψ).symm ⟨Sym2.map ψ e, map_mem_edgeSet ψ e he⟩ : H.edgeSet)
      = ⟨e, he⟩ := Subtype.ext (sym2_map_symm ψ e)
  show (↑(φ ((lineGraphIso ψ).symm ⟨Sym2.map ψ e, map_mem_edgeSet ψ e he⟩)) : V)
      = (↑(φ ⟨e, he⟩) : V)
  rw [hkey]

theorem isBipartiteSubdivision_map {J : SimpleGraph U} {H : SimpleGraph α}
    {H' : SimpleGraph β} (ψ : H ≃g H') (h : IsBipartiteSubdivision J H) :
    IsBipartiteSubdivision J H' :=
  ⟨Workspace.ProofLemmas.SubdivisionCounting.isSubdivision_of_iso ψ h.1,
    SimpleGraph.Colorable.of_hom ψ.symm.toHom h.2⟩

theorem isAppearance_map {J : SimpleGraph U} {H : SimpleGraph α} {H' : SimpleGraph β}
    (ψ : H ≃g H') {G : SimpleGraph V} {K : Set V} (happ : IsAppearance G J H K)
    (φ : H.lineGraph ≃g G.induce K) : IsAppearance G J H' K :=
  ⟨isBipartiteSubdivision_map ψ happ.1, ⟨(lineGraphIso ψ).symm.trans φ⟩⟩

theorem nondegenerate_map {J : SimpleGraph U} {H : SimpleGraph α} {H' : SimpleGraph β}
    (ψ : H ≃g H') (h : NondegenerateAppearance J H) : NondegenerateAppearance J H' := by
  intro hdeg
  refine h ?_
  rcases hdeg with ⟨hk4, hd⟩ | ⟨hnk4, hk33, ⟨iso⟩⟩
  · exact Or.inl ⟨hk4,
      Workspace.ProofLemmas.SubdivisionCounting.degenerateK4Appearance_of_iso ψ.symm hd⟩
  · exact Or.inr ⟨hnk4, hk33, ⟨ψ.trans iso⟩⟩

end Appearance

/-! ### 5.8's outcome-1 carve-out, for `H` on an arbitrary finite vertex type

`Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath`
is stated with `H : SimpleGraph (Fin n)`.  §7.5 works with `H : SimpleGraph W`.  This is the
same statement with the vertex type of `H` relaxed. -/

section Carveout

variable {V : Type*} [Fintype V] [DecidableEq V] {U : Type*} [Fintype U]

theorem enlargementFromNonlocalAttachmentPathW
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    {W : Type*} [Fintype W] (H : SimpleGraph W) (K : Set V)
    (happ : IsAppearance G J H K) (φ : H.lineGraph ≃g G.induce K)
    (Nc : W → Set V)
    (hN : ∀ c : W, Nc c = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPK : ∀ x ∈ P, x ∉ K)
    (c₁ c₂ : W) (hnb : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (h₁ : ∀ x ∈ Nc c₁, G.Adj p₁ x) (h₂ : ∀ x ∈ Nc c₂, G.Adj p₂ x)
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ Nc c₁) ∨ (x = p₂ ∧ y ∈ Nc c₂))
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H) :
    ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H' := by
  classical
  obtain ⟨ψ⟩ : Nonempty (H ≃g SimpleGraph.map (Fintype.equivFin W).toEmbedding H) :=
    ⟨SimpleGraph.Iso.map (Fintype.equivFin W) H⟩
  refine Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath
    G hG J hJ (Fintype.card W) (SimpleGraph.map (Fintype.equivFin W).toEmbedding H) K
    (isAppearance_map ψ happ φ) ((lineGraphIso ψ).symm.trans φ) (fun c => Nc (ψ.symm c)) ?_
    P p₁ p₂ hP hPK (ψ c₁) (ψ c₂) ?_ ?_ ?_ ?_ ?_
  · -- the transported `N`
    intro c
    show Nc (ψ.symm c) = _
    rw [hN (ψ.symm c)]
    ext x
    constructor
    · rintro ⟨e, he, hec, rfl⟩
      refine ⟨Sym2.map ψ e, map_mem_edgeSet ψ e he, ?_, ?_⟩
      · have h := (mem_incidentEdges_map ψ (ψ.symm c) e).mpr hec
        rwa [RelIso.apply_symm_apply] at h
      · exact (phi_bridge ψ φ e he).symm
    · rintro ⟨e', he', hec', rfl⟩
      refine ⟨Sym2.map ψ.symm e', map_mem_edgeSet ψ.symm e' he', ?_, ?_⟩
      · refine (mem_incidentEdges_map ψ (ψ.symm c) (Sym2.map ψ.symm e')).mp ?_
        rw [sym2_map_symm' ψ, RelIso.apply_symm_apply]
        exact hec'
      · have hb := phi_bridge ψ φ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')
        rw [show (⟨Sym2.map ψ (Sym2.map ψ.symm e'),
            map_mem_edgeSet ψ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')⟩ :
            (SimpleGraph.map (Fintype.equivFin W).toEmbedding H).edgeSet) = ⟨e', he'⟩ from
          Subtype.ext (sym2_map_symm' ψ e')] at hb
        exact hb
  · -- `ψ c₁` and `ψ c₂` still lie on no common branch
    rintro ⟨q, hq, hq1, hq2⟩
    refine hnb ⟨q.map ψ.symm, isBranch_map ψ.symm hq, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨ψ c₁, hq1, by simp⟩
    · exact List.mem_map.mpr ⟨ψ c₂, hq2, by simp⟩
  · simpa using h₁
  · simpa using h₂
  · simpa using hno
  · intro hk4
    exact nondegenerate_map ψ (hnd hk4)

end Carveout

/-! ### Two `φ`-image dictionaries used to move hypotheses across `ψ` -/

section PhiSets

variable {V : Type*}

theorem phi_set_image {H : SimpleGraph α} {H' : SimpleGraph β} (ψ : H ≃g H')
    {G : SimpleGraph V} {K : Set V} (φ : H.lineGraph ≃g G.induce K) (p : V → Prop) :
    {e' : Sym2 β | ∃ he' : e' ∈ H'.edgeSet,
        p (↑(((lineGraphIso ψ).symm.trans φ) ⟨e', he'⟩) : V)}
      = Sym2.map ψ '' {e : Sym2 α | ∃ he : e ∈ H.edgeSet, p (↑(φ ⟨e, he⟩) : V)} := by
  ext e'
  constructor
  · rintro ⟨he', hmem⟩
    refine ⟨Sym2.map ψ.symm e', ⟨map_mem_edgeSet ψ.symm e' he', ?_⟩, sym2_map_symm' ψ e'⟩
    have hb := phi_bridge ψ φ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')
    rw [show (⟨Sym2.map ψ (Sym2.map ψ.symm e'),
        map_mem_edgeSet ψ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')⟩ :
        H'.edgeSet) = ⟨e', he'⟩ from Subtype.ext (sym2_map_symm' ψ e')] at hb
    rw [← hb]
    exact hmem
  · rintro ⟨e, ⟨he, hmem⟩, rfl⟩
    exact ⟨map_mem_edgeSet ψ e he, by rw [phi_bridge ψ φ e he]; exact hmem⟩

theorem rungSet_map {H : SimpleGraph α} {H' : SimpleGraph β} (ψ : H ≃g H')
    {G : SimpleGraph V} {K : Set V} (φ : H.lineGraph ≃g G.induce K) (q : List β) :
    {x : V | ∃ (e : Sym2 α) (he : e ∈ H.edgeSet), e ∈ trackEdges (q.map ψ.symm) ∧
        x = (↑(φ ⟨e, he⟩) : V)}
      = {x : V | ∃ (e' : Sym2 β) (he' : e' ∈ H'.edgeSet), e' ∈ trackEdges q ∧
        x = (↑(((lineGraphIso ψ).symm.trans φ) ⟨e', he'⟩) : V)} := by
  ext x
  constructor
  · rintro ⟨e, he, heq, rfl⟩
    rw [trackEdges_map_iso ψ.symm] at heq
    obtain ⟨e', he'q, rfl⟩ := heq
    have he'E : e' ∈ H'.edgeSet := by
      have : Sym2.map ψ (Sym2.map ψ.symm e') ∈ H'.edgeSet := map_mem_edgeSet ψ _ he
      rwa [sym2_map_symm' ψ] at this
    refine ⟨e', he'E, he'q, ?_⟩
    have hb := phi_bridge ψ φ (Sym2.map ψ.symm e') he
    rw [show (⟨Sym2.map ψ (Sym2.map ψ.symm e'), map_mem_edgeSet ψ (Sym2.map ψ.symm e') he⟩ :
        H'.edgeSet) = ⟨e', he'E⟩ from Subtype.ext (sym2_map_symm' ψ e')] at hb
    exact hb.symm
  · rintro ⟨e', he', he'q, rfl⟩
    refine ⟨Sym2.map ψ.symm e', map_mem_edgeSet ψ.symm e' he', ?_, ?_⟩
    · rw [trackEdges_map_iso ψ.symm]
      exact ⟨e', he'q, rfl⟩
    · have hb := phi_bridge ψ φ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')
      rw [show (⟨Sym2.map ψ (Sym2.map ψ.symm e'),
          map_mem_edgeSet ψ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')⟩ :
          H'.edgeSet) = ⟨e', he'⟩ from Subtype.ext (sym2_map_symm' ψ e')] at hb
      exact hb.symm

theorem branchVertices_symm {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) {b : β}
    (h : b ∈ branchVertices B) : ψ.symm b ∈ branchVertices A := by
  rw [Workspace.ProofLemmas.SubdivisionCounting.branchVertices_image_of_iso ψ] at h
  obtain ⟨z, hz, rfl⟩ := h
  rwa [RelIso.symm_apply_apply]

end PhiSets

/-! ### **5.8 for `H` on an arbitrary vertex type.**

`Workspace.Statements.S05.SPGT.thm_5_8` fixes `H : SimpleGraph (Fin n)`, and
`Thm85Five8Transported` only relaxes the vertex type of `J`.  Every `Thm75*` statement uses
`H : SimpleGraph W`, so 5.8 cannot be cited in §7.5 without this. -/

section Five8

variable {V : Type*} [Fintype V] [DecidableEq V] {U : Type*} [Fintype U]

theorem five8_transport (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) {W : Type*} {H : SimpleGraph W} {n : ℕ} {H' : SimpleGraph (Fin n)}
    (ψ : H ≃g H') (K : Set V) (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K) (N : W → Set V)
    (hN : ∀ c : W, N c = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (F : Set V) (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hnotlocal : ¬ LocalForLineGraph H
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K})
    (hnomajor : ∀ x ∈ F, ¬ MajorForLineGraph G H K φ x) :
    ∃ (P : List V) (p₁ p₂ : V), IsPathFrom G P p₁ p₂ ∧ (∀ x ∈ P, x ∈ F) ∧
      ((∃ c₁ c₂ : W,
          (¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
          (∀ x ∈ N c₁, G.Adj p₁ x) ∧ (∀ x ∈ N c₂, G.Adj p₂ x) ∧
          (∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ N c₁) ∨ (x = p₂ ∧ y ∈ N c₂))) ∨
       (∃ (b₁ b₂ : W) (q : List W) (R : List V) (r₁ r₂ : V),
          b₁ ∈ branchVertices H ∧ b₂ ∈ branchVertices H ∧
          IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
          IsPathList G R ∧
          {x : V | x ∈ R} =
            {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
              e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)} ∧
          N b₁ ∩ {x : V | x ∈ R} = {r₁} ∧ N b₂ ∩ {x : V | x ∈ R} = {r₂} ∧
          (((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧
            (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
           ((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂}) ∨
              (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
            (Even (pathLength P) ↔ Even (pathLength R))) ∨
           (p₁ = p₂ ∧ (∀ x ∈ (N b₁ ∪ N b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
            (∀ y ∈ K, G.Adj p₁ y → y ∈ N b₁ ∪ N b₂ ∪ {z : V | z ∈ R}) ∧
            Even (pathLength R)) ∨
           (r₁ = r₂ ∧ (∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂})) ∧
            Even (pathLength P))))) := by
  classical
  have hN' : ∀ c : Fin n, N (ψ.symm c) = {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H'.edgeSet),
      e ∈ incidentEdges H' c ∧ x = (↑(((lineGraphIso ψ).symm.trans φ) ⟨e, he⟩) : V)} := by
    intro c
    rw [hN (ψ.symm c)]
    ext x
    constructor
    · rintro ⟨e, he, hec, rfl⟩
      refine ⟨Sym2.map ψ e, map_mem_edgeSet ψ e he, ?_, (phi_bridge ψ φ e he).symm⟩
      have h := (mem_incidentEdges_map ψ (ψ.symm c) e).mpr hec
      rwa [RelIso.apply_symm_apply] at h
    · rintro ⟨e', he', hec', rfl⟩
      refine ⟨Sym2.map ψ.symm e', map_mem_edgeSet ψ.symm e' he', ?_, ?_⟩
      · refine (mem_incidentEdges_map ψ (ψ.symm c) (Sym2.map ψ.symm e')).mp ?_
        rw [sym2_map_symm' ψ, RelIso.apply_symm_apply]
        exact hec'
      · have hb := phi_bridge ψ φ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')
        rw [show (⟨Sym2.map ψ (Sym2.map ψ.symm e'),
            map_mem_edgeSet ψ (Sym2.map ψ.symm e') (map_mem_edgeSet ψ.symm e' he')⟩ :
            H'.edgeSet) = ⟨e', he'⟩ from Subtype.ext (sym2_map_symm' ψ e')] at hb
        exact hb
  have hnotlocal' : ¬ LocalForLineGraph H'
      {e : Sym2 (Fin n) | ∃ he : e ∈ H'.edgeSet,
        (↑(((lineGraphIso ψ).symm.trans φ) ⟨e, he⟩) : V) ∈ attachments G F K} := by
    rw [phi_set_image ψ φ (fun y => y ∈ attachments G F K)]
    intro hcon
    have h := localForLineGraph_map ψ.symm hcon
    rw [image_map_symm_image ψ] at h
    exact hnotlocal h
  have hnomajor' : ∀ x ∈ F, ¬ MajorForLineGraph G H' K ((lineGraphIso ψ).symm.trans φ) x := by
    intro x hx hmaj
    refine hnomajor x hx ⟨hmaj.1, ?_⟩
    have h2 := hmaj.2
    rw [phi_set_image ψ φ (fun y => G.Adj x y)] at h2
    have h3 := saturatesLineGraph_map ψ.symm h2
    rwa [image_map_symm_image ψ] at h3
  obtain ⟨P, p₁, p₂, hP, hPF, hcase⟩ :=
    Workspace.ProofLemmas.Thm85Five8Transported.thm85Five8Transported G hG J hJ n H' K
      (isBipartiteSubdivision_map ψ hsub) ((lineGraphIso ψ).symm.trans φ)
      (fun c => N (ψ.symm c)) hN' F hFK hFconn hnotlocal' hnomajor'
  refine ⟨P, p₁, p₂, hP, hPF, ?_⟩
  rcases hcase with ⟨c₁, c₂, hnb, hc1, hc2, hno⟩ |
    ⟨b₁, b₂, q, R, r₁, r₂, hb1, hb2, hbr, hbf, hRp, hRset, hr1, hr2, hcases⟩
  · refine Or.inl ⟨ψ.symm c₁, ψ.symm c₂, ?_, hc1, hc2, hno⟩
    rintro ⟨q, hq, hq1, hq2⟩
    refine hnb ⟨q.map ψ, isBranch_map ψ hq, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨ψ.symm c₁, hq1, by simp⟩
    · exact List.mem_map.mpr ⟨ψ.symm c₂, hq2, by simp⟩
  · exact Or.inr ⟨ψ.symm b₁, ψ.symm b₂, q.map ψ.symm, R, r₁, r₂,
      branchVertices_symm ψ hb1, branchVertices_symm ψ hb2, isBranch_map ψ.symm hbr,
      Workspace.ProofLemmas.SubdivisionCounting.isTrackFrom_map ψ.symm hbf, hRp,
      hRset.trans (rungSet_map ψ φ q).symm, hr1, hr2, hcases⟩

/-- **5.8 with `H` on an arbitrary finite vertex type.** -/
theorem five8W (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) {W : Type*} [Fintype W] (H : SimpleGraph W) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K) (N : W → Set V)
    (hN : ∀ c : W, N c = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (F : Set V) (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hnotlocal : ¬ LocalForLineGraph H
      {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K})
    (hnomajor : ∀ x ∈ F, ¬ MajorForLineGraph G H K φ x) :
    ∃ (P : List V) (p₁ p₂ : V), IsPathFrom G P p₁ p₂ ∧ (∀ x ∈ P, x ∈ F) ∧
      ((∃ c₁ c₂ : W,
          (¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
          (∀ x ∈ N c₁, G.Adj p₁ x) ∧ (∀ x ∈ N c₂, G.Adj p₂ x) ∧
          (∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ N c₁) ∨ (x = p₂ ∧ y ∈ N c₂))) ∨
       (∃ (b₁ b₂ : W) (q : List W) (R : List V) (r₁ r₂ : V),
          b₁ ∈ branchVertices H ∧ b₂ ∈ branchVertices H ∧
          IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
          IsPathList G R ∧
          {x : V | x ∈ R} =
            {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
              e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)} ∧
          N b₁ ∩ {x : V | x ∈ R} = {r₁} ∧ N b₂ ∩ {x : V | x ∈ R} = {r₂} ∧
          (((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧
            (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
           ((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂}) ∨
              (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
            (Even (pathLength P) ↔ Even (pathLength R))) ∨
           (p₁ = p₂ ∧ (∀ x ∈ (N b₁ ∪ N b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
            (∀ y ∈ K, G.Adj p₁ y → y ∈ N b₁ ∪ N b₂ ∪ {z : V | z ∈ R}) ∧
            Even (pathLength R)) ∨
           (r₁ = r₂ ∧ (∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂})) ∧
            Even (pathLength P))))) := by
  obtain ⟨ψ⟩ : Nonempty (H ≃g SimpleGraph.map (Fintype.equivFin W).toEmbedding H) :=
    ⟨SimpleGraph.Iso.map (Fintype.equivFin W) H⟩
  exact five8_transport G hG J hJ ψ K hsub φ N hN F hFK hFconn hnotlocal hnomajor

end Five8

/-! ### PAPER (proof of 7.5, claim (2), printed p. 36)

*"Suppose some vertex `v ∈ F` is major with respect to `L(H)`.  Then since `v ∉ X` it follows
that `v` has a nonneighbour in `Y`, and so `Y ∪ v` is anticonnected; the maximality of `Y`
therefore implies that `v ∈ Y`, and hence `F ∩ Y ≠ ∅`, a contradiction.  So we may assume that
no vertex in `F` is major."*

This is exactly the hypothesis `hnomajor` that 5.8 (and hence `five8W`) needs, so it is the step
that lets claim (2) reach 5.8 at all. -/

section NoMajor

open Workspace.ProofLemmas.Thm75Setup

variable {V : Type*}

theorem phi_inj {G : SimpleGraph V} {H : SimpleGraph α} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {e f : Sym2 α} (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet)
    (h : (↑(φ ⟨e, he⟩) : V) = (↑(φ ⟨f, hf⟩) : V)) : e = f := by
  have h1 : (⟨e, he⟩ : H.edgeSet) = ⟨f, hf⟩ := φ.injective (Subtype.ext h)
  exact congrArg Subtype.val h1

theorem reachable_of_subset (Γ : SimpleGraph V) {S S' : Set V} (hSS' : S ⊆ S')
    (hS : ConnectedSet Γ S) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (ha' : a ∈ S') (hb' : b ∈ S') :
    (Γ.induce S').Reachable ⟨a, ha'⟩ ⟨b, hb'⟩ :=
  (hS ⟨a, ha⟩ ⟨b, hb⟩).map
    ({ toFun := fun z => ⟨(z : V), hSS' z.2⟩, map_rel' := fun h => h } :
      Γ.induce S →g Γ.induce S')

theorem anticonnected_union_singleton (Γ : SimpleGraph V) (Y : Set V)
    (hY : AnticonnectedSet Γ Y) {v y₀ : V} (hy₀ : y₀ ∈ Y) (hnadj : ¬ Γ.Adj v y₀)
    (hvy : v ≠ y₀) : AnticonnectedSet Γ (Y ∪ {v}) := by
  have hsub : Y ⊆ Y ∪ {v} := Set.subset_union_left
  have hy₀' : y₀ ∈ Y ∪ {v} := Or.inl hy₀
  have key : ∀ a : ↥(Y ∪ {v} : Set V), (Γᶜ.induce (Y ∪ {v})).Reachable a ⟨y₀, hy₀'⟩ := by
    rintro ⟨a, ha⟩
    have haM : a ∈ Y ∪ ({v} : Set V) := ha
    rcases ha with haY | hav
    · exact reachable_of_subset Γᶜ hsub hY haY hy₀ _ hy₀'
    · have hav' : a = v := hav
      refine SimpleGraph.Adj.reachable
        (show (Γᶜ.induce (Y ∪ ({v} : Set V))).Adj ⟨a, haM⟩ ⟨y₀, hy₀'⟩ from ?_)
      show Γᶜ.Adj a y₀
      rw [SimpleGraph.compl_adj, hav']
      exact ⟨hvy, hnadj⟩
  intro a b
  exact (key a).trans (key b).symm

/-- A major vertex is `Bc₁c₂`-dominant: saturation bounds the non-neighbours in `δ_H(c)` by one
for **every** branch-vertex `c`, in particular for `c₁` and `c₂`. -/
theorem dominant_of_major [Fintype V] [DecidableEq V] {G : SimpleGraph V} {H : SimpleGraph α}
    {K : Set V} (φ : H.lineGraph ≃g G.induce K) {c₁ c₂ : α}
    (hc₁b : c₁ ∈ branchVertices H) (hc₂b : c₂ ∈ branchVertices H) {v : V}
    (hmaj : MajorForLineGraph G H K φ v) :
    IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) v := by
  have key : ∀ c : α, c ∈ branchVertices H →
      (NSet G H K φ c \ G.neighborSet v).Subsingleton := by
    intro c hc x hx y hy
    obtain ⟨e, he, hec, hxe⟩ := hx.1
    obtain ⟨f, hf, hfc, hyf⟩ := hy.1
    have hesat : e ∈ incidentEdges H c \
        {e : Sym2 α | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)} := by
      refine ⟨hec, ?_⟩
      rintro ⟨he', hadj⟩
      refine hx.2 ?_
      show G.Adj v x
      rw [hxe]
      exact hadj
    have hfsat : f ∈ incidentEdges H c \
        {e : Sym2 α | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)} := by
      refine ⟨hfc, ?_⟩
      rintro ⟨hf', hadj⟩
      refine hy.2 ?_
      show G.Adj v y
      rw [hyf]
      exact hadj
    have hef : e = f := hmaj.2 c hc hesat hfsat
    rw [hxe, hyf, show (⟨e, he⟩ : H.edgeSet) = ⟨f, hf⟩ from Subtype.ext hef]
  exact ⟨key c₁ hc₁b, key c₂ hc₂b⟩

/-- **The printed sentence.**  Under the standing hypotheses of claim (2) of 7.5, no vertex of
`F` is major with respect to `L(H)`. -/
theorem no_major_in_F [Fintype V] [DecidableEq V] {G : SimpleGraph V} {H : SimpleGraph α}
    (K : Set V) (φ : H.lineGraph ≃g G.induce K) {c₁ c₂ : α}
    (hc₁b : c₁ ∈ branchVertices H) (hc₂b : c₂ ∈ branchVertices H)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y)
    (hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
      (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y)
    (X X₀ X₁ : Set V) (hX : X = {x : V | VertexComplete G x Y}) (hX₀ : X₀ = X \ K)
    (F : Set V) (hFdisj : ∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y) :
    ∀ v ∈ F, ¬ MajorForLineGraph G H K φ v := by
  intro v hv hmaj
  have hdom : IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) v :=
    dominant_of_major φ hc₁b hc₂b hmaj
  by_cases hvX : VertexComplete G v Y
  · exact hFdisj v hv (Or.inl (Or.inl (by rw [hX₀, hX]; exact ⟨hvX, hmaj.1⟩)))
  · obtain ⟨y₀, hy₀Y, hy₀⟩ : ∃ y ∈ Y, ¬ G.Adj v y := by
      by_contra hcon
      refine hvX ?_
      intro y hy
      by_contra h
      exact hcon ⟨y, hy, h⟩
    have hvy : v ≠ y₀ := by
      intro hcon
      exact hFdisj v hv (Or.inr (by rw [hcon]; exact hy₀Y))
    have hanti' : AnticonnectedSet G (Y ∪ {v}) :=
      anticonnected_union_singleton G Y hYanti hy₀Y hy₀ hvy
    have hall : ∀ z ∈ Y ∪ ({v} : Set V),
        IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) z := by
      rintro z (hz | hz)
      · exact hYdom z hz
      · have hzv : z = v := hz
        rw [hzv]
        exact hdom
    have heq := hYmax (Y ∪ {v}) Set.subset_union_left hanti' hall
    exact hFdisj v hv (Or.inr (by rw [← heq]; exact Or.inr rfl))

end NoMajor

end Thm75Claim2Transport
