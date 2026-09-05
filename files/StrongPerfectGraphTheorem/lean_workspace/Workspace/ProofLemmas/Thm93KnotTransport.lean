import Workspace.ProofLemmas.Thm93Infrastructure

/-! Transport the knot appearance dictionary along an induced graph isomorphism. -/

set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm93KnotTransport
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

/-- Relabel the vertices of an appearance, including its four triangles and two branches.
The map on line-graph vertices is the original map followed by `f`. -/
theorem transport {A V : Type*} (D : SimpleGraph A) (G : SimpleGraph V)
    (f : A → V) (hf : Function.Injective f)
    (hadj : ∀ a b, G.Adj (f a) (f b) ↔ D.Adj a b)
    (K : Set V) (hK : K = Set.range f)
    (P₁ P₂ : List A) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : A)
    (hdata : KnotAppearanceData D P₁ P₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ Set.univ) :
    KnotAppearanceData G (P₁.map f) (P₂.map f)
      (f a₁) (f b₁) (f a₂) (f b₂) (f x₁) (f y₁) (f x₂) (f y₂) K := by
  classical
  let g : ↥(Set.univ : Set A) → K := fun a => ⟨f a, by rw [hK]; exact ⟨a, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b h
      exact Subtype.ext (hf (congrArg Subtype.val h))
    · intro b
      have hb : (b : V) ∈ Set.range f := by rw [← hK]; exact b.property
      obtain ⟨a, ha⟩ := hb
      exact ⟨⟨a, Set.mem_univ a⟩, Subtype.ext ha⟩
  let psi : D.induce Set.univ ≃g G.induce K :=
    { Equiv.ofBijective g hg with
      map_rel_iff' := by intro a b; exact hadj a b }
  obtain ⟨n, H, phi, happ, hdeg, c₁, c₂, c₃, c₄, N,
    hN, hnd, h12, h23, h34, h41, hbv, hx₁, hy₂, hy₁, hx₂,
    hNc₁, hNc₂, hNc₃, hNc₄, hB₁, hB₂⟩ := hdata
  have hphi : ∀ e : H.edgeSet,
      (↑((phi.trans psi) e) : V) = f (↑(phi e) : A) := fun _ => rfl
  have himage (q : List (Fin n)) :
      f '' {v : A | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ v = (↑(phi ⟨e, he⟩) : A)} =
      {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ v = (↑((phi.trans psi) ⟨e, he⟩) : V)} := by
    ext v
    constructor
    · rintro ⟨w, ⟨e, he, hq, rfl⟩, rfl⟩
      exact ⟨e, he, hq, rfl⟩
    · rintro ⟨e, he, hq, rfl⟩
      exact ⟨_, ⟨e, he, hq, rfl⟩, rfl⟩
  refine ⟨n, H, phi.trans psi, ⟨happ.1, ⟨phi.trans psi⟩⟩, hdeg,
    c₁, c₂, c₃, c₄, fun c => f '' N c,
    ?_, hnd, h12, h23, h34, h41, hbv, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    dsimp only
    rw [hN c]
    ext v
    constructor
    · rintro ⟨w, ⟨e, he, hc, rfl⟩, rfl⟩
      exact ⟨e, he, hc, rfl⟩
    · rintro ⟨e, he, hc, rfl⟩
      exact ⟨_, ⟨e, he, hc, rfl⟩, rfl⟩
  · obtain ⟨he, h⟩ := hx₁
    exact ⟨he, congrArg f h⟩
  · obtain ⟨he, h⟩ := hy₂
    exact ⟨he, congrArg f h⟩
  · obtain ⟨he, h⟩ := hy₁
    exact ⟨he, congrArg f h⟩
  · obtain ⟨he, h⟩ := hx₂
    exact ⟨he, congrArg f h⟩
  · simp [Set.image_insert_eq, Set.image_singleton, hNc₁]
  · simp [Set.image_insert_eq, Set.image_singleton, hNc₂]
  · simp [Set.image_insert_eq, Set.image_singleton, hNc₃]
  · simp [Set.image_insert_eq, Set.image_singleton, hNc₄]
  · obtain ⟨q, hq, ht, hset⟩ := hB₁
    refine ⟨q, hq, ht, ?_⟩
    rw [← himage, ← hset]
    ext v
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  · obtain ⟨q, hq, ht, hset⟩ := hB₂
    refine ⟨q, hq, ht, ?_⟩
    rw [← himage, ← hset]
    ext v
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]

end Workspace.ProofLemmas.Thm93KnotTransport
