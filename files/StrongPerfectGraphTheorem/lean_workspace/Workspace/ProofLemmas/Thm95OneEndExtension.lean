import Workspace.ProofLemmas.Thm95StripExtension
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.PathGlue

/-! The one-end strip addition in the last sentence of 9.5. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm95OneEndExtension

open Workspace.Types.Core.SPGT Workspace.Types.Knots.SPGT
open Thm95StripExtension

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Deleting the first vertex of an induced path gives its tail. -/
theorem mem_tail {P : List V} {a b v : V} (hP : IsPathFrom G P a b) :
    v ∈ P.tail ↔ v ∈ P ∧ v ≠ a := by
  constructor
  · intro hv
    exact ⟨List.mem_of_mem_tail hv, tail_ne_head hP hv⟩
  · rintro ⟨hv, hne⟩
    cases P with
    | nil => exact (hP.1.1 rfl).elim
    | cons c t =>
      have hca : c = a := Option.some.inj hP.2.1
      rcases List.mem_cons.mp hv with heq | hv
      · exact (hne (heq.trans hca)).elim
      · exact hv

/-- A path's first vertex sees only its second vertex in the tail. -/
theorem head_adj_tail {s x : V} {q : List V} (hQ : IsPathList G (s :: x :: q)) :
    ∀ w ∈ x :: q, G.Adj s w ↔ w = x := by
  intro w hw
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
  have hadj := PathBasics.path_adj_iff hQ (i := 0) (j := k + 1) (by simp) (by simpa using hk)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hadj
  have hnodup : (x :: q).Nodup := (List.nodup_cons.mp hQ.2.1).2
  have heq : (x :: q)[k] = x ↔ k = 0 := by
    exact hnodup.getElem_inj_iff (i := k) (j := 0) (hi := hk) (hj := by simp)
  rw [← hkw, hadj, heq]
  omega

/-- The path from 9.3.2 can be continued into the old rung to cover all its vertices
by a rung of the enlarged strip. The continuation stops at its first old B-vertex. -/
theorem covering_rung {A C B : Set V} (hS : IsStrip G (A, C, B))
    {P R : List V} {a b r s : V} (hP : IsSRung G (A, C, B) P)
    (hPend : IsPathFrom G P a b) (hR : IsPathFrom G R r s)
    (hout : ∀ v ∈ R, v ∉ A ∪ B ∪ C)
    (hattach : ∃ w ∈ ({v | v ∈ P} \ {a} : Set V), G.Adj s w)
    (hanti : Anticomplete G ({v | v ∈ R} \ {s}) ({v | v ∈ P} \ {a})) :
    ∃ Q : List V, IsSRung G (insert r A, C ∪ ({v | v ∈ R} \ {r}), B) Q ∧
      ∀ v ∈ R, v ∈ Q := by
  obtain ⟨a', b', hP', ha', hb', htail, hlast, hint⟩ := hP
  have haa : a' = a := Option.some.inj (hP'.2.1.symm.trans hPend.2.1)
  have hbb : b' = b := Option.some.inj (hP'.2.2.symm.trans hPend.2.2)
  subst a'; subst b'
  have hp : IsSRung G (A, C, B) P := ⟨a, b, hPend, ha', hb', htail, hlast, hint⟩
  have hsout := hout s (PathBasics.getLast_mem hR.2.2)
  have hPtail : P.tail ≠ [] := by
    have hbP := PathBasics.getLast_mem hPend.2.2
    have hba : b ≠ a := fun h => Set.disjoint_left.mp hS.1 (h ▸ ha') hb'
    have hbTail := (mem_tail hPend).mpr ⟨hbP, hba⟩
    intro hnil
    simpa only [hnil, List.not_mem_nil] using hbTail
  have hlen : 1 < P.length := by
    have := List.length_pos_of_ne_nil hPtail
    simp only [List.length_tail] at this
    omega
  have hconn : ConnectedSet G {v | v ∈ P.tail} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (by simpa only [List.drop_one] using PathBasics.isPathList_drop hPend.1 hlen)
  have hbTail : b ∈ P.tail := (mem_tail hPend).mpr
    ⟨PathBasics.getLast_mem hPend.2.2, fun h => Set.disjoint_left.mp hS.1 (h ▸ ha') hb'⟩
  obtain ⟨t, ht, Q, hQ, hQpos, hQmem, hQB⟩ :=
    FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet G
      {v | v ∈ P.tail} B s hconn
      (by obtain ⟨w, hw, hadj⟩ := hattach; exact ⟨w, (mem_tail hPend).mpr hw, hadj⟩)
      ⟨b, hbTail, hb'⟩ (fun h => hsout (Or.inl (Or.inr h)))
  obtain ⟨q, hsplit⟩ : ∃ q, Q = s :: q := by
    cases Q with
    | nil => exact (hQ.1.1 rfl).elim
    | cons c q =>
      have hcs : c = s := Option.some.inj hQ.2.1
      exact ⟨q, by rw [hcs]⟩
  subst Q
  obtain ⟨x, q, rfl⟩ : ∃ x q', q = x :: q' := by
    cases q with
    | nil => simp [pathLength] at hQpos
    | cons x q => exact ⟨x, q, rfl⟩
  have htailQ : IsPathFrom G (x :: q) x t := by
    refine ⟨?_, rfl, ?_⟩
    · simpa only [List.drop_one, List.tail_cons] using
        PathBasics.isPathList_drop hQ.1 (k := 1) (by simp)
    · simpa only [List.getLast?_cons_cons] using hQ.2.2
  have htailmem : ∀ v ∈ x :: q, v ∈ P.tail := by
    intro v hv
    exact hQmem v (List.mem_cons_of_mem _ hv) (tail_ne_head hQ hv)
  have hdisj : ∀ v ∈ R, v ∉ x :: q := by
    intro v hv hvQ
    exact hout v hv (KnotFromTwist.mem_stripVertices_of_isSRung hp
      (List.mem_of_mem_tail (htailmem v hvQ)))
  have hcross : ∀ v ∈ R, ∀ w ∈ x :: q, G.Adj v w ↔ v = s ∧ w = x := by
    intro v hv w hw
    by_cases hvs : v = s
    · subst v
      simpa only [true_and] using head_adj_tail hQ.1 w hw
    · exact iff_of_false (hanti v ⟨hv, hvs⟩ w ((mem_tail hPend).mp (htailmem w hw)))
        (fun h => hvs h.1)
  have hglue := PathGlue.glue_path hR htailQ hdisj hcross
  refine ⟨R ++ (x :: q), ⟨r, t, hglue, Or.inl rfl, ht.2, ?_, ?_, ?_⟩,
    fun v hv => List.mem_append_left _ hv⟩
  · intro v hv hvA
    rcases hvA with hvR | hvA
    · exact tail_ne_head hglue hv hvR
    · rcases List.mem_append.mp (List.mem_of_mem_tail hv) with hvR | hvQ
      · exact hout v hvR (Or.inl (Or.inl hvA))
      · exact htail v (htailmem v hvQ) hvA
  · intro v hv hvB
    rcases List.mem_append.mp (List.mem_of_mem_dropLast hv) with hvR | hvQ
    · exact hout v hvR (Or.inl (Or.inr hvB))
    · exact dropLast_ne_last hglue hv ((hQB v (List.mem_cons_of_mem _ hvQ)).mp hvB)
  · intro v hv
    have hv' := (PathBasics.mem_interior_iff_of_pathFrom hglue).mp hv
    rcases List.mem_append.mp hv'.1 with hvR | hvQ
    · exact Or.inr ⟨hvR, hv'.2.1⟩
    · have hvP := (mem_tail hPend).mp (htailmem v hvQ)
      by_cases hvb : v = b
      · have hvB : v ∈ B := hvb ▸ hb'
        exact (hv'.2.2 ((hQB v (List.mem_cons_of_mem _ hvQ)).mp hvB)).elim
      · exact Or.inl (hint v ((PathBasics.mem_interior_iff_of_pathFrom hPend).mpr
          ⟨hvP.1, hvP.2, hvb⟩))

/-- PAPER (9.5): "we can add f₁ to A₁ and {f₂,...,fₖ} to C₁."
The enlarged triple is a strip because the new path continues into an old rung. -/
theorem strip_add_one_end {A C B : Set V} (hS : IsStrip G (A, C, B))
    {P R : List V} {a b r s : V} (hP : IsSRung G (A, C, B) P)
    (hPend : IsPathFrom G P a b) (hR : IsPathFrom G R r s)
    (hout : ∀ v ∈ R, v ∉ A ∪ B ∪ C)
    (hattach : ∃ w ∈ ({v | v ∈ P} \ {a} : Set V), G.Adj s w)
    (hanti : Anticomplete G ({v | v ∈ R} \ {s}) ({v | v ∈ P} \ {a})) :
    IsStrip G (insert r A, C ∪ ({v | v ∈ R} \ {r}), B) := by
  have hrout := hout r (PathBasics.head_mem hR.2.1)
  obtain ⟨Q, hQ, hRQ⟩ := covering_rung hS hP hPend hR hout hattach hanti
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_,
    ⟨r, Or.inl rfl⟩, hS.2.2.2.2.1, ?_⟩
  · intro v hv hvB
    rcases hv with heq | hvA
    · exact hrout (Or.inl (Or.inr (heq ▸ hvB)))
    · exact Set.disjoint_left.mp hS.1 hvA hvB
  · intro v hv hw
    rcases hv with heq | hvA <;> rcases hw with hvC | hvR
    · exact hrout (Or.inr (heq ▸ hvC))
    · exact hvR.2 heq
    · exact Set.disjoint_left.mp hS.2.1 hvA hvC
    · exact hout v hvR.1 (Or.inl (Or.inl hvA))
  · intro v hvB hw
    rcases hw with hvC | hvR
    · exact Set.disjoint_left.mp hS.2.2.1 hvB hvC
    · exact hout v hvR.1 (Or.inl (Or.inr hvB))
  · intro v hv
    by_cases hvold : v ∈ A ∪ B ∪ C
    · obtain ⟨p, hp, hvp⟩ := hS.2.2.2.2.2 v hvold
      refine ⟨p, old_rung (fun _ => Or.inr) (fun _ => Or.inl) Set.Subset.rfl ?_
        (fun _ _ h => h) hp, hvp⟩
      intro w hw hwA
      rcases hwA with heq | hwA
      · exact (hrout (heq ▸ hw)).elim
      · exact hwA
    · refine ⟨Q, hQ, hRQ v ?_⟩
      rcases hv with ((heq | hvA) | hvB) | (hvC | hvR)
      · exact heq ▸ PathBasics.head_mem hR.2.1
      · exact (hvold (Or.inl (Or.inl hvA))).elim
      · exact (hvold (Or.inl (Or.inr hvB))).elim
      · exact (hvold (Or.inr hvC)).elim
      · exact hvR.1

/-- The last maximality contradiction in 9.5, once 9.3 has been repeated over all
antirungs. The proof constructs the larger striation explicitly. -/
theorem one_end_absurd {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hmax : MaximalStriation G S T) {F : Set V}
    (hF : F ⊆ (striationVertices S T)ᶜ) (i : Fin m)
    (hantiS : ∀ k, k ≠ i → Anticomplete G F (stripVertices (S k)))
    (S₀ : Set V × Set V × Set V) (hor : S₀ = S i ∨ S₀ = reverseStrip (S i))
    {P R : List V} {a b r s : V} (hP : IsSRung G S₀ P)
    (hPend : IsPathFrom G P a b) (hR : IsPathFrom G R r s)
    (hRF : ∀ v ∈ R, v ∈ F)
    (hattach : ∃ w ∈ ({v | v ∈ P} \ {a} : Set V), G.Adj s w)
    (hanti : Anticomplete G ({v | v ∈ R} \ {s}) ({v | v ∈ P} \ {a}))
    (hra : ∀ j w, w ∈ stripVertices (T j) → (G.Adj r w ↔ G.Adj a w))
    (hantiT : ∀ j, Anticomplete G ({v | v ∈ R} \ {r}) (stripVertices (T j))) : False := by
  have hS₀ : IsStrip G S₀ := by
    rcases hor with h | h
    · rw [h]; exact hmax.1.1 i
    · rw [h]; exact KnotFromTwist.isStrip_reverseStrip (hmax.1.1 i)
  have hvertices : stripVertices S₀ = stripVertices (S i) := by
    rcases hor with h | h
    · rw [h]
    · rw [h, stripVertices_reverse]
  obtain ⟨A, C, B⟩ := S₀
  have haA : a ∈ A := by
    obtain ⟨a', b', hp', ha, _⟩ := hP
    have heq : a' = a := Option.some.inj (hp'.2.1.symm.trans hPend.2.1)
    exact heq ▸ ha
  have hout : ∀ v ∈ R, v ∉ A ∪ B ∪ C := by
    intro v hv hvold
    apply hF (hRF v hv)
    exact StriationCompl.stripVertices_S_subset S T i (hvertices ▸ hvold)
  let U : Set V × Set V × Set V := (insert r A, C ∪ ({v | v ∈ R} \ {r}), B)
  have hU : IsStrip G U := strip_add_one_end hS₀ hP hPend hR hout hattach hanti
  have hcopyA : ∀ j v, v ∈ U.1 →
      ∃ a ∈ A, ∀ w ∈ stripVertices (T j), G.Adj v w ↔ G.Adj a w := by
    intro j v hv
    rcases hv with heq | hv
    · subst v; exact ⟨a, haA, hra j⟩
    · exact ⟨v, hv, fun _ _ => Iff.rfl⟩
  have hcopyB : ∀ j v, v ∈ U.2.2 →
      ∃ b ∈ B, ∀ w ∈ stripVertices (T j), G.Adj v w ↔ G.Adj b w :=
    fun _ v hv => ⟨v, hv, fun _ _ => Iff.rfl⟩
  have hcopyC : ∀ j v, v ∈ U.2.1 → v ∈ C ∨ VertexAnticomplete G v (stripVertices (T j)) :=
    fun j _ hv => hv.imp id (fun h => hantiT j _ h)
  apply maximal_absurd_or_reverse hG hmax hF i hantiS (A, C, B) U hor hU
    (r := r) (hrF := hRF r (PathBasics.head_mem hR.2.1))
  · intro v hv
    rcases hv with (hvA | hvB) | hvC
    · exact Or.inl (Or.inl (Or.inr hvA))
    · exact Or.inl (Or.inr hvB)
    · exact Or.inr (Or.inl hvC)
  · intro v hv
    rcases hv with ((heq | hvA) | hvB) | (hvC | hvR)
    · exact Or.inr (heq ▸ hRF r (PathBasics.head_mem hR.2.1))
    · exact Or.inl (Or.inl (Or.inl hvA))
    · exact Or.inl (Or.inl (Or.inr hvB))
    · exact Or.inl (Or.inr hvC)
    · exact Or.inr (hRF v hvR.1)
  · exact Or.inl (Or.inl (Or.inl rfl))
  · intro j hp
    exact parallel_enlarge hp (hcopyA j) (hcopyB j) (hcopyC j)
  · intro j hc
    exact coParallel_enlarge hc (hcopyA j) (hcopyB j) (hcopyC j)

end Workspace.ProofLemmas.Thm95OneEndExtension
