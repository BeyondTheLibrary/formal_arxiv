import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.StriationCompl
import Workspace.ProofLemmas.Thm91KnotOddness

/-!
The strip replacement used in 9.5, Claim (3) and the closing paragraph.
The new rungs are odd because each closes to a hole through two antistrips.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm95StripExtension

open Workspace.Types.Core.SPGT Workspace.Types.Knots.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- The two end sets of an antistrip give private neighbours of the two ends of a rung.
This is the adjacency pattern used by the hole argument in 9.1. -/
theorem private_neighbours {U T : Set V × Set V × Set V}
    (hT : IsAntistrip G T)
    (hpar : ParallelStripAntistrip G U T ∨ CoParallel G U T)
    {p : List V} (hp : IsSRung G U p) :
    ∃ a b x y : V, IsPathFrom G p a b ∧ a ∈ U.1 ∧ b ∈ U.2.2 ∧
      x ∈ stripVertices T ∧ y ∈ stripVertices T ∧
      (∀ z ∈ p, G.Adj x z ↔ z = a) ∧ (∀ z ∈ p, G.Adj y z ↔ z = b) := by
  obtain ⟨A, C, B⟩ := U
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨a, b, hp', ha, hb, htail, hlast, hint⟩ := hp
  obtain ⟨x, hx⟩ := hT.2.2.2.1
  obtain ⟨y, hy⟩ := hT.2.2.2.2.1
  have step {X Z Y : Set V} {x y : V}
      (hpar : ParallelStripAntistrip G (A, C, B) (X, Z, Y))
      (hx : x ∈ X) (hy : y ∈ Y) :
      (∀ z ∈ p, G.Adj x z ↔ z = a) ∧ (∀ z ∈ p, G.Adj y z ↔ z = b) := by
    constructor
    · intro z hz
      constructor
      · intro hadj
        by_contra hza
        by_cases hzb : z = b
        · exact hpar.2.1 x hx z (Or.inl (hzb ▸ hb)) hadj
        · exact hpar.2.1 x hx z (Or.inr
            (hint z ((PathBasics.mem_interior_iff_of_pathFrom hp').mpr ⟨hz, hza, hzb⟩))) hadj
      · intro hza
        simpa only [hza] using (hpar.1.1 a ha x (Or.inl hx)).symm
    · intro z hz
      constructor
      · intro hadj
        by_contra hzb
        by_cases hza : z = a
        · exact hpar.2.2 y hy z (Or.inl (hza ▸ ha)) hadj
        · exact hpar.2.2 y hy z (Or.inr
            (hint z ((PathBasics.mem_interior_iff_of_pathFrom hp').mpr ⟨hz, hza, hzb⟩))) hadj
      · intro hzb
        simpa only [hzb] using (hpar.1.2 b hb y (Or.inl hy)).symm
  rcases hpar with hpar | hpar
  · exact ⟨a, b, x, y, hp', ha, hb, Or.inl (Or.inl hx), Or.inl (Or.inr hy),
      step hpar hx hy⟩
  · exact ⟨a, b, y, x, hp', ha, hb, Or.inl (Or.inr hy), Or.inl (Or.inl hx),
      step hpar hy hx⟩

/-- PAPER (9.1): "Certainly P₁ is odd since x₁-a₁-P₁-b₁-y₂-x₁ is a hole."
The same hole proves oddness of every rung after replacing a strip. -/
theorem odd_rungs {n : ℕ} {T : Fin n → Set V × Set V × Set V}
    {U : Set V × Set V × Set V} (hG : Berge G) (hn : 2 ≤ n)
    (hU : IsStrip G U) (hT : ∀ j, IsAntistrip G (T j))
    (hdisj : ∀ j, Disjoint (stripVertices U) (stripVertices (T j)))
    (hcomp : ∀ j j', j < j' → Complete G (stripVertices (T j)) (stripVertices (T j')))
    (hpar : ∀ j, ParallelStripAntistrip G U (T j) ∨ CoParallel G U (T j))
    {p : List V} (hp : IsSRung G U p) : Odd (pathLength p) := by
  let j : Fin n := ⟨0, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  obtain ⟨a, b, x, _, hpath, ha, hb, hx, _, hxa, _⟩ :=
    private_neighbours (hT j) (hpar j) hp
  obtain ⟨a', b', _, y, hpath', _, _, _, hy, _, hyb⟩ :=
    private_neighbours (hT k) (hpar k) hp
  have hb' : b' = b := Option.some.inj (hpath'.2.2.symm.trans hpath.2.2)
  subst b'
  have hab : a ≠ b := by
    obtain ⟨A, C, B⟩ := U
    exact fun heq => Set.disjoint_left.mp hU.1 ha (heq ▸ hb)
  have hlen : 1 ≤ pathLength p := by
    have hp0 := PathBasics.length_eq_pathLength_add_one hpath.1
    have hhead := PathBasics.getElem_zero_of_head? hpath.2.1 (by omega)
    have hlast := PathBasics.getElem_last_of_getLast? hpath.2.2 (by omega)
    by_contra h
    have heq : p.length - 1 = 0 := by unfold pathLength at h; omega
    have hlast' : p[0] = b := by simpa only [heq] using hlast
    exact hab (hhead.symm.trans hlast')
  exact Thm91.odd_of_two_attachments hG hpath hlen
    (fun hx' => Set.disjoint_left.mp (hdisj j)
      (KnotFromTwist.mem_stripVertices_of_isSRung hp hx') hx)
    (fun hy' => Set.disjoint_left.mp (hdisj k)
      (KnotFromTwist.mem_stripVertices_of_isSRung hp hy') hy)
    (hcomp j k (by change (0 : ℕ) < 1; omega) x hx y hy) hxa hyb

/-- Replacing one strip preserves the striation when its disjointness, anticompleteness,
and parallel or co-parallel relations are preserved. Oddness follows from Berge. -/
theorem replace {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hL : IsStriation G S T) (i : Fin m)
    (U : Set V × Set V × Set V) (hU : IsStrip G U)
    (hdS : ∀ k, k ≠ i → Disjoint (stripVertices U) (stripVertices (S k)))
    (hdT : ∀ j, Disjoint (stripVertices U) (stripVertices (T j)))
    (haS : ∀ k, k ≠ i → Anticomplete G (stripVertices U) (stripVertices (S k)))
    (hp : ∀ j, ParallelStripAntistrip G (S i) (T j) → ParallelStripAntistrip G U (T j))
    (hc : ∀ j, CoParallel G (S i) (T j) → CoParallel G U (T j)) :
    IsStriation G (Function.update S i U) T := by
  classical
  obtain ⟨hS, hT, hSS, hTT, hST, hSo, hTo, hm, hn, hSa, hTc, hpc, htwS, htwT⟩ := hL
  have hup (k : Fin m) (j : Fin n) :
      (ParallelStripAntistrip G (S k) (T j) →
        ParallelStripAntistrip G (Function.update S i U k) (T j)) ∧
      (CoParallel G (S k) (T j) → CoParallel G (Function.update S i U k) (T j)) := by
    by_cases hki : k = i
    · subst k
      simpa using And.intro (hp j) (hc j)
    · simp [Function.update_of_ne hki]
  have htw (k l : Fin m) (j j' : Fin n)
      (h : IsTwist G (S k) (S l) (T j) (T j')) :
      IsTwist G (Function.update S i U k) (Function.update S i U l) (T j) (T j') := by
    have h1 := hup k j
    have h2 := hup l j
    have h3 := hup k j'
    have h4 := hup l j'
    have ag (j : Fin n) : AgreeOn G (S k) (S l) (T j) →
        AgreeOn G (Function.update S i U k) (Function.update S i U l) (T j) :=
      fun h => h.imp (fun h => ⟨(hup k j).1 h.1, (hup l j).1 h.2⟩)
        (fun h => ⟨(hup k j).2 h.1, (hup l j).2 h.2⟩)
    rcases h with ⟨hag, hd⟩ | ⟨hag, hd⟩
    · exact Or.inl ⟨ag j hag, hd.imp (fun h => ⟨h3.1 h.1, h4.2 h.2⟩)
        (fun h => ⟨h3.2 h.1, h4.1 h.2⟩)⟩
    · exact Or.inr ⟨ag j' hag, hd.imp (fun h => ⟨h1.1 h.1, h2.2 h.2⟩)
        (fun h => ⟨h1.2 h.1, h2.1 h.2⟩)⟩
  refine ⟨?_, hT, ?_, hTT, ?_, ?_, hTo, hm, hn, ?_, hTc, ?_, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k; simpa using hU
    · simpa [Function.update_of_ne hki] using hS k
  · intro k l hkl
    by_cases hki : k = i
    · subst k
      simpa [Function.update_of_ne hkl.symm] using hdS l hkl.symm
    · by_cases hli : l = i
      · subst l
        simpa [Function.update_of_ne hki] using (hdS k hki).symm
      · simpa [Function.update_of_ne hki, Function.update_of_ne hli] using hSS k l hkl
  · intro k j
    by_cases hki : k = i
    · subst k; simpa using hdT j
    · simpa [Function.update_of_ne hki] using hST k j
  · intro k p hr
    by_cases hki : k = i
    · subst k
      simp only [Function.update_self] at hr
      exact odd_rungs hG hn hU hT hdT hTc
        (fun j => (hpc i j).imp (hp j) (hc j)) hr
    · simp only [Function.update_of_ne hki] at hr
      exact hSo k p hr
  · intro k l hkl
    by_cases hki : k = i
    · subst k
      simpa [Function.update_of_ne (ne_of_gt hkl)] using haS l (ne_of_gt hkl)
    · by_cases hli : l = i
      · subst l
        simp only [Function.update_self, Function.update_of_ne hki]
        exact fun x hx y hy hadj => haS k hki y hy x hx hadj.symm
      · simpa [Function.update_of_ne hki, Function.update_of_ne hli] using hSa k l hkl
  · intro k j
    exact (hpc k j).imp (hup k j).1 (hup k j).2
  · intro k l hkl
    obtain ⟨j, j', hjj', ht⟩ := htwS k l hkl
    exact ⟨j, j', hjj', htw k l j j' ht⟩
  · intro j j' hjj'
    obtain ⟨k, l, hkl, ht⟩ := htwT j j' hjj'
    exact ⟨k, l, hkl, htw k l j j' ht⟩

/-- A replacement containing the old strip and a new vertex strictly enlarges the striation. -/
theorem vertices_ssubset_update {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {i : Fin m} {U : Set V × Set V × Set V}
    (hsub : stripVertices (S i) ⊆ stripVertices U)
    {r : V} (hr : r ∈ stripVertices U) (hrout : r ∉ striationVertices S T) :
    striationVertices S T ⊂ striationVertices (Function.update S i U) T := by
  classical
  constructor
  · intro v hv
    rcases hv with hv | hv
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hv
      refine Or.inl (Set.mem_iUnion_of_mem k ?_)
      by_cases hki : k = i
      · subst k; simpa using hsub hk
      · simpa [Function.update_of_ne hki] using hk
    · exact Or.inr hv
  · intro hback
    apply hrout
    exact hback (Or.inl (Set.mem_iUnion_of_mem i (by simpa using hr)))

/-- The strip extension contradicts maximality as soon as it adds a vertex outside L. -/
theorem maximal_absurd {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hmax : MaximalStriation G S T) {F : Set V}
    (hF : F ⊆ (striationVertices S T)ᶜ) (i : Fin m)
    (hanti : ∀ k, k ≠ i → Anticomplete G F (stripVertices (S k)))
    (U : Set V × Set V × Set V) (hU : IsStrip G U)
    (hsub : stripVertices (S i) ⊆ stripVertices U)
    (hsupport : stripVertices U ⊆ stripVertices (S i) ∪ F)
    {r : V} (hrF : r ∈ F) (hrU : r ∈ stripVertices U)
    (hp : ∀ j, ParallelStripAntistrip G (S i) (T j) → ParallelStripAntistrip G U (T j))
    (hc : ∀ j, CoParallel G (S i) (T j) → CoParallel G U (T j)) : False := by
  have hdS : ∀ k, k ≠ i → Disjoint (stripVertices U) (stripVertices (S k)) := by
    intro k hki
    refine Set.disjoint_left.mpr ?_
    intro v hv hk
    rcases hsupport hv with hi | hf
    · exact Set.disjoint_left.mp (hmax.1.2.2.1 i k hki.symm) hi hk
    · exact hF hf (StriationCompl.stripVertices_S_subset S T k hk)
  have hdT : ∀ j, Disjoint (stripVertices U) (stripVertices (T j)) := by
    intro j
    refine Set.disjoint_left.mpr ?_
    intro v hv hj
    rcases hsupport hv with hi | hf
    · exact Set.disjoint_left.mp (hmax.1.2.2.2.2.1 i j) hi hj
    · exact hF hf (StriationCompl.stripVertices_T_subset S T j hj)
  have haS : ∀ k, k ≠ i → Anticomplete G (stripVertices U) (stripVertices (S k)) := by
    intro k hki v hv w hw hadj
    rcases hsupport hv with hi | hf
    · rcases lt_or_gt_of_ne hki with hlt | hlt
      · exact hmax.1.2.2.2.2.2.2.2.2.2.1 k i hlt w hw v hi hadj.symm
      · exact hmax.1.2.2.2.2.2.2.2.2.2.1 i k hlt v hi w hw hadj
    · exact hanti k hki v hf w hw hadj
  exact hmax.2 ⟨m, n, Function.update S i U, T,
    replace hG hmax.1 i U hU hdS hdT haS hp hc,
    vertices_ssubset_update hsub hrU (hF hrF)⟩

/-- Enlarging a strip keeps every old rung if the new end sets contain no old middle
vertices. This is the covering check in each of the two additions in 9.5. -/
theorem old_rung {A C B A' C' B' : Set V}
    (ha : A ⊆ A') (hc : C ⊆ C') (hb : B ⊆ B')
    (hA : ∀ v ∈ A ∪ B ∪ C, v ∈ A' → v ∈ A)
    (hB : ∀ v ∈ A ∪ B ∪ C, v ∈ B' → v ∈ B)
    {p : List V} (hp : IsSRung G (A, C, B) p) : IsSRung G (A', C', B') p := by
  obtain ⟨a, b, hpath, haA, hbB, htail, hlast, hint⟩ := hp
  have hmem : ∀ {v}, v ∈ p → v ∈ A ∪ B ∪ C := fun hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung
    (show IsSRung G (A, C, B) p from ⟨a, b, hpath, haA, hbB, htail, hlast, hint⟩) hv
  refine ⟨a, b, hpath, ha haA, hb hbB, ?_, ?_, fun v hv => hc (hint v hv)⟩
  · intro v hv hvA
    exact htail v hv (hA v (hmem (List.mem_of_mem_tail hv)) hvA)
  · intro v hv hvB
    exact hlast v hv (hB v (hmem (List.mem_of_mem_dropLast hv)) hvB)

/-- Reversal changes the end labels, and leaves the vertex set fixed. -/
theorem stripVertices_reverse (S : Set V × Set V × Set V) :
    stripVertices (reverseStrip S) = stripVertices S := by
  obtain ⟨A, C, B⟩ := S
  exact congrArg (· ∪ C) (Set.union_comm B A)

/-- The maximality contradiction also permits reversing the strip before enlarging it,
as in the naming convention for the two outcomes of 9.3. -/
theorem maximal_absurd_or_reverse {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hmax : MaximalStriation G S T) {F : Set V}
    (hF : F ⊆ (striationVertices S T)ᶜ) (i : Fin m)
    (hanti : ∀ k, k ≠ i → Anticomplete G F (stripVertices (S k)))
    (S₀ U : Set V × Set V × Set V) (hor : S₀ = S i ∨ S₀ = reverseStrip (S i))
    (hU : IsStrip G U) (hsub : stripVertices S₀ ⊆ stripVertices U)
    (hsupport : stripVertices U ⊆ stripVertices S₀ ∪ F)
    {r : V} (hrF : r ∈ F) (hrU : r ∈ stripVertices U)
    (hp : ∀ j, ParallelStripAntistrip G S₀ (T j) → ParallelStripAntistrip G U (T j))
    (hc : ∀ j, CoParallel G S₀ (T j) → CoParallel G U (T j)) : False := by
  rcases hor with hor | hor <;> subst S₀
  · exact maximal_absurd hG hmax hF i hanti U hU hsub hsupport hrF hrU hp hc
  · apply maximal_absurd hG hmax hF i hanti (reverseStrip U)
      (KnotFromTwist.isStrip_reverseStrip hU)
    · simpa only [stripVertices_reverse] using hsub
    · simpa only [stripVertices_reverse] using hsupport
    · exact hrF
    · simpa only [stripVertices_reverse] using hrU
    · intro j hpar
      exact (KnotFromTwist.parallel_reverseStrip_left U (T j)).mpr
        (hc j ((KnotFromTwist.coParallel_reverseStrip_left (S i) (T j)).mpr hpar))
    · intro j hcop
      exact (KnotFromTwist.coParallel_reverseStrip_left U (T j)).mpr
        (hp j ((KnotFromTwist.parallel_reverseStrip_left (S i) (T j)).mpr hcop))

/-- A path does not repeat its first vertex in its tail. -/
theorem tail_ne_head {p : List V} {a b : V} (hp : IsPathFrom G p a b)
    {v : V} (hv : v ∈ p.tail) : v ≠ a := by
  cases p with
  | nil => exact (hp.1.1 rfl).elim
  | cons c q =>
    have hca : c = a := Option.some.inj hp.2.1
    have hvq : v ∈ q := hv
    intro hva
    exact (List.nodup_cons.mp hp.1.2.1).1 (hca.symm ▸ hva ▸ hvq)

/-- A path does not repeat its last vertex before the end. -/
theorem dropLast_ne_last {p : List V} {a b : V} (hp : IsPathFrom G p a b)
    {v : V} (hv : v ∈ p.dropLast) : v ≠ b := by
  have hne := hp.1.1
  have hv' := (PathBasics.mem_dropLast_iff hp.1.2.1 hne).mp hv
  have hb : p.getLast hne = b :=
    Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hp.2.2)
  simpa only [hb] using hv'.2

/-- PAPER (9.5(3)): "we can add f₁ to A₁, {f₂,...,fₖ₋₁} to C₁ and fₖ to B₁."
Disjointness and the rung covering condition for this triple. -/
theorem strip_add_two_ends {A C B : Set V} (hS : IsStrip G (A, C, B))
    {R : List V} {r s : V} (hR : IsPathFrom G R r s) (hrs : r ≠ s)
    (hout : ∀ v ∈ R, v ∉ A ∪ B ∪ C) :
    IsStrip G (insert r A, C ∪ {v | v ∈ interior R}, insert s B) := by
  have hr := PathBasics.head_mem hR.2.1
  have hs := PathBasics.getLast_mem hR.2.2
  have hrout := hout r hr
  have hsout := hout s hs
  have hdisj : Disjoint (insert r A) (insert s B) ∧
      Disjoint (insert r A) (C ∪ {v | v ∈ interior R}) ∧
      Disjoint (insert s B) (C ∪ {v | v ∈ interior R}) := by
    refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
    · intro v hv hw
      rcases hv with heq | hv <;> rcases hw with heq' | hw
      · exact hrs (heq.symm.trans heq')
      · exact hrout (Or.inl (Or.inr (heq ▸ hw)))
      · exact hsout (Or.inl (Or.inl (heq' ▸ hv)))
      · exact Set.disjoint_left.mp hS.1 hv hw
    · intro v hv hw
      rcases hv with heq | hv <;> rcases hw with hw | hw
      · exact hrout (Or.inr (heq ▸ hw))
      · exact ((PathBasics.mem_interior_iff_of_pathFrom hR).mp hw).2.1 heq
      · exact Set.disjoint_left.mp hS.2.1 hv hw
      · exact hout v (PathBasics.interior_subset hw) (Or.inl (Or.inl hv))
    · intro v hv hw
      rcases hv with heq | hv <;> rcases hw with hw | hw
      · exact hsout (Or.inr (heq ▸ hw))
      · exact ((PathBasics.mem_interior_iff_of_pathFrom hR).mp hw).2.2 heq
      · exact Set.disjoint_left.mp hS.2.2.1 hv hw
      · exact hout v (PathBasics.interior_subset hw) (Or.inl (Or.inr hv))
  have hnew : IsSRung G (insert r A, C ∪ {v | v ∈ interior R}, insert s B) R := by
    refine ⟨r, s, hR, Or.inl rfl, Or.inl rfl, ?_, ?_, fun v hv => Or.inr hv⟩
    · intro v hv hvA
      rcases hvA with hvA | hvA
      · exact tail_ne_head hR hv hvA
      · exact hout v (List.mem_of_mem_tail hv) (Or.inl (Or.inl hvA))
    · intro v hv hvB
      rcases hvB with hvB | hvB
      · exact dropLast_ne_last hR hv hvB
      · exact hout v (List.mem_of_mem_dropLast hv) (Or.inl (Or.inr hvB))
  have hold {p : List V} (hp : IsSRung G (A, C, B) p) :
      IsSRung G (insert r A, C ∪ {v | v ∈ interior R}, insert s B) p := by
    apply old_rung (fun _ => Or.inr) (fun _ => Or.inl) (fun _ => Or.inr) ?_ ?_ hp
    · intro v hv hvA
      rcases hvA with heq | hvA
      · exact (hrout (heq ▸ hv)).elim
      · exact hvA
    · intro v hv hvB
      rcases hvB with heq | hvB
      · exact (hsout (heq ▸ hv)).elim
      · exact hvB
  refine ⟨hdisj.1, hdisj.2.1, hdisj.2.2, ⟨r, Or.inl rfl⟩, ⟨s, Or.inl rfl⟩, ?_⟩
  intro v hv
  by_cases hvold : v ∈ A ∪ B ∪ C
  · obtain ⟨p, hp, hvp⟩ := hS.2.2.2.2.2 v hvold
    exact ⟨p, hold hp, hvp⟩
  · refine ⟨R, hnew, ?_⟩
    rcases hv with ((heq | hA) | (heq | hB)) | (hC | hI)
    · exact heq ▸ hr
    · exact (hvold (Or.inl (Or.inl hA))).elim
    · exact heq ▸ hs
    · exact (hvold (Or.inl (Or.inr hB))).elim
    · exact (hvold (Or.inr hC)).elim
    · exact PathBasics.interior_subset hI

/-- Copying old end neighbourhoods and adding vertices anticomplete to an antistrip
preserves parallelism. -/
theorem parallel_enlarge {A C B A' C' B' : Set V} {T : Set V × Set V × Set V}
    (hpar : ParallelStripAntistrip G (A, C, B) T)
    (ha : ∀ v ∈ A', ∃ a ∈ A, ∀ w ∈ stripVertices T, G.Adj v w ↔ G.Adj a w)
    (hb : ∀ v ∈ B', ∃ b ∈ B, ∀ w ∈ stripVertices T, G.Adj v w ↔ G.Adj b w)
    (hc : ∀ v ∈ C', v ∈ C ∨ VertexAnticomplete G v (stripVertices T)) :
    ParallelStripAntistrip G (A', C', B') T := by
  obtain ⟨X, Z, Y⟩ := T
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro v hv w hw
    obtain ⟨a, haA, hcopy⟩ := ha v hv
    have hwT : w ∈ stripVertices (X, Z, Y) := hw.elim (fun h => Or.inl (Or.inl h)) Or.inr
    exact (hcopy w hwT).mpr (hpar.1.1 a haA w hw)
  · intro v hv w hw
    obtain ⟨b, hbB, hcopy⟩ := hb v hv
    have hwT : w ∈ stripVertices (X, Z, Y) := hw.elim (fun h => Or.inl (Or.inr h)) Or.inr
    exact (hcopy w hwT).mpr (hpar.1.2 b hbB w hw)
  · intro x hx v hv hadj
    rcases hv with hv | hv
    · obtain ⟨b, hbB, hcopy⟩ := hb v hv
      exact hpar.2.1 x hx b (Or.inl hbB)
        ((hcopy x (Or.inl (Or.inl hx))).mp hadj.symm).symm
    · rcases hc v hv with hvC | hanti
      · exact hpar.2.1 x hx v (Or.inr hvC) hadj
      · exact hanti x (Or.inl (Or.inl hx)) hadj.symm
  · intro y hy v hv hadj
    rcases hv with hv | hv
    · obtain ⟨a, haA, hcopy⟩ := ha v hv
      exact hpar.2.2 y hy a (Or.inl haA)
        ((hcopy y (Or.inl (Or.inr hy))).mp hadj.symm).symm
    · rcases hc v hv with hvC | hanti
      · exact hpar.2.2 y hy v (Or.inr hvC) hadj
      · exact hanti y (Or.inl (Or.inr hy)) hadj.symm

/-- The same neighbourhood-copying check for a co-parallel pair. -/
theorem coParallel_enlarge {A C B A' C' B' : Set V} {T : Set V × Set V × Set V}
    (hpar : CoParallel G (A, C, B) T)
    (ha : ∀ v ∈ A', ∃ a ∈ A, ∀ w ∈ stripVertices T, G.Adj v w ↔ G.Adj a w)
    (hb : ∀ v ∈ B', ∃ b ∈ B, ∀ w ∈ stripVertices T, G.Adj v w ↔ G.Adj b w)
    (hc : ∀ v ∈ C', v ∈ C ∨ VertexAnticomplete G v (stripVertices T)) :
    CoParallel G (A', C', B') T := by
  have heq : stripVertices (reverseStrip T) = stripVertices T := by
    obtain ⟨X, Z, Y⟩ := T
    exact congrArg (· ∪ Z) (Set.union_comm Y X)
  apply parallel_enlarge hpar
  · simpa only [heq] using ha
  · simpa only [heq] using hb
  · simpa only [heq] using hc

/-- The final addition in 9.5(3), after the repetitions of 9.3 have identified the
neighbourhoods of the two ends on every antistrip. No restriction on the edges back
to the old strip is needed for this last construction. -/
theorem two_end_absurd {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hmax : MaximalStriation G S T) {F : Set V}
    (hF : F ⊆ (striationVertices S T)ᶜ) (i : Fin m)
    (hantiS : ∀ k, k ≠ i → Anticomplete G F (stripVertices (S k)))
    {R : List V} {r s a b : V} (hR : IsPathFrom G R r s) (hrs : r ≠ s)
    (hRF : ∀ v ∈ R, v ∈ F) (ha : a ∈ (S i).1) (hb : b ∈ (S i).2.2)
    (hra : ∀ j w, w ∈ stripVertices (T j) → (G.Adj r w ↔ G.Adj a w))
    (hsb : ∀ j w, w ∈ stripVertices (T j) → (G.Adj s w ↔ G.Adj b w))
    (hantiT : ∀ j, Anticomplete G {v | v ∈ interior R} (stripVertices (T j))) : False := by
  rcases hSi : S i with ⟨A, C, B⟩
  have haA : a ∈ A := by simpa only [hSi] using ha
  have hbB : b ∈ B := by simpa only [hSi] using hb
  have hS : IsStrip G (A, C, B) := by simpa only [hSi] using hmax.1.1 i
  have hout : ∀ v ∈ R, v ∉ A ∪ B ∪ C := by
    intro v hv hvS
    apply hF (hRF v hv)
    exact StriationCompl.stripVertices_S_subset S T i (by simpa only [hSi] using hvS)
  let U : Set V × Set V × Set V := (insert r A, C ∪ {v | v ∈ interior R}, insert s B)
  have hU : IsStrip G U := strip_add_two_ends hS hR hrs hout
  have hcopyA : ∀ j v, v ∈ U.1 →
      ∃ a ∈ A, ∀ w ∈ stripVertices (T j), G.Adj v w ↔ G.Adj a w := by
    intro j v hv
    rcases hv with heq | hv
    · subst v
      exact ⟨a, haA, hra j⟩
    · exact ⟨v, hv, fun _ _ => Iff.rfl⟩
  have hcopyB : ∀ j v, v ∈ U.2.2 →
      ∃ b ∈ B, ∀ w ∈ stripVertices (T j), G.Adj v w ↔ G.Adj b w := by
    intro j v hv
    rcases hv with heq | hv
    · subst v
      exact ⟨b, hbB, hsb j⟩
    · exact ⟨v, hv, fun _ _ => Iff.rfl⟩
  have hcopyC : ∀ j v, v ∈ U.2.1 → v ∈ C ∨ VertexAnticomplete G v (stripVertices (T j)) := by
    intro j v hv
    exact hv.imp id (fun hv => hantiT j v hv)
  apply maximal_absurd hG hmax hF i hantiS U hU
    (r := r) (hrF := hRF r (PathBasics.head_mem hR.2.1))
  · rw [hSi]
    intro v hv
    rcases hv with (hv | hv) | hv
    · exact Or.inl (Or.inl (Or.inr hv))
    · exact Or.inl (Or.inr (Or.inr hv))
    · exact Or.inr (Or.inl hv)
  · intro v hv
    rw [hSi]
    rcases hv with ((heq | hv) | (heq | hv)) | (hv | hv)
    · exact Or.inr (heq ▸ hRF r (PathBasics.head_mem hR.2.1))
    · exact Or.inl (Or.inl (Or.inl hv))
    · exact Or.inr (heq ▸ hRF s (PathBasics.getLast_mem hR.2.2))
    · exact Or.inl (Or.inl (Or.inr hv))
    · exact Or.inl (Or.inr hv)
    · exact Or.inr (hRF v (PathBasics.interior_subset hv))
  · exact Or.inl (Or.inl (Or.inl rfl))
  · intro j hp
    rw [hSi] at hp
    exact parallel_enlarge hp (hcopyA j) (hcopyB j) (hcopyC j)
  · intro j hc
    rw [hSi] at hc
    exact coParallel_enlarge hc (hcopyA j) (hcopyB j) (hcopyC j)

end Workspace.ProofLemmas.Thm95StripExtension
