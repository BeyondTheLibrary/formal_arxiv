/-  Proof attempt for statement 18.7 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 115).

    THE PAPER'S PROOF (paper/proofs/18_7.md, verbatim):

      "Proof.  Suppose G contains a pseudowheel; then it contains an optimal
       pseudowheel, say (X, Y, P), where P is p1-...-pn.  Let Z be the set of all
       Y-complete vertices in G.  So Y, Z are disjoint, nonempty, and complete to
       each other, and |Z| >= 2.  Let F0 = V(G) \ (Y u Z).  By 15.2, we may assume
       that F0 is connected and every vertex in Z has a neighbour in F0, for
       otherwise the theorem holds.  Choose i > 1 such that p_i p_{i+1} is
       Y-complete, and let A,B be the two components of V(P \ p_i).  Since p1,
       p_{i+1} both have neighbours in F0, it follows that F0 contains a minimal
       connected set F such that there are vertices in A and in B with neighbours
       in F.  From the minimality of F it is disjoint from V(P); and disjoint from
       X u Y since X subseteq Z, contrary to 18.6.  This proves 18.7."

    HOW IT MAPS ONTO THE LEAN PROOF.

    * "it contains an optimal pseudowheel" is `exists_optimal`: minimise the number
      of Y-complete vertices of P over all pseudowheels, then maximise |Y| among the
      minimisers with the same X and P.  (Enlarging Y can only shrink the set of
      Y-complete vertices, so the maximiser still attains the global minimum.)
    * "Z ... nonempty ... |Z| >= 2" uses p1 and the second Y-complete vertex of P
      supplied by the definition of a pseudowheel; "Y, Z disjoint" is `G.irrefl`.
    * "By 15.2 we may assume F0 is connected and every vertex of Z has a neighbour
      in F0" is the second bullet of `thm_15_2` applied to the complete pair (Z,Y).
      Its side condition `Z u Y /= V(G)` holds because p2 lies in neither.
    * "Choose i > 1 such that p_i p_{i+1} is Y-complete" is `thm_18_4` (P has an odd
      number, at least 3, of Y-complete edges), together with the fact that p2 is not
      Y-complete, which forces i > 1.
    * "F0 contains a minimal connected set F ..." is `exists_min_nat` applied to the
      family of connected subsets of F0 having an attachment in A and one in B; F0
      itself belongs to the family.
    * "From the minimality of F it is disjoint from V(P)" is `shrink`: if v in F lies
      on P then v lies in A or in B (it is not Y-complete, so v /= p_i); replacing F
      by the component of F \ {v} containing the far attachment gives a strictly
      smaller member of the family, since that component has a vertex adjacent to v
      and v itself lies on the missing side.
    * "contrary to 18.6": the subpath P' produced by `thm_18_6` contains the two
      attachments, one strictly before p_i and one strictly after, hence contains p_i
      in its interior -- but p_i is Y-complete.                                      -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Decompositions
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Statements.S15.Thm_15_2
import Workspace.Statements.S18.Thm_18_4
import Workspace.Statements.S18.Thm_18_6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S18

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

/-! ### Choosing an extremal object -/

/-- Minimise a `ℕ`-valued measure over a nonempty family. -/
private theorem exists_min_nat {α : Type*} (p : α → Prop) (f : α → ℕ) (h : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → f a ≤ f b := by
  classical
  have hne : {n : ℕ | ∃ a, p a ∧ f a = n}.Nonempty := by
    obtain ⟨a, ha⟩ := h
    exact ⟨f a, a, ha, rfl⟩
  obtain ⟨a, ha, hfa⟩ := Nat.sInf_mem hne
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hfa]
  exact Nat.sInf_le ⟨b, hb, rfl⟩

/-- Maximise a bounded `ℕ`-valued measure over a nonempty family. -/
private theorem exists_max_nat {α : Type*} (p : α → Prop) (f : α → ℕ) (N : ℕ)
    (hbd : ∀ a, p a → f a ≤ N) (h : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → f b ≤ f a := by
  classical
  have hne : {n : ℕ | ∃ a, p a ∧ f a = n}.Nonempty := by
    obtain ⟨a, ha⟩ := h
    exact ⟨f a, a, ha, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ a, p a ∧ f a = n} := by
    refine ⟨N, ?_⟩
    rintro n ⟨a, ha, rfl⟩
    exact hbd a ha
  obtain ⟨a, ha, hfa⟩ := Nat.sSup_mem hne hbdd
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hfa]
  exact le_csSup hbdd ⟨b, hb, rfl⟩

/-! ### Walks, components, infixes -/

/-- If no edge of `H` leaves `E` inside `D`, a walk of `H|D` starting in `E` stays in `E`. -/
private theorem walk_stays {V : Type*} {H : SimpleGraph V} {D E : Set V}
    (hclosed : ∀ a ∈ E, ∀ b ∈ D, H.Adj a b → b ∈ E)
    {x y : ↥D} (p : (H.induce D).Walk x y) (hx : (x : V) ∈ E) : (y : V) ∈ E := by
  revert hx
  induction p with
  | nil => exact fun h => h
  | @cons a b _ hab _ ih => exact fun ha => ih (hclosed _ ha _ b.2 hab)

/-- The engine behind *"from the minimality of `F`"*: given a connected `F`, a vertex
`v ∈ F` and another vertex `w ∈ F`, the component `D` of `F \ {v}` containing `w` is a
strictly smaller connected set that still reaches `w`, and — because `F` is connected —
some vertex of `D` is adjacent to `v`. -/
private theorem shrink {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Set V} {v w : V}
    (hFconn : ConnectedSet G F) (hvF : v ∈ F) (hwF : w ∈ F) (hwv : w ≠ v) :
    ∃ D : Set V, D ⊆ F ∧ v ∉ D ∧ w ∈ D ∧ ConnectedSet G D ∧
      (∃ d ∈ D, G.Adj v d) ∧ D.ncard < F.ncard := by
  classical
  have hwmem : w ∈ F \ ({v} : Set V) := ⟨hwF, hwv⟩
  obtain ⟨D, hD, hwD⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G (F \ ({v} : Set V)) hwmem
  have hDsub : D ⊆ F := fun z hz => (hD.1 hz).1
  have hvD : v ∉ D := fun hz => (hD.1 hz).2 rfl
  refine ⟨D, hDsub, hvD, hwD, hD.2.1, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hclosed : ∀ a ∈ D, ∀ b ∈ F, G.Adj a b → b ∈ D := by
      intro a haD b hbF hab
      have hbv : b ≠ v := fun hbe => hcon a haD (hbe ▸ hab.symm)
      have hconn : ConnectedSet G (D ∪ ({b} : Set V)) :=
        Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
          hD.2.1 ⟨a, haD, hab.symm⟩
      have hsub : D ∪ ({b} : Set V) ⊆ F \ ({v} : Set V) := by
        rintro z (hz | hz)
        · exact hD.1 hz
        · have hzb : z = b := hz
          rw [hzb]
          exact ⟨hbF, hbv⟩
      have heq := hD.2.2 (D ∪ ({b} : Set V)) Set.subset_union_left hsub hconn
      have hbin : b ∈ D ∪ ({b} : Set V) := Set.mem_union_right _ rfl
      rw [heq] at hbin
      exact hbin
    obtain ⟨walk⟩ := hFconn ⟨w, hwF⟩ ⟨v, hvF⟩
    exact hvD (walk_stays hclosed walk hwD)
  · exact Set.ncard_lt_ncard ⟨hDsub, fun hc => hvD (hc hvF)⟩ (Set.toFinite _)

/-- An infix sits at a fixed offset inside the ambient list. -/
private theorem infix_getElem {α : Type*} {q P : List α} (h : q <:+: P) :
    ∃ r : ℕ, r + q.length ≤ P.length ∧
      ∀ (k : ℕ) (hk : k < q.length) (hk' : r + k < P.length), (P[r + k]'hk') = q[k]'hk := by
  obtain ⟨s, t, hst⟩ := h
  subst hst
  refine ⟨s.length, by simp [List.length_append], ?_⟩
  intro k hk hk'
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### "it contains an optimal pseudowheel" -/

private theorem exists_optimal (G : SimpleGraph V)
    (hex : ∃ (X Y : Set V) (P : List V), IsPseudowheel G X Y P) :
    ∃ (X Y : Set V) (P : List V), OptimalPseudowheel G X Y P := by
  classical
  -- minimise the number of `Y`-complete vertices of `P` over all pseudowheels
  obtain ⟨⟨X₀, Y₀, P₀⟩, hpw₀, hmin⟩ :=
    exists_min_nat (fun t : Set V × Set V × List V => IsPseudowheel G t.1 t.2.1 t.2.2)
      (fun t => {v : V | v ∈ t.2.2 ∧ VertexComplete G v t.2.1}.ncard)
      (by obtain ⟨X, Y, P, h⟩ := hex; exact ⟨⟨X, Y, P⟩, h⟩)
  -- among the minimisers with this `X` and `P`, take one with `Y` of maximum size
  obtain ⟨Y₁, ⟨hpw₁, hcnt₁⟩, hmax⟩ :=
    exists_max_nat (fun Y : Set V => IsPseudowheel G X₀ Y P₀ ∧
        {v : V | v ∈ P₀ ∧ VertexComplete G v Y}.ncard =
          {v : V | v ∈ P₀ ∧ VertexComplete G v Y₀}.ncard)
      (fun Y => Y.ncard) (Fintype.card V)
      (by
        intro Y _
        calc Y.ncard ≤ (Set.univ : Set V).ncard :=
              Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
          _ = Fintype.card V := by rw [Set.ncard_univ, Nat.card_eq_fintype_card])
      ⟨Y₀, hpw₀, rfl⟩
  refine ⟨X₀, Y₁, P₀, hpw₁, ?_, ?_⟩
  · rintro ⟨X', Y', P', hpw', hlt⟩
    have := hmin ⟨X', Y', P'⟩ hpw'
    simp only at this hlt
    omega
  · rintro ⟨Y', hpw', hss⟩
    have hsub : {v : V | v ∈ P₀ ∧ VertexComplete G v Y'} ⊆
        {v : V | v ∈ P₀ ∧ VertexComplete G v Y₁} := by
      rintro v ⟨hvP, hvY⟩
      exact ⟨hvP, fun y hy => hvY y (hss.1 hy)⟩
    have hle : {v : V | v ∈ P₀ ∧ VertexComplete G v Y'}.ncard ≤
        {v : V | v ∈ P₀ ∧ VertexComplete G v Y₀}.ncard := by
      rw [← hcnt₁]; exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hge := hmin ⟨X₀, Y', P₀⟩ hpw'
    simp only at hge
    have heq : {v : V | v ∈ P₀ ∧ VertexComplete G v Y'}.ncard =
        {v : V | v ∈ P₀ ∧ VertexComplete G v Y₀}.ncard := le_antisymm hle hge
    have hlt : Y₁.ncard < Y'.ncard := Set.ncard_lt_ncard hss (Set.toFinite _)
    have := hmax Y' ⟨hpw', heq⟩
    omega


/-- **18.7** — the main result of Section 18 (printed p. 115).

Preceded by: *"Now we come to the main result of this section, 1.8.8, which we
restate, the following."*

PAPER: *"Let `G ∈ F₇`.  If it contains a pseudowheel then it admits a balanced
skew partition.  In particular, every recalcitrant graph belongs to `F₈`."*

This is the eighth of the twelve main steps of the proof of 1.2: it discharges
statement 8 of theorem 1.8 (printed p. 7), *"For every `G ∈ F₇`, either `G` admits
a balanced skew partition, or `G ∈ F₈`."*

Encoding notes.

* Both sentences are part of the statement; they are formalized as two theorems.
* **This** theorem is the first sentence, with its own hypothesis `G ∈ F₇`: if
  `G ∈ F₇` and `G` contains a pseudowheel (i.e. some triple `(X,Y,P)` is a
  pseudowheel in `G`), then `G` admits a balanced skew partition.
* The closing *"In particular"* sentence is `thm_18_7_recalcitrant` below.  It is
  deliberately **not** placed under the hypothesis `G ∈ F₇`, nor under any other:
  the paper asserts it of every recalcitrant graph. -/
theorem thm_18_7 (G : SimpleGraph V) :
    InF7 G → (∃ (X Y : Set V) (P : List V), IsPseudowheel G X Y P) →
      AdmitsBalancedSkewPartition G := by
  intro hG hex
  classical
  by_contra hno
  -- "Suppose G contains a pseudowheel; then it contains an optimal pseudowheel (X,Y,P)."
  obtain ⟨X, Y, P, hopt⟩ := exists_optimal G hex
  obtain ⟨⟨hXYdisj, hXne, hYne, hXanti, hYanti, hXYcompl⟩, p₁, p₂, pₙ,
    ⟨hPfrom, hp₂head, hPout, hPlen⟩, hXuniq, hp₁Y, ⟨w₀, hw₀P, hw₀ne, hw₀Y⟩, hp₂Y, hpₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hP0 : (P[0]'(by omega)) = p₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hPfrom.2.1 (by omega)
  -- the second vertex of `P` really is `p₂`
  have hP1 : (P[1]'(by omega)) = p₂ := by
    have h0 : 0 < P.tail.length := by simp only [List.length_tail]; omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at hp₂head
    have hval := Option.some_injective _ hp₂head
    rw [← hval]
    simp
  have hp₂P : p₂ ∈ P := by
    rw [← hP1]; exact List.getElem_mem _
  -- "Let Z be the set of all Y-complete vertices in G."
  obtain ⟨Z, hZmem⟩ : ∃ Z : Set V, ∀ x : V, x ∈ Z ↔ VertexComplete G x Y :=
    ⟨{v : V | VertexComplete G v Y}, fun _ => Iff.rfl⟩
  have hF₀mem : ∀ x : V, x ∈ (Z ∪ Y)ᶜ ↔ (¬ VertexComplete G x Y ∧ x ∉ Y) := by
    intro x
    simp only [Set.mem_compl_iff, Set.mem_union, not_or, hZmem]
  -- "So Y, Z are disjoint, nonempty, and complete to each other, and |Z| ≥ 2."
  have hZYdisj : Disjoint Z Y :=
    Set.disjoint_left.mpr fun a haZ haY => G.irrefl ((hZmem a).mp haZ a haY)
  have hp₁Z : p₁ ∈ Z := (hZmem p₁).mpr hp₁Y
  have hw₀Z : w₀ ∈ Z := (hZmem w₀).mpr hw₀Y
  have hZne : Z.Nonempty := ⟨p₁, hp₁Z⟩
  have hZnt : Z.Nontrivial := ⟨p₁, hp₁Z, w₀, hw₀Z, hw₀ne.symm⟩
  have hZcompl : Complete G Z Y := fun z hz => (hZmem z).mp hz
  -- "Let F₀ = V(G) \ (Y ∪ Z).  By 15.2, we may assume that F₀ is connected and every
  -- vertex in Z has a neighbour in F₀, for otherwise the theorem holds."
  have hZYuniv : Z ∪ Y ≠ Set.univ := by
    intro h
    have hmem : p₂ ∈ Z ∪ Y := by rw [h]; trivial
    rcases hmem with h' | h'
    · exact hp₂Y ((hZmem p₂).mp h')
    · exact (hPout p₂ hp₂P).2 h'
  obtain ⟨-, hb2⟩ :=
    _root_.Workspace.Statements.S15.SPGT.thm_15_2 G hG.1 hno Z Y hZne hYne hZYdisj hZcompl
  obtain ⟨hF₀conn, hZnbr⟩ := hb2 hZYuniv
  have hZnbr' := hZnbr hZnt
  -- "Choose i > 1 such that pᵢpᵢ₊₁ is Y-complete."
  have h184 := thm_18_4 G hG X Y P hopt.1
  have hEne : ({e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G Y u v}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by have := h184.1.2; omega)
  obtain ⟨e, u, huP, v, hvP, -, hadjuv, huY, hvY⟩ := hEne
  obtain ⟨m, hm, hmY, hm1Y⟩ : ∃ (m : ℕ) (hm : m + 1 < P.length),
      VertexComplete G (P[m]'(Nat.lt_of_succ_lt hm)) Y ∧ VertexComplete G (P[m + 1]'hm) Y := by
    obtain ⟨iu, hiu, hueq⟩ := List.getElem_of_mem huP
    obtain ⟨iv, hiv, hveq⟩ := List.getElem_of_mem hvP
    have hadjidx : G.Adj (P[iu]'hiu) (P[iv]'hiv) := by rw [hueq, hveq]; exact hadjuv
    rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hP hiu hiv).mp hadjidx with h | h
    · subst h
      refine ⟨iu, hiv, ?_, ?_⟩
      · have h1 : (P[iu]'(Nat.lt_of_succ_lt hiv)) = u := hueq
        rw [h1]; exact huY
      · have h2 : (P[iu + 1]'hiv) = v := hveq
        rw [h2]; exact hvY
    · subst h
      refine ⟨iv, hiu, ?_, ?_⟩
      · have h1 : (P[iv]'(Nat.lt_of_succ_lt hiu)) = v := hveq
        rw [h1]; exact hvY
      · have h2 : (P[iv + 1]'hiu) = u := hueq
        rw [h2]; exact huY
  have hm0 : m < P.length := Nat.lt_of_succ_lt hm
  -- `i > 1`, because `p₂` is not `Y`-complete
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hmz : m = 0 := by omega
    subst hmz
    have hval : VertexComplete G (P[1]'(by omega)) Y := hm1Y
    rw [hP1] at hval
    exact hp₂Y hval
  -- "let A,B be the two components of V(P \ pᵢ)"
  obtain ⟨A, hAmem⟩ : ∃ A : Set V,
      ∀ x : V, x ∈ A ↔ ∃ (j : ℕ) (hj : j < P.length), j < m ∧ (P[j]'hj) = x :=
    ⟨{x : V | ∃ (j : ℕ) (hj : j < P.length), j < m ∧ (P[j]'hj) = x}, fun _ => Iff.rfl⟩
  obtain ⟨B, hBmem⟩ : ∃ B : Set V,
      ∀ x : V, x ∈ B ↔ ∃ (j : ℕ) (hj : j < P.length), m < j ∧ (P[j]'hj) = x :=
    ⟨{x : V | ∃ (j : ℕ) (hj : j < P.length), m < j ∧ (P[j]'hj) = x}, fun _ => Iff.rfl⟩
  have hp₁A : p₁ ∈ A := (hAmem p₁).mpr ⟨0, by omega, by omega, hP0⟩
  have hPm1B : (P[m + 1]'hm) ∈ B := (hBmem _).mpr ⟨m + 1, hm, by omega, rfl⟩
  -- "Since p₁, pᵢ₊₁ both have neighbours in F₀ ..."
  obtain ⟨wa, hwaF₀, hadjwa⟩ := hZnbr' p₁ hp₁Z
  obtain ⟨wb, hwbF₀, hadjwb⟩ := hZnbr' (P[m + 1]'hm) ((hZmem _).mpr hm1Y)
  -- "... F₀ contains a minimal connected set F such that there are vertices in A and
  -- in B with neighbours in F."
  obtain ⟨F, ⟨hFsub, hFconn, hFA, hFB⟩, hFmin⟩ :=
    exists_min_nat (fun S : Set V => S ⊆ (Z ∪ Y)ᶜ ∧ ConnectedSet G S ∧
        (∃ a ∈ A, ∃ f ∈ S, G.Adj a f) ∧ (∃ b ∈ B, ∃ f ∈ S, G.Adj b f))
      (fun S => S.ncard)
      ⟨(Z ∪ Y)ᶜ, subset_rfl, hF₀conn, ⟨p₁, hp₁A, wa, hwaF₀, hadjwa⟩,
        ⟨_, hPm1B, wb, hwbF₀, hadjwb⟩⟩
  obtain ⟨a₀, ha₀A, fa, hfaF, hadja⟩ := hFA
  obtain ⟨b₀, hb₀B, fb, hfbF, hadjb⟩ := hFB
  -- "From the minimality of F it is disjoint from V(P)."
  have hFnotP : ∀ z ∈ F, z ∉ P := by
    intro z hzF hzP
    have hzF₀ := (hF₀mem z).mp (hFsub hzF)
    obtain ⟨j, hj, hjz⟩ := List.getElem_of_mem hzP
    have hjm : j ≠ m := by
      rintro rfl
      apply hzF₀.1
      rw [← hjz]
      exact hmY
    rcases Nat.lt_or_ge j m with hlt | hge
    · -- `z ∈ A`; shrink `F` towards the `B`-attachment
      have hzA : z ∈ A := (hAmem z).mpr ⟨j, hj, hlt, hjz⟩
      have hfbz : fb ≠ z := by
        intro hfz
        obtain ⟨l, hl, hlm, hlb⟩ := (hBmem b₀).mp hb₀B
        have hadj2 : G.Adj (P[l]'hl) (P[j]'hj) := by
          rw [hlb, hjz, ← hfz]; exact hadjb
        have hcases := (Workspace.ProofLemmas.PathBasics.path_adj_iff hP hl hj).mp hadj2
        omega
      obtain ⟨D, hDF, hzD, hfbD, hDconn, hDadj, hDcard⟩ := shrink hFconn hzF hfbF hfbz
      obtain ⟨d, hdD, hdadj⟩ := hDadj
      have := hFmin D ⟨hDF.trans hFsub, hDconn, ⟨z, hzA, d, hdD, hdadj⟩,
        ⟨b₀, hb₀B, fb, hfbD, hadjb⟩⟩
      omega
    · -- `z ∈ B`; shrink `F` towards the `A`-attachment
      have hgt : m < j := by omega
      have hzB : z ∈ B := (hBmem z).mpr ⟨j, hj, hgt, hjz⟩
      have hfaz : fa ≠ z := by
        intro hfz
        obtain ⟨l, hl, hlm, hla⟩ := (hAmem a₀).mp ha₀A
        have hadj2 : G.Adj (P[l]'hl) (P[j]'hj) := by
          rw [hla, hjz, ← hfz]; exact hadja
        have hcases := (Workspace.ProofLemmas.PathBasics.path_adj_iff hP hl hj).mp hadj2
        omega
      obtain ⟨D, hDF, hzD, hfaD, hDconn, hDadj, hDcard⟩ := shrink hFconn hzF hfaF hfaz
      obtain ⟨d, hdD, hdadj⟩ := hDadj
      have := hFmin D ⟨hDF.trans hFsub, hDconn, ⟨a₀, ha₀A, fa, hfaD, hadja⟩,
        ⟨z, hzB, d, hdD, hdadj⟩⟩
      omega
  -- "and disjoint from X ∪ Y since X ⊆ Z, contrary to 18.6"
  have hFcond : ∀ f ∈ F, f ∉ X ∪ Y ∧ f ∉ P := by
    intro f hf
    have hfF₀ := (hF₀mem f).mp (hFsub hf)
    refine ⟨?_, hFnotP f hf⟩
    rintro (h | h)
    · exact hfF₀.1 (hXYcompl f h)
    · exact hfF₀.2 h
  have hFY : ∀ f ∈ F, ¬ VertexComplete G f Y := fun f hf => ((hF₀mem f).mp (hFsub hf)).1
  obtain ⟨q, hqpath, hqinfix, hqatt, hqint, -⟩ :=
    thm_18_6 G hG X Y P p₁ pₙ hopt hPfrom.2.1 hPfrom.2.2 F hFcond hFconn hFY
  -- the two attachments straddle `pᵢ`, so `pᵢ` lies in the interior of the subpath
  obtain ⟨la, hla, hlam, hlaeq⟩ := (hAmem a₀).mp ha₀A
  obtain ⟨lb, hlb, hlbm, hlbeq⟩ := (hBmem b₀).mp hb₀B
  have ha₀P : a₀ ∈ P := by rw [← hlaeq]; exact List.getElem_mem _
  have hb₀P : b₀ ∈ P := by rw [← hlbeq]; exact List.getElem_mem _
  have ha₀q : a₀ ∈ q := hqatt a₀ ⟨ha₀P, fa, hfaF, hadja⟩
  have hb₀q : b₀ ∈ q := hqatt b₀ ⟨hb₀P, fb, hfbF, hadjb⟩
  obtain ⟨r, hrlen, hrget⟩ := infix_getElem hqinfix
  obtain ⟨k₁, hk₁, hk₁eq⟩ := List.getElem_of_mem ha₀q
  obtain ⟨k₂, hk₂, hk₂eq⟩ := List.getElem_of_mem hb₀q
  have hidx₁ : r + k₁ = la := by
    by_contra hc
    refine Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hP
      (show r + k₁ < P.length by omega) hla hc ?_
    rw [hrget k₁ hk₁ (by omega), hk₁eq, hlaeq]
  have hidx₂ : r + k₂ = lb := by
    by_contra hc
    refine Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hP
      (show r + k₂ < P.length by omega) hlb hc ?_
    rw [hrget k₂ hk₂ (by omega), hk₂eq, hlbeq]
  have hrm : r + (m - r) = m := by omega
  have hqm : (q[m - r]'(by omega)) = (P[m]'hm0) := by
    have hh := hrget (m - r) (by omega) (by omega)
    rw [← hh]
    simp only [hrm]
  have hmem : (P[m]'hm0) ∈ SPGT.interior q := by
    rw [← hqm]
    exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hqpath (by omega)
      (by omega) (by omega)
  exact hqint _ hmem hmY


end SPGT

end Workspace.Statements.S18
