/-  Proof attempt for statement 15.2 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 93).

    THE PAPER'S PROOF (paper/proofs/15_2.md, verbatim):

      "Proof.  By 15.1, G admits no skew partition.  Assume first that X u Y = V(G).
       Then Gbar is not connected; let the anticomponents of G be B_1,...,B_k say,
       where k >= 2.  We may assume that G is not complete, and therefore we may
       assume that some B_i, say B_1, has cardinality > 1.  Choose x, y in B_1,
       nonadjacent.  Then ({x,y}, V(G) \ {x,y}) is not a skew partition, and so
       G \ {x,y} is anticonnected.  Hence k = 2 and B_1 = {x,y}.  Similarly B_2 has
       cardinality <= 2, and so |V(G)| <= 4 and the theorem holds.  Now assume that
       G \ (X u Y) is nonnull.  Suppose that V(G) \ (X u Y) is not connected; then
       (V(G) \ (X u Y), X u Y) is a skew partition, a contradiction.  So
       V(G) \ (X u Y) is connected.  Now suppose some x in X has no neighbour in
       V(G) \ (X u Y).  Hence V(G) \ ((X \ {x}) u Y) is not connected, and since G
       admits no skew partition it follows that X = {x}.  This proves 15.2."

    HOW IT MAPS ONTO THE LEAN PROOF.

    * "By 15.1, G admits no skew partition" is `hnoskew`, the contrapositive of
      `thm_15_1` against the hypothesis `hno`.
    * The engine of the first bullet is `not_anticonnected_of_meets`: because `X` is
      complete to `Y`, no edge of `Gbar` joins `X` to `Y`, so no set covered by
      `X u Y` and meeting both of them is anticonnected (walk induction, `walk_stays`).
      This is exactly the paper's "Gbar is not connected", used repeatedly.
    * "({x,y}, V(G) \ {x,y}) is not a skew partition, and so G \ {x,y} is
      anticonnected" is `anticonn_compl_pair` (its first half, "{x,y} is not
      connected", is `pair_not_connected`).
    * "Hence k = 2 and B_1 = {x,y}" is `side_eq_pair`: the anticonnected set
      `V(G) \ {x,y}` cannot meet both sides, so the side containing x and y is exactly
      {x,y}; the other side is then its complement, hence anticonnected, and both are
      anticomponents (`isAnticomponent_side`) -- these are the paper's B_1 and B_2, and
      every anticomponent is one of them.
    * "Similarly B_2 has cardinality <= 2" is `side_eq_pair` again, applied with the
      two sides interchanged, to a nonadjacent pair inside B_2 supplied by
      `exists_nonadj_of_anticonn`.
    * The second bullet is the two skew partitions the paper writes down:
      `((X u Y)^c, X u Y)` and `((V(G) \ ((X \ {x}) u Y)), (X \ {x}) u Y)`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.Statements.S15.Thm_15_1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S15

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

/-! ### Helper lemmas -/

/-- If no edge of `H` leaves `E` inside `D`, a walk of `H|D` starting in `E` stays in `E`. -/
private theorem walk_stays {V : Type*} {H : SimpleGraph V} {D E : Set V}
    (hclosed : ∀ a ∈ E, ∀ b ∈ D, H.Adj a b → b ∈ E)
    {x y : ↥D} (p : (H.induce D).Walk x y) (hx : (x : V) ∈ E) : (y : V) ∈ E := by
  revert hx
  induction p with
  | nil => exact fun h => h
  | @cons a b _ hab _ ih => exact fun ha => ih (hclosed _ ha _ b.2 hab)

/-- The paper's *"`Ḡ` is not connected"*, in the form used throughout the proof: if `S` is
complete to `T` and `D ⊆ S ∪ T` meets both `S` and `T`, then `D` is not anticonnected —
a `Ḡ`-walk inside `D` that starts in `S` can never leave `S`. -/
private theorem not_anticonnected_of_meets {V : Type*} {G : SimpleGraph V} {S T D : Set V}
    (hsub : D ⊆ S ∪ T) (hc : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t)
    {a b : V} (haD : a ∈ D) (haS : a ∈ S) (hbD : b ∈ D) (hbT : b ∈ T) :
    ¬ AnticonnectedSet G D := by
  intro hconn
  obtain ⟨p⟩ := hconn ⟨a, haD⟩ ⟨b, hbD⟩
  have hstay : ∀ u ∈ S, ∀ v ∈ D, Gᶜ.Adj u v → v ∈ S := by
    intro u hu v hv hadj
    rcases hsub hv with h | h
    · exact h
    · exact absurd (hc u hu v h) hadj.2
  exact G.irrefl (hc b (walk_stays hstay p haS) b hbT)

/-- Two distinct nonadjacent vertices do not form a connected set. -/
private theorem pair_not_connected {V : Type*} {G : SimpleGraph V} {x y : V}
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) : ¬ ConnectedSet G ({x, y} : Set V) := by
  intro hconn
  have hx : x ∈ ({x, y} : Set V) := by simp
  have hy : y ∈ ({x, y} : Set V) := by simp
  obtain ⟨p⟩ := hconn ⟨x, hx⟩ ⟨y, hy⟩
  have hstay : ∀ a ∈ ({x} : Set V), ∀ b ∈ ({x, y} : Set V), G.Adj a b → b ∈ ({x} : Set V) := by
    intro a ha b hb hadj
    have ha' : a = x := ha
    have hxb : G.Adj x b := by rw [← ha']; exact hadj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with hb | hb
    · exact hb
    · exact absurd (by rw [← hb]; exact hxb) hnadj
  exact hxy (walk_stays hstay p (rfl : x ∈ ({x} : Set V))).symm

/-- Two distinct nonadjacent vertices do form an *anti*connected set. -/
private theorem anticonn_pair {V : Type*} {G : SimpleGraph V} {x y : V}
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) : AnticonnectedSet G ({x, y} : Set V) := by
  have key : ∀ a b : ↥({x, y} : Set V), (a : V) = x → (b : V) = y →
      (Gᶜ.induce ({x, y} : Set V)).Reachable a b := by
    intro a b ha hb
    have hadj : Gᶜ.Adj (a : V) (b : V) :=
      ⟨by rw [ha, hb]; exact hxy, by rw [ha, hb]; exact hnadj⟩
    exact SimpleGraph.Adj.reachable hadj
  intro u v
  have hu : (u : V) = x ∨ (u : V) = y := u.2
  have hv : (v : V) = x ∨ (v : V) = y := v.2
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · have huv : u = v := Subtype.ext (hu.trans hv.symm)
    rw [huv]
  · exact key u v hu hv
  · exact (key v u hv hu).symm
  · have huv : u = v := Subtype.ext (hu.trans hv.symm)
    rw [huv]

/-- The paper's *"Then `({x,y}, V(G) \ {x,y})` is not a skew partition, and so `G \ {x,y}`
is anticonnected."* -/
private theorem anticonn_compl_pair {V : Type*} {G : SimpleGraph V}
    (hnoskew : ¬ AdmitsSkewPartition G) {x y : V}
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) : AnticonnectedSet G (({x, y} : Set V)ᶜ) := by
  by_contra hcon
  exact hnoskew ⟨{x, y}, ({x, y} : Set V)ᶜ, Set.union_compl_self _, disjoint_compl_right,
    pair_not_connected hxy hnadj, hcon⟩

/-- The paper's *"Hence `k = 2` and `B₁ = {x,y}`"*: if `(S,T)` is a complete pair covering
`V(G)` and `x, y ∈ S` are distinct and nonadjacent, then `S = {x,y}`.  (The anticonnected
set `V(G) \ {x,y}` contains all of `T`, so by `not_anticonnected_of_meets` it can contain
no further vertex of `S`.) -/
private theorem side_eq_pair {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hcov : S ∪ T = Set.univ) (hdisj : Disjoint S T) (hT : T.Nonempty)
    (hc : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t)
    (hnoskew : ¬ AdmitsSkewPartition G) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) :
    S = ({x, y} : Set V) := by
  have hanti := anticonn_compl_pair hnoskew hxy hnadj
  have hsub : (({x, y} : Set V)ᶜ) ⊆ S ∪ T := by rw [hcov]; exact Set.subset_univ _
  obtain ⟨t, htT⟩ := hT
  have htmem : t ∈ (({x, y} : Set V)ᶜ) := by
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact (Set.disjoint_left.mp hdisj hx) htT
    · exact (Set.disjoint_left.mp hdisj hy) htT
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    by_contra hznot
    exact not_anticonnected_of_meets (S := S) (T := T) hsub hc hznot hz htmem htT hanti
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy

/-- Each side of a complete pair covering `V(G)` is, if anticonnected, an anticomponent of
`V(G)` — i.e. one of the paper's `Bᵢ`. -/
private theorem isAnticomponent_side {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hcov : S ∪ T = Set.univ) (hc : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t)
    (hS : S.Nonempty) (hSanti : AnticonnectedSet G S) :
    IsAnticomponent G Set.univ S := by
  refine ⟨Set.subset_univ _, hSanti, ?_⟩
  intro D hSD _ hDconn
  by_contra hne
  obtain ⟨s, hsS⟩ := hS
  obtain ⟨d, hdD, hdS⟩ : ∃ d ∈ D, d ∉ S := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm h hSD)
  have hdmem : d ∈ S ∪ T := by rw [hcov]; exact Set.mem_univ d
  have hdT : d ∈ T := by
    rcases hdmem with h | h
    · exact absurd h hdS
    · exact h
  have hsub : D ⊆ S ∪ T := by rw [hcov]; exact Set.subset_univ _
  exact not_anticonnected_of_meets (S := S) (T := T) hsub hc (hSD hsS) hsS hdD hdT hDconn

/-- An anticonnected set with more than one vertex contains two distinct nonadjacent
vertices — this is the paper's *"we may assume that some `Bᵢ` … has cardinality `> 1`.
Choose `x, y ∈ B₁`, nonadjacent."* -/
private theorem exists_nonadj_of_anticonn {V : Type*} {G : SimpleGraph V} {T : Set V}
    (hanti : AnticonnectedSet G T) (hnsub : ¬ T.Subsingleton) :
    ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ ¬ G.Adj a b := by
  by_contra hcon
  push Not at hcon
  apply hnsub
  intro a haT b hbT
  obtain ⟨p⟩ := hanti ⟨a, haT⟩ ⟨b, hbT⟩
  have hstay : ∀ u ∈ ({a} : Set V), ∀ v ∈ T, Gᶜ.Adj u v → v ∈ ({a} : Set V) := by
    intro u hu v hv hadj
    have hu' : u = a := hu
    exact absurd (hcon u (by rw [hu']; exact haT) v hv hadj.1) hadj.2
  exact (walk_stays hstay p (rfl : a ∈ ({a} : Set V))).symm

/-- The whole content of the first bullet of 15.2, stated symmetrically in the two sides
so that it can be applied whichever side of `(X,Y)` the nonadjacent pair happens to lie in. -/
private theorem bullet_one {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hcov : S ∪ T = Set.univ) (hdisj : Disjoint S T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hc : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t)
    (hnoskew : ¬ AdmitsSkewPartition G) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) :
    (∃ B₁ B₂ : Set V, B₁ ≠ B₂ ∧
        IsAnticomponent G Set.univ B₁ ∧ IsAnticomponent G Set.univ B₂ ∧
        ∀ B : Set V, IsAnticomponent G Set.univ B → B = B₁ ∨ B = B₂) ∧
      (∀ B : Set V, IsAnticomponent G Set.univ B → B.ncard ≤ 2) := by
  -- the swapped data, used for the "similarly" half of the argument
  have hcov' : T ∪ S = Set.univ := by rw [Set.union_comm]; exact hcov
  have hc' : ∀ t ∈ T, ∀ s ∈ S, G.Adj t s := fun t ht s hs => (hc s hs t ht).symm
  -- "Hence k = 2 and B₁ = {x,y}."
  have hSeq : S = ({x, y} : Set V) := side_eq_pair hcov hdisj hT hc hnoskew hx hy hxy hnadj
  have hTeq : T = (({x, y} : Set V))ᶜ := by
    rw [← hSeq]
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz hzS
      exact (Set.disjoint_left.mp hdisj hzS) hz
    · intro z hz
      have hzmem : z ∈ S ∪ T := by rw [hcov]; exact Set.mem_univ z
      rcases hzmem with h | h
      · exact absurd h hz
      · exact h
  have hSanti : AnticonnectedSet G S := by rw [hSeq]; exact anticonn_pair hxy hnadj
  have hTanti : AnticonnectedSet G T := by
    rw [hTeq]; exact anticonn_compl_pair hnoskew hxy hnadj
  have hSac : IsAnticomponent G Set.univ S := isAnticomponent_side hcov hc hS hSanti
  have hTac : IsAnticomponent G Set.univ T := isAnticomponent_side hcov' hc' hT hTanti
  -- every anticomponent is `S` or `T`
  have hall : ∀ B : Set V, IsAnticomponent G Set.univ B → B = S ∨ B = T := by
    intro B hB
    have hBanti : AnticonnectedSet G B := hB.2.1
    have hBsub : B ⊆ S ∪ T := by rw [hcov]; exact Set.subset_univ _
    by_cases hmeetT : ∃ b ∈ B, b ∈ T
    · right
      obtain ⟨b, hbB, hbT⟩ := hmeetT
      have hBT : B ⊆ T := by
        intro z hz
        rcases hBsub hz with h | h
        · exact absurd hBanti (not_anticonnected_of_meets (S := S) (T := T) hBsub hc hz h hbB hbT)
        · exact h
      exact (hB.2.2 T hBT (Set.subset_univ _) hTanti).symm
    · left
      push Not at hmeetT
      have hBS : B ⊆ S := by
        intro z hz
        rcases hBsub hz with h | h
        · exact h
        · exact absurd h (hmeetT z hz)
      exact (hB.2.2 S hBS (Set.subset_univ _) hSanti).symm
  -- `S` and `T` are distinct
  obtain ⟨s₀, hs₀⟩ := hS
  have hST : S ≠ T := by
    intro h
    exact (Set.disjoint_left.mp hdisj hs₀) (h ▸ hs₀)
  -- cardinalities: `|S| = 2` and, "similarly", `|T| ≤ 2`
  have hScard : S.ncard ≤ 2 := by rw [hSeq, Set.ncard_pair hxy]
  have hTcard : T.ncard ≤ 2 := by
    by_cases hsub : T.Subsingleton
    · rcases hsub.eq_empty_or_singleton with h | ⟨t, h⟩ <;> rw [h] <;> simp
    · obtain ⟨a, haT, b, hbT, hab, hnab⟩ := exists_nonadj_of_anticonn hTanti hsub
      have : T = ({a, b} : Set V) :=
        side_eq_pair hcov' hdisj.symm ⟨s₀, hs₀⟩ hc' hnoskew haT hbT hab hnab
      rw [this, Set.ncard_pair hab]
  refine ⟨⟨S, T, hST, hSac, hTac, hall⟩, ?_⟩
  intro B hB
  rcases hall B hB with h | h
  · rw [h]; exact hScard
  · rw [h]; exact hTcard

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **15.2** (printed p. 93)

PAPER: *"Let `G ∈ F₆`, and assume that `G` admits no balanced skew partition.  Let
`X, Y ⊆ V(G)` be nonempty, disjoint, and complete to each other.*

*• If `X ∪ Y = V(G)`, then either `G` is complete, or `Ḡ` has exactly two components, both
with `≤ 2` vertices (and hence `|V(G)| ≤ 4`).*

*• If `X ∪ Y ≠ V(G)`, then `V(G) \ (X ∪ Y)` is connected, and if in addition `|X| > 1`, then
every vertex in `X` has a neighbour in `V(G) \ (X ∪ Y)`."*

Transcription notes.

* The two bullets are two implications with a common set of hypotheses, so the conclusion is
  their conjunction.
* *"`G` is complete"* is: every two distinct vertices of `G` are adjacent.
* *"`Ḡ` has exactly two components"*: the components of `Ḡ` are the maximal connected subsets
  of `V(Ḡ)`, i.e. the *anticomponents* of `V(G)` in the sense of `Core`
  (`IsAnticomponent G Set.univ ·`).  *"Exactly two"* is rendered by exhibiting two distinct
  ones and requiring every one to be one of the two.  (`pdftotext` drops the overline on `Ḡ`
  here; the rendered page, the arXiv source and the printed proof — which argues about *"the
  anticomponents of `G`"* — all confirm `Ḡ`.)
* *"both with `≤ 2` vertices"* is the cardinality bound on every component of `Ḡ`.
* The parenthetical *"(and hence `|V(G)| ≤ 4`)"* is flagged by the authors as a consequence,
  not as a further alternative, so it is **not** a conjunct.
* *"`|X| > 1`"* is `X.Nontrivial`, and *"has a neighbour in `S`"* is `∃ z ∈ S, G.Adj x z`. -/
theorem thm_15_2 (G : SimpleGraph V) (hG : InF6 G)
    (hno : ¬ AdmitsBalancedSkewPartition G)
    (X Y : Set V) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hcomplete : Complete G X Y) :
    (X ∪ Y = Set.univ →
      ((∀ u v : V, u ≠ v → G.Adj u v) ∨
        ((∃ B₁ B₂ : Set V, B₁ ≠ B₂ ∧
            IsAnticomponent G Set.univ B₁ ∧ IsAnticomponent G Set.univ B₂ ∧
            ∀ B : Set V, IsAnticomponent G Set.univ B → B = B₁ ∨ B = B₂) ∧
          (∀ B : Set V, IsAnticomponent G Set.univ B → B.ncard ≤ 2)))) ∧
    (X ∪ Y ≠ Set.univ →
      (ConnectedSet G ((X ∪ Y)ᶜ) ∧
        (X.Nontrivial → ∀ x ∈ X, ∃ z ∈ (X ∪ Y)ᶜ, G.Adj x z))) := by
  -- "By 15.1, G admits no skew partition."
  have hnoskew : ¬ AdmitsSkewPartition G := fun h => hno (thm_15_1 G hG h)
  have hc : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y := hcomplete
  have hc' : ∀ y ∈ Y, ∀ x ∈ X, G.Adj y x := fun y hy x hx => (hc x hx y hy).symm
  constructor
  · -- "Assume first that X ∪ Y = V(G)."
    intro hunion
    -- "We may assume that G is not complete."
    by_cases hcomp : ∀ u v : V, u ≠ v → G.Adj u v
    · exact Or.inl hcomp
    right
    push Not at hcomp
    obtain ⟨u, v, huv, hnadj⟩ := hcomp
    have hmem : ∀ w : V, w ∈ X ∨ w ∈ Y := by
      intro w
      have : w ∈ X ∪ Y := by rw [hunion]; exact Set.mem_univ w
      exact this
    have hunion' : Y ∪ X = Set.univ := by rw [Set.union_comm]; exact hunion
    -- "Choose x, y ∈ B₁, nonadjacent" — the two are on the same side of (X,Y).
    rcases hmem u with huX | huY
    · rcases hmem v with hvX | hvY
      · exact bullet_one hunion hXY hX hY hc hnoskew huX hvX huv hnadj
      · exact absurd (hc u huX v hvY) hnadj
    · rcases hmem v with hvX | hvY
      · exact absurd (hc' u huY v hvX) hnadj
      · exact bullet_one hunion' hXY.symm hY hX hc' hnoskew huY hvY huv hnadj
  · -- "Now assume that G \ (X ∪ Y) is nonnull."
    intro hne
    have hFne : ((X ∪ Y)ᶜ).Nonempty := Set.nonempty_compl.mpr hne
    obtain ⟨x₀, hx₀⟩ := hX
    obtain ⟨y₀, hy₀⟩ := hY
    have hXYsub : (X ∪ Y) ⊆ X ∪ Y := Set.Subset.rfl
    have hXYnotanti : ¬ AnticonnectedSet G (X ∪ Y) :=
      not_anticonnected_of_meets (S := X) (T := Y) hXYsub hc
        (Set.mem_union_left _ hx₀) hx₀ (Set.mem_union_right _ hy₀) hy₀
    constructor
    · -- "Suppose that V(G) \ (X ∪ Y) is not connected; then (V(G) \ (X ∪ Y), X ∪ Y) is a
      -- skew partition, a contradiction."
      by_contra hncon
      exact hnoskew ⟨(X ∪ Y)ᶜ, X ∪ Y, Set.compl_union_self _, disjoint_compl_left,
        hncon, hXYnotanti⟩
    · -- "Now suppose some x ∈ X has no neighbour in V(G) \ (X ∪ Y). …  it follows that X = {x}."
      intro hXnt x hxX
      by_contra hcon
      push Not at hcon
      -- `X` is nontrivial, so there is a second vertex `x'` of `X`
      obtain ⟨x', hx'X, hx'ne⟩ := hXnt.exists_ne x
      -- the paper's `B = (X \ {x}) ∪ Y` and `A = V(G) \ B`
      have hBsub : ((X \ {x}) ∪ Y) ⊆ X ∪ Y := by
        intro z hz
        rcases hz with h | h
        · exact Set.mem_union_left _ h.1
        · exact Set.mem_union_right _ h
      have hx'B : x' ∈ (X \ {x}) ∪ Y := Set.mem_union_left _ ⟨hx'X, hx'ne⟩
      have hy₀B : y₀ ∈ (X \ {x}) ∪ Y := Set.mem_union_right _ hy₀
      have hBnotanti : ¬ AnticonnectedSet G ((X \ {x}) ∪ Y) :=
        not_anticonnected_of_meets (S := X) (T := Y) hBsub hc hx'B hx'X hy₀B hy₀
      -- `A` decomposes as `{x} ∪ (V(G) \ (X ∪ Y))`, and `x` is isolated in `G|A`
      have hAdesc : ∀ b : V, b ∈ (((X \ {x}) ∪ Y)ᶜ) → b = x ∨ b ∈ (X ∪ Y)ᶜ := by
        intro b hb
        by_cases hbX : b ∈ X
        · left
          by_contra hbne
          exact hb (Set.mem_union_left _ ⟨hbX, hbne⟩)
        · right
          intro hbXY
          rcases hbXY with h | h
          · exact hbX h
          · exact hb (Set.mem_union_right _ h)
      have hxA : x ∈ (((X \ {x}) ∪ Y)ᶜ) := by
        intro hmem
        rcases hmem with h | h
        · exact h.2 rfl
        · exact (Set.disjoint_left.mp hXY hxX) h
      obtain ⟨w, hw⟩ := hFne
      have hwA : w ∈ (((X \ {x}) ∪ Y)ᶜ) := fun hmem => hw (hBsub hmem)
      have hwx : w ≠ x := by
        intro h
        exact hw (Set.mem_union_left _ (h ▸ hxX))
      have hAnotconn : ¬ ConnectedSet G ((((X \ {x}) ∪ Y))ᶜ) := by
        intro hconn
        obtain ⟨p⟩ := hconn ⟨x, hxA⟩ ⟨w, hwA⟩
        have hstay : ∀ a ∈ ({x} : Set V), ∀ b ∈ (((X \ {x}) ∪ Y)ᶜ), G.Adj a b →
            b ∈ ({x} : Set V) := by
          intro a ha b hb hadj
          have ha' : a = x := ha
          have hxb : G.Adj x b := by rw [← ha']; exact hadj
          rcases hAdesc b hb with h | h
          · exact h
          · exact absurd hxb (hcon b h)
        exact hwx (walk_stays hstay p (rfl : x ∈ ({x} : Set V)))
      exact hnoskew ⟨(((X \ {x}) ∪ Y))ᶜ, (X \ {x}) ∪ Y, Set.compl_union_self _,
        disjoint_compl_left, hAnotconn, hBnotanti⟩


end SPGT

end Workspace.Statements.S15
