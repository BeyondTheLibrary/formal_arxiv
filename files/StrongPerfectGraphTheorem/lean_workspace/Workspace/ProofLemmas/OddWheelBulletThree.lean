import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.Types.Appearances
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelBullets12
import Workspace.Statements.S15.Thm_15_2
import Workspace.Statements.S16.Thm_16_2

/-!
# The main argument of 16.3, up to the third bullet of 16.2

PAPER (16.3, printed p. 101), everything between claim (1) and the construction of `C'`:

> *"Since `(C,Y)` is an odd wheel, `C` has at least two segments, and therefore there are vertices
> `u,v` in `C` with different wheel-parity and neither of them `Y`-complete.  Let `X` be the set of
> all `Y`-complete vertices in `V(G)`.  Then `|X| > 1`, since `|X ∩ V(C)| ≥ 4`; so by 15.2, we may
> assume that `V(G) \ (X ∪ Y)` is nonempty and connected ( = `Z` say), and every vertex in `X` has a
> neighbour in it, for otherwise `G` admits a balanced skew partition and the theorem holds.  In
> particular `u, v ∈ Z`, so there is a minimal connected subset `F` of `Z` such that there are two
> vertices of `C \ X` (say `p, q`) of opposite wheel-parity, both with neighbours in `F`.  Since
> `p, q` have opposite wheel-parity and are not `Y`-complete, they are not adjacent.  From the
> minimality of `F`, `F` is a path, and no vertex of `F` is in `C`.  By 16.2 and (1), there is a
> 3-vertex path `p₁-p₂-p₃` in `C`, all `Y`-complete, and a path `p₁-f₁-⋯-f_k-p₃` with interior in
> `F`, such that there are no edges between `{f₁,…,f_k}` and `{p₄,…,pₙ}`."*

`exists_bullet_three` below is exactly that, with claim (1) taken as a hypothesis.  Composing it
with `Workspace.ProofLemmas.OddWheelRebuild` (the `C'` construction and the closing count) closes
16.3.

Two remarks on the printed text.

* *"From the minimality of `F`, `F` is a path"* is not needed and is not proved here: 16.2 wants
  only that `F` is connected and misses `C`, `Y` and the `Y`-complete vertices.
* *"no vertex of `F` is in `C`"* is the component-of-`F \ {z}` argument (`shrink`), the same one
  that discharges the corresponding step of 18.7.  It needs the parity dichotomy: a rim vertex
  `z ∈ F` is of opposite parity to `p` or to `q`, because `p, q` are of opposite parity to each
  other and wheel-parity is two-valued (`OddWheelParityFacts.exists_parity'`).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelBulletThree

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-! ### Connectivity helpers -/

private theorem walk_stays {G : SimpleGraph V} {D E : Set V}
    (hclosed : ∀ a ∈ E, ∀ b ∈ D, G.Adj a b → b ∈ E)
    {x y : ↥D} (p : (G.induce D).Walk x y) (hx : (x : V) ∈ E) : (y : V) ∈ E := by
  revert hx
  induction p with
  | nil => exact fun h => h
  | @cons a b _ hab _ ih => exact fun ha => ih (hclosed _ ha _ b.2 hab)

/-- In a connected set with two distinct vertices, every vertex has a neighbour. -/
theorem exists_adj_of_connected {G : SimpleGraph V} {S : Set V} (hS : ConnectedSet G S) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : ∃ f ∈ S, G.Adj x f := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p⟩ := hS ⟨x, hx⟩ ⟨y, hy⟩
  have hclosed : ∀ a ∈ ({x} : Set V), ∀ b ∈ S, G.Adj a b → b ∈ ({x} : Set V) := by
    intro a ha b hb hab
    have ha' : a = x := ha
    rw [ha'] at hab
    exact absurd hab (hcon b hb)
  exact hxy (walk_stays hclosed p (rfl : x ∈ ({x} : Set V))).symm

/-- The engine behind *"from the minimality of `F`"* — see `ProofAttempts/thm_18_7/Attempt_2.lean`. -/
private theorem shrink [Fintype V] {G : SimpleGraph V} {F : Set V} {v w : V}
    (hFconn : ConnectedSet G F) (hvF : v ∈ F) (hwF : w ∈ F) (hwv : w ≠ v) :
    ∃ D : Set V, D ⊆ F ∧ v ∉ D ∧ w ∈ D ∧ ConnectedSet G D ∧
      (∃ d ∈ D, G.Adj v d) ∧ D.ncard < F.ncard := by
  classical
  have hwmem : w ∈ F \ ({v} : Set V) := ⟨hwF, hwv⟩
  obtain ⟨D, hD, hwD⟩ :=
    ComponentsOfSetBasics.exists_isComponent_mem G (F \ ({v} : Set V)) hwmem
  have hDsub : D ⊆ F := fun z hz => (hD.1 hz).1
  have hvD : v ∉ D := fun hz => (hD.1 hz).2 rfl
  refine ⟨D, hDsub, hvD, hwD, hD.2.1, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hclosed : ∀ a ∈ D, ∀ b ∈ F, G.Adj a b → b ∈ D := by
      intro a haD b hbF hab
      have hbv : b ≠ v := fun hbe => hcon a haD (hbe ▸ hab.symm)
      have hconn : ConnectedSet G (D ∪ ({b} : Set V)) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hD.2.1 ⟨a, haD, hab.symm⟩
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

/-! ### The main statement -/

/-- PAPER (16.3, printed p. 101): everything from *"Since `(C,Y)` is an odd wheel, `C` has at
least two segments"* to *"…such that there are no edges between `{f₁,…,f_k}` and `{p₄,…,pₙ}`"*,
with claim (1) as a hypothesis. -/
theorem exists_bullet_three [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : InF6 G) (hno : ¬ AdmitsBalancedSkewPartition G)
    {C : List V} {Y : Set V} (hodd : IsOddWheel G C Y)
    (hclaim1 : ∀ z : V, z ∉ C → z ∉ Y → ¬ VertexComplete G z Y →
      ∀ x y : V, G.Adj z x → G.Adj z y → ¬ G.Adj x y → ¬ OppositeWheelParity G C Y x y) :
    ∃ (F : Set V) (p₁ p₂ p₃ : V) (P : List V),
      (∀ f ∈ F, f ∉ C) ∧ (∀ f ∈ F, f ∉ Y) ∧ ConnectedSet G F ∧
      (∀ f ∈ F, ¬ VertexComplete G f Y) ∧
      (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
      VertexComplete G p₁ Y ∧ VertexComplete G p₂ Y ∧ VertexComplete G p₃ Y ∧
      IsPathFrom G P p₁ p₃ ∧ (∀ x ∈ SPGT.interior P, x ∈ F) ∧
      (∀ x ∈ SPGT.interior P, ∀ u ∈ C, u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → ¬ G.Adj x u) := by
  classical
  have hBerge : Berge G := hG.1.1.1
  have hw : IsWheel G C Y := hodd.1
  have hhole : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hhole heven
  obtain ⟨hYne, hYanti, hCY⟩ := hw.2.1
  obtain ⟨a₀, b₀, c₀, d₀, ha₀C, hb₀C, hc₀C, hd₀C, hab₀, hcd₀, -, -, -, -⟩ := hw.2.2
  -- "there are vertices `u, v` in `C` with different wheel-parity, neither `Y`-complete"
  obtain ⟨u₀, w₀, hu₀C, hw₀C, hu₀nc, hw₀nc, hopp₀⟩ :=
    OddWheelParityFacts.exists_two_nonComplete_opposite hBerge hw hodd
  have hπ₀ : π u₀ ≠ π w₀ := fun h =>
    hopp₀.2.2.2 ((hπ u₀ w₀ hu₀C hw₀C hopp₀.1).mpr h)
  -- "Let `X` be the set of all `Y`-complete vertices in `V(G)`."
  obtain ⟨X, hXmem⟩ : ∃ X : Set V, ∀ x : V, x ∈ X ↔ VertexComplete G x Y :=
    ⟨{z : V | VertexComplete G z Y}, fun _ => Iff.rfl⟩
  have hXY : Disjoint X Y :=
    Set.disjoint_left.mpr fun z hzX hzY => G.irrefl ((hXmem z).mp hzX z hzY)
  have hXcompl : Complete G X Y := fun z hz => (hXmem z).mp hz
  have ha₀X : a₀ ∈ X := (hXmem a₀).mpr hab₀.2.1
  have hb₀X : b₀ ∈ X := (hXmem b₀).mpr hab₀.2.2
  have hXne : X.Nonempty := ⟨a₀, ha₀X⟩
  have hXnt : X.Nontrivial := ⟨a₀, ha₀X, b₀, hb₀X, hab₀.1.ne⟩
  -- "`V(G) \ (X ∪ Y)` is nonempty"
  have hXYuniv : X ∪ Y ≠ Set.univ := by
    intro h
    have hmem : u₀ ∈ X ∪ Y := by rw [h]; trivial
    rcases hmem with h' | h'
    · exact hu₀nc ((hXmem u₀).mp h')
    · exact hCY u₀ hu₀C h'
  -- "so by 15.2, we may assume …"
  obtain ⟨-, hb2⟩ :=
    _root_.Workspace.Statements.S15.SPGT.thm_15_2 G hG hno X Y hXne hYne hXY hXcompl
  obtain ⟨hZconn, hZnbr⟩ := hb2 hXYuniv
  have hZnbr' := hZnbr hXnt
  have hu₀Z : u₀ ∈ (X ∪ Y)ᶜ := by
    rintro (h | h)
    · exact hu₀nc ((hXmem u₀).mp h)
    · exact hCY u₀ hu₀C h
  have hw₀Z : w₀ ∈ (X ∪ Y)ᶜ := by
    rintro (h | h)
    · exact hw₀nc ((hXmem w₀).mp h)
    · exact hCY w₀ hw₀C h
  -- "there is a minimal connected subset `F` of `Z` such that …"
  obtain ⟨F, ⟨hFsub, hFconn, hFatt⟩, hFmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun S : Set V => S ⊆ (X ∪ Y)ᶜ ∧ ConnectedSet G S ∧
        ∃ p ∈ C, ∃ q ∈ C, ¬ VertexComplete G p Y ∧ ¬ VertexComplete G q Y ∧ π p ≠ π q ∧
          (∃ f ∈ S, G.Adj p f) ∧ (∃ f ∈ S, G.Adj q f))
      (fun S => S.ncard)
      ⟨(X ∪ Y)ᶜ, subset_rfl, hZconn, u₀, hu₀C, w₀, hw₀C, hu₀nc, hw₀nc, hπ₀,
        exists_adj_of_connected hZconn hu₀Z hw₀Z hopp₀.1,
        exists_adj_of_connected hZconn hw₀Z hu₀Z (Ne.symm hopp₀.1)⟩
  obtain ⟨p, hpC, q, hqC, hpnc, hqnc, hpq, ⟨fp, hfpF, hadjp⟩, ⟨fq, hfqF, hadjq⟩⟩ := hFatt
  have hpqne : p ≠ q := fun h => hpq (by rw [h])
  have hFY : ∀ f ∈ F, f ∉ Y := fun f hf hfY => (hFsub hf) (Set.mem_union_right _ hfY)
  have hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y :=
    fun f hf hfc => (hFsub hf) (Set.mem_union_left _ ((hXmem f).mpr hfc))
  -- "Since `p, q` have opposite wheel-parity and are not `Y`-complete, they are not adjacent."
  have hpqnadj : ¬ G.Adj p q := by
    intro hadj
    have := (hπ p q hpC hqC hpqne).mp
      (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hhole heven hpC hqC hadj hpnc)
    exact hpq this
  -- "From the minimality of `F` … no vertex of `F` is in `C`."
  have hFC : ∀ f ∈ F, f ∉ C := by
    intro z hzF hzC
    have hznc : ¬ VertexComplete G z Y := hFnc z hzF
    have hzp2 := hπ2 z
    have hpp2 := hπ2 p
    have hqp2 := hπ2 q
    have hshrinkcase : ∀ (r : V) (fr : V), r ∈ C → ¬ VertexComplete G r Y → π z ≠ π r →
        fr ∈ F → G.Adj r fr → False := by
      intro r fr hrC hrnc hzr hfrF hadjr
      have hfrz : fr ≠ z := by
        intro hfz
        have hadjrz : G.Adj r z := by rw [← hfz]; exact hadjr
        have hrzne : r ≠ z := fun h => hzr (by rw [h])
        have hsame : SameWheelParity G C Y r z :=
          OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete hhole heven hrC hzC
            hadjrz hrnc
        exact hzr ((hπ r z hrC hzC hrzne).mp hsame).symm
      have hfrz' : fr ≠ z := hfrz
      obtain ⟨D, hDF, hzD, hfrD, hDconn, ⟨d, hdD, hdadj⟩, hDcard⟩ :=
        shrink hFconn hzF hfrF hfrz'
      have := hFmin D ⟨hDF.trans hFsub, hDconn, z, hzC, r, hrC, hznc, hrnc, hzr,
        ⟨d, hdD, hdadj⟩, ⟨fr, hfrD, hadjr⟩⟩
      omega
    rcases (by omega : π z ≠ π p ∨ π z ≠ π q) with h | h
    · exact hshrinkcase p fp hpC hpnc h hfpF hadjp
    · exact hshrinkcase q fq hqC hqnc h hfqF hadjq
  -- "By 16.2 and (1) …"
  have hpatt : p ∈ attachments G F {u : V | u ∈ C} := ⟨hpC, fp, hfpF, hadjp⟩
  have hqatt : q ∈ attachments G F {u : V | u ∈ C} := ⟨hqC, fq, hfqF, hadjq⟩
  have h162 := _root_.Workspace.Statements.S16.SPGT.thm_16_2 G hG C Y hw F hFC hFY hFconn hFnc
    (attachments G F {u : V | u ∈ C}) rfl
    ⟨p, hpatt, q, hqatt, hpqne, hpC, hqC, fun hs => hpq ((hπ p q hpC hqC hpqne).mp hs)⟩
    ⟨p, hpatt, q, hqatt, hpqne, hpqnadj⟩
  rcases h162 with ⟨v', hv'F, hWwheel⟩ | ⟨v', hv'F, hdeg, p₁, p₂, p₃, hpath, hblock,
      hW1, hW2, hW3, hother⟩ | ⟨p₁, p₂, p₃, hblock, hY1, hY2, hY3, P, hPfrom, hPF, hPno⟩
  · exact absurd hWwheel (OddWheelBullets12.not_isWheel_union hBerge hw hclaim1
      (hFC v' hv'F) (hFY v' hv'F) (hFnc v' hv'F))
  · exact absurd trivial (fun _ => OddWheelBullets12.not_bullet_two hBerge hw hclaim1
      (hFC v' hv'F) (hFY v' hv'F) (hFnc v' hv'F) hdeg hpath hblock hW1 hW2 hW3 hother)
  · exact ⟨F, p₁, p₂, p₃, P, hFC, hFY, hFconn, hFnc, hblock, hY1, hY2, hY3, hPfrom, hPF, hPno⟩

end Workspace.ProofLemmas.OddWheelBulletThree
