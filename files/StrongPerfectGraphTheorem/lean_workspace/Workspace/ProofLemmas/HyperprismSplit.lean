import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.ProofLemmas.HyperprismRungStructure
import Workspace.ProofLemmas.HyperprismClaim2Setup

/-!
# Splitting every strip of a hyperprism in two (10.6, claim (2))

The printed proof of claim (2) of **10.6** runs the following paragraph twice — once on p. 61
(the `n` even block) and once, verbatim, on p. 62 (the `n` odd block):

> *"For `i = 1,2,3` let `A'ᵢ` be … and let `A''ᵢ = Aᵢ \ A'ᵢ`; … We have shown so far that every
> `i`-rung is either between `A'ᵢ` and `B'ᵢ` or between `A''ᵢ` and `B''ᵢ`.  Let `C'ᵢ` be the
> union of the interiors of the `i`-rungs between `A'ᵢ` and `B'ᵢ`, and `C''ᵢ` the union of the
> interiors of the `i`-rungs between `A''ᵢ` and `B''ᵢ`.  We observe that `Cᵢ = C'ᵢ ∪ C''ᵢ`.
> Moreover, `C'ᵢ ∩ C''ᵢ = ∅`, for otherwise there would be an `i`-rung between `A'ᵢ` and
> `B''ᵢ`.  For the same reason there are no edges between `A'ᵢ ∪ C'ᵢ` and `C''ᵢ ∪ B''ᵢ`, and no
> edges between `A''ᵢ ∪ C''ᵢ` and `C'ᵢ ∪ B'ᵢ`."*

`IsRungSplit` is the hypothesis *"every `i`-rung is either between `A'ᵢ` and `B'ᵢ` or between
`A''ᵢ` and `B''ᵢ`"* (with `P = A'`, `Q = B'`), and this module derives the whole paragraph from
it.  Every derivation is one call to `HyperprismRungStructure.exists_rung_join`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismSplit

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismRungStructure
open Workspace.ProofLemmas.HyperprismClaim2Setup

variable {V : Type*} {G : SimpleGraph V} {A B C P Q : Fin 3 → Set V}

/-- *"every `i`-rung is either between `A'ᵢ` and `B'ᵢ` or between `A''ᵢ` and `B''ᵢ`"*, with
`P = A'` and `Q = B'`. -/
structure IsRungSplit (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V) : Prop where
  PA : ∀ m : Fin 3, P m ⊆ A m
  QB : ∀ m : Fin 3, Q m ⊆ B m
  dich : ∀ (m : Fin 3) (p : List V) (a b : V), IsRungFrom G A B C m p a b →
      (a ∈ P m ∧ b ∈ Q m) ∨ (a ∉ P m ∧ b ∉ Q m)

/-- `C'ₘ` — the union of the interiors of the `m`-rungs between `A'ₘ` and `B'ₘ`. -/
def Cp (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V) (m : Fin 3) : Set V :=
  {v | ∃ (p : List V) (a b : V),
    IsRungFrom G A B C m p a b ∧ a ∈ P m ∧ b ∈ Q m ∧ v ∈ SPGT.interior p}

/-- `C''ₘ` — the union of the interiors of the `m`-rungs between `A''ₘ` and `B''ₘ`. -/
def Cpp (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V) (m : Fin 3) : Set V :=
  {v | ∃ (p : List V) (a b : V),
    IsRungFrom G A B C m p a b ∧ a ∉ P m ∧ b ∉ Q m ∧ v ∈ SPGT.interior p}

/-- *"every vertex of `A'ₘ` is the `A`-end of an `m`-rung between `A'ₘ` and `B'ₘ`"*. -/
theorem exists_rung_prime_of_mem_P (hH : IsHyperprism G A B C) (hs : IsRungSplit G A B C P Q)
    {m : Fin 3} {a : V} (ha : a ∈ P m) :
    ∃ (p : List V) (b : V), IsRungFrom G A B C m p a b ∧ b ∈ Q m := by
  obtain ⟨p, b, hp⟩ := exists_rung_from_A hH m (hs.PA m ha)
  rcases hs.dich m p a b hp with ⟨-, hb⟩ | ⟨hcon, -⟩
  · exact ⟨p, b, hp, hb⟩
  · exact absurd ha hcon

theorem exists_rung_prime_of_mem_Q (hH : IsHyperprism G A B C) (hs : IsRungSplit G A B C P Q)
    {m : Fin 3} {b : V} (hb : b ∈ Q m) :
    ∃ (p : List V) (a : V), IsRungFrom G A B C m p a b ∧ a ∈ P m := by
  obtain ⟨p, a, hp⟩ := exists_rung_from_B hH m (hs.QB m hb)
  rcases hs.dich m p a b hp with ⟨ha, -⟩ | ⟨-, hcon⟩
  · exact ⟨p, a, hp, ha⟩
  · exact absurd hb hcon

theorem exists_rung_dprime_of_notMem_P (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q) {m : Fin 3} {a : V} (ha : a ∈ A m) (ha' : a ∉ P m) :
    ∃ (p : List V) (b : V), IsRungFrom G A B C m p a b ∧ b ∉ Q m := by
  obtain ⟨p, b, hp⟩ := exists_rung_from_A hH m ha
  rcases hs.dich m p a b hp with ⟨hcon, -⟩ | ⟨-, hb⟩
  · exact absurd hcon ha'
  · exact ⟨p, b, hp, hb⟩

theorem exists_rung_dprime_of_notMem_Q (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q) {m : Fin 3} {b : V} (hb : b ∈ B m) (hb' : b ∉ Q m) :
    ∃ (p : List V) (a : V), IsRungFrom G A B C m p a b ∧ a ∉ P m := by
  obtain ⟨p, a, hp⟩ := exists_rung_from_B hH m hb
  rcases hs.dich m p a b hp with ⟨-, hcon⟩ | ⟨ha, -⟩
  · exact absurd hcon hb'
  · exact ⟨p, a, hp, ha⟩

theorem Cp_subset_C (m : Fin 3) : Cp G A B C P Q m ⊆ C m := by
  rintro v ⟨p, a, b, hp, -, -, hv⟩
  exact hp.2.2.2 v hv

theorem Cpp_subset_C (m : Fin 3) : Cpp G A B C P Q m ⊆ C m := by
  rintro v ⟨p, a, b, hp, -, -, hv⟩
  exact hp.2.2.2 v hv

/-- *"We observe that `Cᵢ = C'ᵢ ∪ C''ᵢ`."* -/
theorem C_eq (hH : IsHyperprism G A B C) (hs : IsRungSplit G A B C P Q) (m : Fin 3) :
    C m = Cp G A B C P Q m ∪ Cpp G A B C P Q m := by
  ext v
  constructor
  · intro hv
    obtain ⟨p, a, b, hp, hvp⟩ := (mem_C_iff hH m).mp hv
    rcases hs.dich m p a b hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨p, a, b, hp, ha, hb, hvp⟩
    · exact Or.inr ⟨p, a, b, hp, ha, hb, hvp⟩
  · rintro (h | h)
    · exact Cp_subset_C m h
    · exact Cpp_subset_C m h

/-- *"Moreover, `C'ᵢ ∩ C''ᵢ = ∅`, for otherwise there would be an `i`-rung between `A'ᵢ` and
`B''ᵢ`."* -/
theorem Cp_Cpp_disjoint (hH : IsHyperprism G A B C) (hs : IsRungSplit G A B C P Q)
    (m : Fin 3) : Disjoint (Cp G A B C P Q m) (Cpp G A B C P Q m) := by
  rw [Set.disjoint_left]
  rintro v ⟨p, a, b, hp, ha, hb, hvp⟩ ⟨p', a', b', hp', ha', hb', hvp'⟩
  obtain ⟨r, hr⟩ := exists_rung_splice hH hp hp' hvp hvp'
  rcases hs.dich m r a b' hr with ⟨-, hcon⟩ | ⟨hcon, -⟩
  · exact hb' hcon
  · exact hcon ha

/-- *"there are no edges between `A'ᵢ ∪ C'ᵢ` and `C''ᵢ ∪ B''ᵢ`"*. -/
theorem no_edge_prime_dprime (hH : IsHyperprism G A B C) (hs : IsRungSplit G A B C P Q)
    (m : Fin 3) {x y : V} (hx : x ∈ P m ∪ Cp G A B C P Q m)
    (hy : y ∈ Cpp G A B C P Q m ∪ (B m \ Q m)) : ¬ G.Adj x y := by
  intro hadj
  -- a primed rung whose `dropLast` contains `x`
  obtain ⟨p, a, b, hp, ha, hb, hxp⟩ :
      ∃ (p : List V) (a b : V), IsRungFrom G A B C m p a b ∧ a ∈ P m ∧ b ∈ Q m ∧
        x ∈ p.dropLast := by
    rcases hx with hx | hx
    · obtain ⟨p, b, hp, hb⟩ := exists_rung_prime_of_mem_P hH hs hx
      exact ⟨p, x, b, hp, hx, hb, mem_dropLast_A_end hH hp⟩
    · obtain ⟨p, a, b, hp, ha, hb, hxp⟩ := hx
      exact ⟨p, a, b, hp, ha, hb, mem_dropLast_of_mem_interior hp hxp⟩
  -- a double-primed rung whose `tail` contains `y`
  obtain ⟨p', a', b', hp', ha', hb', hyp⟩ :
      ∃ (p' : List V) (a' b' : V), IsRungFrom G A B C m p' a' b' ∧ a' ∉ P m ∧ b' ∉ Q m ∧
        y ∈ p'.tail := by
    rcases hy with hy | hy
    · obtain ⟨p', a', b', hp', ha', hb', hyp⟩ := hy
      exact ⟨p', a', b', hp', ha', hb', mem_tail_of_mem_interior hp' hyp⟩
    · obtain ⟨p', a', hp', ha'⟩ := exists_rung_dprime_of_notMem_Q hH hs hy.1 hy.2
      exact ⟨p', a', y, hp', ha', hy.2, mem_tail_B_end hH hp'⟩
  obtain ⟨r, hr⟩ := exists_rung_join hH hp hp' (Or.inr ⟨x, hxp, y, hyp, hadj⟩)
  rcases hs.dich m r a b' hr with ⟨-, hcon⟩ | ⟨hcon, -⟩
  · exact hb' hcon
  · exact hcon ha

/-- *"and no edges between `A''ᵢ ∪ C''ᵢ` and `C'ᵢ ∪ B'ᵢ`"*. -/
theorem no_edge_dprime_prime (hH : IsHyperprism G A B C) (hs : IsRungSplit G A B C P Q)
    (m : Fin 3) {x y : V} (hx : x ∈ (A m \ P m) ∪ Cpp G A B C P Q m)
    (hy : y ∈ Cp G A B C P Q m ∪ Q m) : ¬ G.Adj x y := by
  intro hadj
  obtain ⟨p, a, b, hp, ha, hb, hxp⟩ :
      ∃ (p : List V) (a b : V), IsRungFrom G A B C m p a b ∧ a ∉ P m ∧ b ∉ Q m ∧
        x ∈ p.dropLast := by
    rcases hx with hx | hx
    · obtain ⟨p, b, hp, hb⟩ := exists_rung_dprime_of_notMem_P hH hs hx.1 hx.2
      exact ⟨p, x, b, hp, hx.2, hb, mem_dropLast_A_end hH hp⟩
    · obtain ⟨p, a, b, hp, ha, hb, hxp⟩ := hx
      exact ⟨p, a, b, hp, ha, hb, mem_dropLast_of_mem_interior hp hxp⟩
  obtain ⟨p', a', b', hp', ha', hb', hyp⟩ :
      ∃ (p' : List V) (a' b' : V), IsRungFrom G A B C m p' a' b' ∧ a' ∈ P m ∧ b' ∈ Q m ∧
        y ∈ p'.tail := by
    rcases hy with hy | hy
    · obtain ⟨p', a', b', hp', ha', hb', hyp⟩ := hy
      exact ⟨p', a', b', hp', ha', hb', mem_tail_of_mem_interior hp' hyp⟩
    · obtain ⟨p', a', hp', ha'⟩ := exists_rung_prime_of_mem_Q hH hs hy
      exact ⟨p', a', y, hp', ha', hy, mem_tail_B_end hH hp'⟩
  obtain ⟨r, hr⟩ := exists_rung_join hH hp hp' (Or.inr ⟨x, hxp, y, hyp, hadj⟩)
  rcases hs.dich m r a b' hr with ⟨hcon, -⟩ | ⟨-, hcon⟩
  · exact ha hcon
  · exact hcon hb'

/-- The interior of any rung of a Berge hyperprism is nonempty: it has even length `≥ 1`, hence
`≥ 2`, hence at least three vertices. -/
theorem interior_ne_nil_of_rung (hG : Berge G) (hH : IsHyperprism G A B C) {m : Fin 3}
    {p : List V} {a b : V} (hp : IsRungFrom G A B C m p a b) :
    ∃ v, v ∈ SPGT.interior p := by
  have hev : Even (SPGT.pathLength p) := rung_even hG hH hp
  have h1 : 1 ≤ SPGT.pathLength p := rung_one_le_pathLength hH hp
  have h2 : 2 ≤ SPGT.pathLength p := by
    rcases hev with ⟨c, hc⟩
    omega
  have hlen : p.length = SPGT.pathLength p + 1 :=
    PathBasics.length_eq_pathLength_add_one hp.2.2.1.1
  have h3 : 3 ≤ p.length := by omega
  have hne := PathBasics.interior_ne_nil hp.2.2.1.1 h3
  exact List.exists_mem_of_ne_nil _ hne

/-- A nonempty `A'ₘ` forces `B'ₘ` and `C'ₘ` nonempty (rungs have even length `≥ 2`, so a
nonempty interior). -/
theorem nonempty_of_P_nonempty (hG : Berge G) (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q) {m : Fin 3} (h : (P m).Nonempty) :
    (Q m).Nonempty ∧ (Cp G A B C P Q m).Nonempty := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨p, b, hp, hb⟩ := exists_rung_prime_of_mem_P hH hs ha
  obtain ⟨v, hv⟩ := interior_ne_nil_of_rung hG hH hp
  exact ⟨⟨b, hb⟩, ⟨v, p, a, b, hp, ha, hb, hv⟩⟩

/-- A nonempty `A''ₘ` forces `B''ₘ` and `C''ₘ` nonempty. -/
theorem nonempty_of_notP_nonempty (hG : Berge G) (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q) {m : Fin 3} (h : (A m \ P m).Nonempty) :
    (B m \ Q m).Nonempty ∧ (Cpp G A B C P Q m).Nonempty := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨p, b, hp, hb⟩ := exists_rung_dprime_of_notMem_P hH hs ha.1 ha.2
  obtain ⟨v, hv⟩ := interior_ne_nil_of_rung hG hH hp
  exact ⟨⟨b, hp.2.1, hb⟩, ⟨v, p, a, b, hp, ha.2, hb, hv⟩⟩

end Workspace.ProofLemmas.HyperprismSplit
