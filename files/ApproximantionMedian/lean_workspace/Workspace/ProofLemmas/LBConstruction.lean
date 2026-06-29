import Mathlib
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.LambdaStarDef

open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.LambdaStarDef

namespace Workspace.ProofLemmas.LBConstruction

/-- μ = (λ*)^{q/(q−1)}. -/
noncomputable def mu (q : ℝ) : ℝ := (lambda_star q) ^ (q / (q - 1))

/-- K = ((1−a*)/a* · μ/(1−μ))^{1/q}. -/
noncomputable def Kconst (q : ℝ) : ℝ :=
  ((1 - a_star q) / (a_star q) * (mu q / (1 - mu q))) ^ ((1 : ℝ) / q)

/-- c* = K/(1+K). -/
noncomputable def c_star (q : ℝ) : ℝ := Kconst q / (1 + Kconst q)

/-- k = ⌊a*·d⌋ (natural-number floor). -/
noncomputable def kCount (q : ℝ) (d : ℕ) : ℕ := ⌊a_star q * (d : ℝ)⌋₊

/-- Number of Type-I points: d·t. -/
noncomputable def numTypeI (q : ℝ) (d t : ℕ) : ℕ := d * t

/-- Number of Type-II points: (d−2k)·t (natural-number subtraction). -/
noncomputable def numTypeII (q : ℝ) (d t : ℕ) : ℕ := (d - 2 * kCount q d) * t

/-- Total number of points: n = d·t + (d−2k)·t. -/
noncomputable def nCount (q : ℝ) (d t : ℕ) : ℕ := numTypeI q d t + numTypeII q d t

/-- Type-I activation predicate: coordinate `j` lies in the length-`k` cyclic
block starting at shift `s`. -/
def typeIActive (q : ℝ) (d : ℕ) (s j : ℕ) : Prop :=
  ((j + d - s % d) % d) < kCount q d

noncomputable instance (q : ℝ) (d s j : ℕ) : Decidable (typeIActive q d s j) :=
  inferInstanceAs (Decidable (((j + d - s % d) % d) < kCount q d))

/-- Bool form of the Type-I activation predicate. -/
noncomputable def typeIActiveB (q : ℝ) (d : ℕ) (s j : ℕ) : Bool :=
  decide (((j + d - s % d) % d) < kCount q d)

/-- The lower-bound placement `P_LB`. The first `d·t` indices are Type-I
points (with cyclic-shift `s = i % d`), the rest are Type-II points (all-ones). -/
noncomputable def P_LB (q : ℝ) (d t : ℕ) :
    Fin (nCount q d t) → Fin d → ℝ :=
  fun i j =>
    if i.val < numTypeI q d t then
      (if typeIActiveB q d (i.val % d) j.val then 1 / (1 - c_star q) else 0)
    else
      1

/-- The optimal facility `f = (1,…,1)`. -/
def f_opt (d : ℕ) : Fin d → ℝ := fun _ => 1

end Workspace.ProofLemmas.LBConstruction
