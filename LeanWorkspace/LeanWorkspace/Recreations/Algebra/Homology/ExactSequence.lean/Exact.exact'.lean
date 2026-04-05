import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem Exact.exact' (hS : S.Exact) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    (S.sc' hS.toIsComplex i j k).Exact := by
  subst hij hjk
  exact hS.exact i hk

