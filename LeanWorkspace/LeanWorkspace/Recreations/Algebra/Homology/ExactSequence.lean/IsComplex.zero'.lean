import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem IsComplex.zero' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    S.map' i j ≫ S.map' j k = 0 := by
  subst hij hjk
  exact hS.zero i hk

