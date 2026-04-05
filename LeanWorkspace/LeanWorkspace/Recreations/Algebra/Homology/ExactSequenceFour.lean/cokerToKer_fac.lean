import Mathlib

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

theorem cokerToKer_fac (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ hS.cokerToKer k hk ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac hS k hk _ _ (cokernelIsCokernel _) (kernelIsKernel _)

