import Mathlib

variable {C : Type*} [Category C] [Preadditive C] [Balanced C] {n : ℕ}
  {S : ComposableArrows C (n + 3)} (hS : S.Exact)

theorem cokerIsoKer_hom_fac (k : ℕ) (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ (hS.cokerIsoKer k).hom ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  CategoryTheory.ComposableArrows.IsComplex.cokerToKer_fac hS.toIsComplex k

