import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem Exact.moduleCat_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f.hom = LinearMap.ker g.hom) :
    (CategoryTheory.ShortComplex.moduleCatMkOfKerLERange f g (by rw [hfg])).Exact := by
  simpa only [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker] using hfg

