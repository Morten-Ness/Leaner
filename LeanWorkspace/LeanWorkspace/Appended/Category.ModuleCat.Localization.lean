import Mathlib

section

variable (R : Type u) [CommRing R]

theorem localizedModuleFunctor_map_exact [Small.{v} R] (S : Submonoid R)
    (T : ShortComplex (ModuleCat.{v} R)) (h : T.Exact) :
    (T.map (ModuleCat.localizedModuleFunctor S)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
    (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ h

end
