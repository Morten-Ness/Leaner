import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem CochainComplex.quasiIsoAt₀_iff {K L : CochainComplex C ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 0 0 1).HasHomology] [(L.sc' 0 0 1).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 0 0 1).map f) := quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

