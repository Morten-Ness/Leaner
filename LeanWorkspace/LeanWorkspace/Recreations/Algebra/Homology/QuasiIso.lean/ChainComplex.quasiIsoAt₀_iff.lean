import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem ChainComplex.quasiIsoAt₀_iff {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 1 0 0).HasHomology] [(L.sc' 1 0 0).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 1 0 0).map f) := quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

