import Mathlib

section

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} {n : ℤ}
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

theorem equiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) :
    SmallShiftedHom.equiv _ DerivedCategory.Q (CochainComplex.HomComplex.CohomologyClass.mk x).toSmallShiftedHom =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q := by
  simp [CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom_mk]

end
