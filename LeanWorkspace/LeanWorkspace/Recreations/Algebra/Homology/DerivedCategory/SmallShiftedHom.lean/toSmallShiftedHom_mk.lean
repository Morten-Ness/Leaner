import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} {n : ℤ}
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

theorem toSmallShiftedHom_mk (x : Cocycle K L n) :
    (CochainComplex.HomComplex.CohomologyClass.mk x).toSmallShiftedHom =
      SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm x) := rfl

