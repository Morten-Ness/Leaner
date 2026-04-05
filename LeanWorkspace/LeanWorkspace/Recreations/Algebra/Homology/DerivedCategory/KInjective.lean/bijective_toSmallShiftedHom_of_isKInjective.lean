import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (K L : CochainComplex C ℤ) (n : ℤ)
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

set_option backward.isDefEq.respectTransparency false in
theorem bijective_toSmallShiftedHom_of_isKInjective [L.IsKInjective] :
    Function.Bijective (toSmallShiftedHom.{w} (K := K) (L := L) (n := n)) := by
  letI := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective,
    ← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

