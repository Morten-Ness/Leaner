import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

set_option backward.isDefEq.respectTransparency false in
theorem shiftMap_homologyFunctor_map_Q
    {K L : CochainComplex C ℤ} {n : ℤ} (f : K ⟶ L⟦n⟧)
    (a a' : ℤ) (h : n + a = a' := by lia) :
    (DerivedCategory.homologyFunctor C 0).shiftMap (ShiftedHom.map f Q) a a' h =
    (DerivedCategory.homologyFunctorFactors C a).hom.app _ ≫
      (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap f a a' h ≫
        (DerivedCategory.homologyFunctorFactors C a').inv.app _ := by
  rw [← ShiftedHom.map_naturality_1 f (quotientCompQhIso C),
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Functor.shiftMap_comp', Functor.shiftMap_comp,
    ShiftedHom.comp_map, DerivedCategory.shiftMap_homologyFunctor_map_Qh ..,
    DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj,
    DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj,
    HomotopyCategory.homologyFunctor_shiftMap]
  simp [DerivedCategory.shift_homologyFunctor, ← Functor.map_comp, ← Functor.map_comp_assoc]

