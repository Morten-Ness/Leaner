import Mathlib

section

variable {R S : CommRingCat.{u}}

variable [Algebra R S]

theorem equalizer_comp {A B : CommRingCat.Under R} (f g : A ⟶ B) :
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ f =
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ g := by
  ext (a : AlgHom.equalizer (toAlgHom f) (toAlgHom g))
  exact a.property

end

section

variable {R S : CommRingCat.{u}}

variable (f : R ⟶ S)

theorem preservesFiniteLimits_of_flat (hf : RingHom.Flat f.hom) :
    PreservesFiniteLimits (CommRingCat.Under.pushout f) where
  preservesFiniteLimits _ := letI : Algebra R S := f.hom.toAlgebra
    haveI : Module.Flat R S := hf
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

end
