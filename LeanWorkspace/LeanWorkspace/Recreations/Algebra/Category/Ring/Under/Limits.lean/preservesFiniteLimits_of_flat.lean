import Mathlib

variable {R S : CommRingCat.{u}}

variable (f : R ⟶ S)

theorem preservesFiniteLimits_of_flat (hf : RingHom.Flat f.hom) :
    PreservesFiniteLimits (CommRingCat.Under.pushout f) where
  preservesFiniteLimits _ := letI : Algebra R S := f.hom.toAlgebra
    haveI : Module.Flat R S := hf
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

