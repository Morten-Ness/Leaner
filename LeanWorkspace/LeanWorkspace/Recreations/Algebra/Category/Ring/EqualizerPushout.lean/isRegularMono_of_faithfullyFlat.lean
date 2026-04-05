import Mathlib

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

theorem isRegularMono_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsRegularMono f := isRegularMono_of_regularMono (CommRingCat.regularMonoOfFaithfullyFlat f hf)

