import Mathlib

open scoped DirectSum

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem Submodule.isSemisimple_torsionBy_of_irreducible {a : R} (h : Irreducible a) :
    IsSemisimpleModule R (torsionBy R M a) := haveI := PrincipalIdealRing.isMaximal_of_irreducible h
  letI := Ideal.Quotient.field (R ∙ a)
  (isSemisimpleModule_iff ..).mpr (submodule_torsionBy_orderIso a).complementedLattice

