import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g := (AddCommGrpCat.epi_iff_surjective _).1 hS.epi_g

