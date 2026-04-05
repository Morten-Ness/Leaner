import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem ShortExact.moduleCat_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g := hS.surjective_g

