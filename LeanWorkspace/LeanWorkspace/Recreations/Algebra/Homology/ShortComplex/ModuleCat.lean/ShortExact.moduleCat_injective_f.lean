import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem ShortExact.moduleCat_injective_f (hS : S.ShortExact) :
    Function.Injective S.f := hS.injective_f

