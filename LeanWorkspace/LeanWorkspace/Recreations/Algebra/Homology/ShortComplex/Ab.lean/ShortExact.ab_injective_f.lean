import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f := (AddCommGrpCat.mono_iff_injective _).1 hS.mono_f

