import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem Function.Injective.isMulTorsionFree [Monoid M] [Monoid N] [IsMulTorsionFree N]
    (f : M →* N) (hf : Function.Injective f) : IsMulTorsionFree M where
  pow_left_injective n hn x y hxy := hf <| IsMulTorsionFree.pow_left_injective hn <| by
    simpa using congrArg f hxy

-- completely uninteresting lemmas about coercion to function, that all homs need

