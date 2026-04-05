import Mathlib

variable {α β : Type*}

theorem Function.Injective.isDomain [Semiring α] [IsDomain α] [Semiring β] {F}
    [FunLike F β α] [MonoidWithZeroHomClass F β α] (f : F) (hf : Function.Injective f) : IsDomain β where
  __ := domain_nontrivial f (map_zero _) (map_one _)
  __ := hf.isCancelMulZero f (map_zero _) (map_mul _)

