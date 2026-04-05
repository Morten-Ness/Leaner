import Mathlib

variable {M N : Type*}

theorem map_dvd [Semigroup M] [Semigroup N] {F : Type*} [FunLike F M N] [MulHomClass F M N]
    (f : F) {a b} : a ∣ b → f a ∣ f b
  | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩
