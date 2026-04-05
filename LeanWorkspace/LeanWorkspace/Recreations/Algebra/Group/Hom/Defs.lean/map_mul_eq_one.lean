import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N]

variable [FunLike F M N]

theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) :
    f a * f b = 1 := by
  rw [← map_mul, h, map_one]

