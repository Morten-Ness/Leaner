import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N] [FunLike F M N] [MonoidHomClass F M N]

theorem map_exists_left_inv (f : F) {x : M} (hx : ∃ y, y * x = 1) : ∃ y, y * f x = 1 := let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

