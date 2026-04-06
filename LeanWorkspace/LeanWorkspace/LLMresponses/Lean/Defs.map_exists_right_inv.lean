import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N] [FunLike F M N] [MonoidHomClass F M N]

theorem map_exists_right_inv (f : F) {x : M} (hx : ∃ y, x * y = 1) : ∃ y, f x * y = 1 := by
  rcases hx with ⟨y, hy⟩
  refine ⟨f y, ?_⟩
  rw [← map_mul f x y, hy, map_one]
