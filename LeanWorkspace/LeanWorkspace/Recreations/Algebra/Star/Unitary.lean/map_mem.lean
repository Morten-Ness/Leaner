import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem map_mem {F : Type*} [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S]
    (f : F) {r : R} (hr : r ∈ unitary R) : f r ∈ unitary S := by
  rw [Unitary.mem_iff] at hr
  simpa [map_star, map_mul] using And.intro congr(f $(hr.1)) congr(f $(hr.2))

