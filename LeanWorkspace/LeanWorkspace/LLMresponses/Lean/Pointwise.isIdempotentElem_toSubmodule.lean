FAIL
import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem isIdempotentElem_toSubmodule (S : Subalgebra R A) :
    IsIdempotentElem S.toSubmodule := by
  rw [show S.toSubmodule * S.toSubmodule = S.toSubmodule ↔ IsIdempotentElem S.toSubmodule by rfl]
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_mul] at hx
    exact hx S.toSubmodule
      ⟨by
        rintro _ ⟨y, hy, z, hz, rfl⟩
        exact S.mul_mem hy hz, by simp⟩
  · intro hx
    rw [Submodule.mem_mul]
    intro p hp
    exact hp ⟨1, S.one_mem, x, hx, by simp⟩
