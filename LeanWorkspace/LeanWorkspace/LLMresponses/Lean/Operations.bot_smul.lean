FAIL
import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem bot_smul : (⊥ : Submodule R A) • N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_smul] at hx
  rcases hx with ⟨a, ha, y, hy, hxy⟩
  rw [Submodule.mem_bot] at ha
  rw [← hxy, ha]
  simp
