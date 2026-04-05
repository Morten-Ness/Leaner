import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem flag_zero (b : Module.Basis (Fin n) R M) : b.flag 0 = ⊥ := by simp [Module.Basis.flag]

