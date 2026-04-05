import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem flag_last (b : Module.Basis (Fin n) R M) : b.flag (.last n) = ⊤ := by
  simp [Module.Basis.flag]

