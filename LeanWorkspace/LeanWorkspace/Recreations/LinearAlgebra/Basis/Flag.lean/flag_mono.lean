import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem flag_mono (b : Module.Basis (Fin n) R M) : Monotone b.flag := Fin.monotone_iff_le_succ.2 fun k ↦ by rw [Module.Basis.flag_succ]; exact le_sup_right

