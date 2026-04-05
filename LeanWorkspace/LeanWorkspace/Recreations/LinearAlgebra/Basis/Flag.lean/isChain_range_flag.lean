import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem isChain_range_flag (b : Module.Basis (Fin n) R M) : IsChain (· ≤ ·) (Set.range b.flag) := Module.Basis.flag_mono b.isChain_range

