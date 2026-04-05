import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem flag_lt_flag [Nontrivial R] (hij : i < j) : b.flag i < b.flag j := Module.Basis.flag_strictMono _ hij

