import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem flag_strictMono [Nontrivial R] (b : Module.Basis (Fin n) R M) : StrictMono b.flag := Fin.strictMono_iff_lt_succ.2 fun _ ↦ by simp [Module.Basis.flag_succ]

