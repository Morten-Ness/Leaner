import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem self_mem_flag_iff [Nontrivial R] (b : Module.Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} :
    b i ∈ b.flag k ↔ i.castSucc < k := b.self_mem_span_image

