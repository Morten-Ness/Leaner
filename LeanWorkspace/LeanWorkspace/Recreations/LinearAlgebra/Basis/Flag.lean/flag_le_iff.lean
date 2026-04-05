import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem flag_le_iff (b : Module.Basis (Fin n) R M) {k p} :
    b.flag k ≤ p ↔ ∀ i : Fin n, i.castSucc < k → b i ∈ p := span_le.trans forall_mem_image

