import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem self_mem_flag (b : Module.Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} (h : i.castSucc < k) :
    b i ∈ b.flag k := subset_span <| mem_image_of_mem _ h

