import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

theorem exists_of₂ [Nonempty ι] [IsDirectedOrder ι] (z w : Module.DirectLimit G f) :
    ∃ i x y, Module.DirectLimit.of R ι G f i x = z ∧ Module.DirectLimit.of R ι G f i y = w := have ⟨i, x, hx⟩ := Module.DirectLimit.exists_of z
  have ⟨j, y, hy⟩ := Module.DirectLimit.exists_of w
  have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  ⟨k, f i k hik x, f j k hjk y, by rw [Module.DirectLimit.of_f, hx], by rw [Module.DirectLimit.of_f, hy]⟩

