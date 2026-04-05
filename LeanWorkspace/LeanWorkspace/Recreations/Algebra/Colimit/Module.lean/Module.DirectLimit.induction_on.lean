import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : Module.DirectLimit G f → Prop}
    (z : Module.DirectLimit G f) (ih : ∀ i x, C (Module.DirectLimit.of R ι G f i x)) : C z := let ⟨i, x, h⟩ := Module.DirectLimit.exists_of z
  h ▸ ih i x

