import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

theorem of_f {i j hij x} : Module.DirectLimit.of R ι G f j (f i j hij x) = Module.DirectLimit.of R ι G f i x := by
  simpa using Module.DirectLimit.of_f (R := R) (ι := ι) (G := G) (f := f) (i := i) (j := j) hij x
