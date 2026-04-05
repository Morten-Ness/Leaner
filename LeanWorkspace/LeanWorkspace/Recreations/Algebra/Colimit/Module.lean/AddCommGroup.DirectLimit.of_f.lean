import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

theorem of_f {i j} (hij) (x) : AddCommGroup.DirectLimit.of G f j (f i j hij x) = AddCommGroup.DirectLimit.of G f i x := Module.DirectLimit.of_f

