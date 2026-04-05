import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : AddCommGroup.DirectLimit G f → Prop}
    (z : AddCommGroup.DirectLimit G f) (ih : ∀ i x, C (AddCommGroup.DirectLimit.of G f i x)) : C z := Module.DirectLimit.induction_on z ih

