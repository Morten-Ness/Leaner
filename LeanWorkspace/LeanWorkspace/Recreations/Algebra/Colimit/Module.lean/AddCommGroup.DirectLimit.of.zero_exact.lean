import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

theorem of.zero_exact [IsDirectedOrder ι] [DirectedSystem G fun i j h ↦ f i j h] (i x)
    (h : AddCommGroup.DirectLimit.of G f i x = 0) : ∃ j hij, f i j hij x = 0 := Module.DirectLimit.of.zero_exact h

