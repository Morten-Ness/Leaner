import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable {G f} [DirectedSystem G (f · · ·)] [IsDirectedOrder ι]

theorem of.zero_exact {i x} (H : Module.DirectLimit.of R ι G f i x = 0) :
    ∃ j hij, f i j hij x = (0 : G j) := by
  convert Module.DirectLimit.exists_eq_of_of_eq (H.trans (map_zero <| _).symm)
  rw [map_zero]

