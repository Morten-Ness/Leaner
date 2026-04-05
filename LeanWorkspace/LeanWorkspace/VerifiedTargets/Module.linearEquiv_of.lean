import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable [Nonempty ι] [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]

theorem linearEquiv_of {i g} : Module.DirectLimit.linearEquiv _ _ (Module.DirectLimit.of _ _ G f i g) = ⟦⟨i, g⟩⟧ := by
  simp [Module.DirectLimit.linearEquiv]; rfl

