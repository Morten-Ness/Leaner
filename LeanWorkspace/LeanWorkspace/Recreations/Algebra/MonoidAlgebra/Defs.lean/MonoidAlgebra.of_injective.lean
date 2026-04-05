import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [MulOneClass M]

theorem of_injective [Nontrivial R] : Function.Injective (MonoidAlgebra.of R M) := fun a b h ↦ by
  simpa using (single_eq_single_iff _ _ _ _).mp h

