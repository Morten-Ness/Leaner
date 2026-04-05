import Mathlib

variable {R : Type*} [Semiring R]
    {ι : Type*}
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    {P : ι → Type*} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

theorem congrLinearEquiv_toLinearMap (u : (i : ι) → N i ≃ₗ[R] P i) :
    (DirectSum.congrLinearEquiv u).toLinearMap = DirectSum.lmap (fun i ↦ (u i).toLinearMap) := rfl

