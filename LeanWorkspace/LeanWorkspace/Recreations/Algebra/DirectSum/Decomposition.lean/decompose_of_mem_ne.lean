import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (DirectSum.decompose ℳ x j : M) = 0 := by
  rw [DirectSum.decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ hij.symm, ZeroMemClass.coe_zero]

