import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (f : Π i, M i →ₗ[R] N i)

theorem range_lmap :
    LinearMap.range (DirectSum.lmap f) =
      (Submodule.pi Set.univ (fun i ↦ LinearMap.range (f i))).comap (DirectSum.coeFnLinearMap R) := DFinsupp.range_mapRangeLinearMap f

