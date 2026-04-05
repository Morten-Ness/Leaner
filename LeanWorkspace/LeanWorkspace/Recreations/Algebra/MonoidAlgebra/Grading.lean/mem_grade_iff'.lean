import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

theorem mem_grade_iff' (m : M) (a : R[M]) :
    a ∈ grade R m ↔ a ∈ (LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) :
      Submodule R R[M]) := by
  rw [AddMonoidAlgebra.mem_grade_iff, Finsupp.support_subset_singleton']
  apply exists_congr
  intro r
  constructor <;> exact Eq.symm

