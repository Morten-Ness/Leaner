FAIL
import Mathlib

variable {R α β : Type*} [CommSemiring R]

variable (e : α ≃ β)

theorem algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    letI : Semiring α := Function.Injective.semiring e.injective e (by simp) (by simp)
      (by simp [map_add]) (by simp [map_mul])
    letI : Algebra R α := e.symm.toRingHom.toAlgebra
    algebraMap R α r = e.symm (algebraMap R β r) := by
  rfl
