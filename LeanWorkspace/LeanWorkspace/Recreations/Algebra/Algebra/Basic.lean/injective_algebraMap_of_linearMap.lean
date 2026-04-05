import Mathlib

open scoped Algebra

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] (b : F →ₗ[F] E)

theorem injective_algebraMap_of_linearMap (hb : Function.Injective b) :
    Function.Injective (algebraMap F E) := fun x y e ↦ hb <| by
  rw [← mul_one x, ← mul_one y, ← smul_eq_mul, ← smul_eq_mul,
    map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, e]

