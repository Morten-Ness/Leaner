import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.of_algHom {f : R[X]} {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (hf : Polynomial.Splits (f.map (algebraMap R A))) (e : A →ₐ[R] B) :
    Polynomial.Splits (f.map (algebraMap R B)) := by
  rw [← e.comp_algebraMap, ← map_map]
  apply hf.map

