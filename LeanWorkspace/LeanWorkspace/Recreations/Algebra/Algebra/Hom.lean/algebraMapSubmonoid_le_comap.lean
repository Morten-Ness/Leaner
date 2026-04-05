import Mathlib

variable (R : Type u) (A : Type v) (B : Type w)

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (M : Submonoid R) {B : Type w} [Semiring B] [Algebra R B] {A}

theorem algebraMapSubmonoid_le_comap (f : A →ₐ[R] B) :
    algebraMapSubmonoid A M ≤ (algebraMapSubmonoid B M).comap f.toRingHom := by
  rw [← Algebra.algebraMapSubmonoid_map_eq M f]
  exact Submonoid.le_comap_map (Algebra.algebraMapSubmonoid A M)

