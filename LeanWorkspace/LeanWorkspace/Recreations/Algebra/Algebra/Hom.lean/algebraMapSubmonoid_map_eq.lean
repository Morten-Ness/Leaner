import Mathlib

variable (R : Type u) (A : Type v) (B : Type w)

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (M : Submonoid R) {B : Type w} [Semiring B] [Algebra R B] {A}

theorem algebraMapSubmonoid_map_eq (f : A →ₐ[R] B) :
    (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M := by
  ext x
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    simp only [AlgHom.commutes]
    use r
  · rintro ⟨r, hr, rfl⟩
    simp only [Submonoid.mem_map]
    use (algebraMap R A r)
    simp only [AlgHom.commutes, and_true]
    use r

