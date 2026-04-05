import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem centralizer_centralizer_centralizer {s : Set A} :
    Subalgebra.centralizer R s.centralizer.centralizer = Subalgebra.centralizer R s := by
  ext x
  constructor
  · intro hx y hy
    exact hx y (by
      intro z hz
      exact (hz y hy).symm)
  · intro hx y hy
    exact (hy x hx).symm
