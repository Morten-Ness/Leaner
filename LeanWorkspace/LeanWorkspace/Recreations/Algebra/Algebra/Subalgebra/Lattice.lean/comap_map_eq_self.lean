import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem comap_map_eq_self {f : A →ₐ[R] B} {S : Subalgebra R A}
    (h : f ⁻¹' {0} ⊆ S) : (S.map f).comap f = S := by
  convert Subalgebra.comap_map_eq f S
  rwa [left_eq_sup, Algebra.adjoin_le_iff]

