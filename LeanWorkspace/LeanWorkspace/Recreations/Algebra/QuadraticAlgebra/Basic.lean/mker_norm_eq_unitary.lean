import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem mker_norm_eq_unitary :
    MonoidHom.mker (@QuadraticAlgebra.norm R a b _) = unitary (QuadraticAlgebra R a b) := Submonoid.ext fun _ => QuadraticAlgebra.norm_eq_one_iff_mem_unitary

