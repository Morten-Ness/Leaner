import Mathlib

open scoped Polynomial

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}

variable {a b : R} {bi : K}

theorem denomsClearable_natDegree (i : R →+* K) (f : R[X]) (a : R) (bu : bi * i b = 1) :
    DenomsClearable a b f.natDegree f i := denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

