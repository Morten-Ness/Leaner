import Mathlib

variable {R S G M N O ι : Type*}

variable [CommSemiring R]

theorem single_one_comm [MulOneClass M] (r : R) (f : R[M]) :
    single (1 : M) r * f = f * single (1 : M) r := MonoidAlgebra.single_commute .one_left (.all _) f

