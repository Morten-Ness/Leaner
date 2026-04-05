import Mathlib

open scoped Polynomial

variable {R S : Type*}

theorem Polynomial.toLaurent_apply [Semiring R] (p : R[X]) :
    toLaurent p = p.toFinsupp.mapDomain (↑) := rfl

