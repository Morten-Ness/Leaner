import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

theorem IsTorsionBy.quotient (N : Submodule R M) {r : R}
    (h : IsTorsionBy R M r) : IsTorsionBy R (M ⧸ N) r := (Module.isTorsionBy_quotient_iff N r).mpr fun x => @h x ▸ N.zero_mem

