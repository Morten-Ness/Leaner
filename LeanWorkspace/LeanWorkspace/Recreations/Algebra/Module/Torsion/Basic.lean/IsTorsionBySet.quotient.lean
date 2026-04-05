import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

theorem IsTorsionBySet.quotient (N : Submodule R M) {s}
    (h : IsTorsionBySet R M s) : IsTorsionBySet R (M ⧸ N) s := (Module.isTorsionBySet_quotient_iff N s).mpr fun x r h' => @h x ⟨r, h'⟩ ▸ N.zero_mem

