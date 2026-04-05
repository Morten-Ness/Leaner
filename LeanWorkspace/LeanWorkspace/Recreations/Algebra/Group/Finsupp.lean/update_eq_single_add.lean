import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem update_eq_single_add {f : ι →₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = single a b + f := by
  rw [Finsupp.update_eq_single_add_erase, erase_of_notMem_support (by simpa)]

