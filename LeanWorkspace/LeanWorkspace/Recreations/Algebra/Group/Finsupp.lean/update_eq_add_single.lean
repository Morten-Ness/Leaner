import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem update_eq_add_single {f : ι →₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = f + single a b := by
  rw [Finsupp.update_eq_erase_add_single, erase_of_notMem_support (by simpa)]

