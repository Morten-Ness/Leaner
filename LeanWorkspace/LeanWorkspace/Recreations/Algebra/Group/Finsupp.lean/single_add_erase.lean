import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem single_add_erase (a : ι) (f : ι →₀ M) : single a (f a) + f.erase a = f := by
  rw [← Finsupp.update_eq_single_add_erase, Function.update_self]

