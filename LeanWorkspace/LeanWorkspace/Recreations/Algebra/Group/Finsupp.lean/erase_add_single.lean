import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem erase_add_single (a : ι) (f : ι →₀ M) : f.erase a + single a (f a) = f := by
  rw [← Finsupp.update_eq_erase_add_single, Function.update_self]

