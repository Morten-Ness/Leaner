import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem erase_add (a : ι) (f f' : ι →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s; by_cases hs : s = a
  · rw [hs, Finsupp.add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [Finsupp.add_apply, erase_ne hs, erase_ne hs, erase_ne hs, Finsupp.add_apply]

