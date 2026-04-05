import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem update_eq_single_add_erase (f : ι →₀ M) (a : ι) (b : M) :
    f.update a b = single a b + f.erase a := by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

