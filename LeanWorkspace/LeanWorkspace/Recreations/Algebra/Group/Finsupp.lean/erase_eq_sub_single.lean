import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem erase_eq_sub_single (f : ι →₀ G) (a : ι) : f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a' a with (rfl | h)
  · simp
  · simp [h]

