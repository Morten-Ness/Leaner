import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem support_single_add {a : ι} {b : M} {f : ι →₀ M} (ha : a ∉ f.support) (hb : b ≠ 0) :
    support (single a b + f) = cons a f.support ha := by
  classical
  have H := support_single_ne_zero a hb
  rw [Finsupp.support_add_eq, H, cons_eq_insert, insert_eq]
  rwa [H, disjoint_singleton_left]

