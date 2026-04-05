import Mathlib

variable {R A : Type*}

theorem RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) [ExpChar A p] : ExpChar R p := by
  cases ‹ExpChar A p› with
  | zero => haveI := f.charZero; exact .zero
  | prime hp => haveI := f.charP H p; exact .prime hp

