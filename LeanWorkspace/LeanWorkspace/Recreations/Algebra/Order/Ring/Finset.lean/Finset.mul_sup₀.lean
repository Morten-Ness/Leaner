import Mathlib

variable {R ι : Type*} [LinearOrder R] [NonUnitalNonAssocSemiring R]
  [CanonicallyOrderedAdd R] [OrderBot R]

theorem Finset.mul_sup₀ (s : Finset ι) (f : ι → R) (a : R) :
    a * s.sup f = s.sup (a * f ·) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, mul_max, ← IH]

