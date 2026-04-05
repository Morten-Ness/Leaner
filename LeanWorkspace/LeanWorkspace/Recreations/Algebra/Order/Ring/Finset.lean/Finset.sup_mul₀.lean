import Mathlib

variable {R ι : Type*} [LinearOrder R] [NonUnitalNonAssocSemiring R]
  [CanonicallyOrderedAdd R] [OrderBot R]

theorem Finset.sup_mul₀ (s : Finset ι) (f : ι → R) (a : R) :
    s.sup f * a = s.sup (f · * a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ IH => simp only [sup_insert, max_mul, ← IH]

