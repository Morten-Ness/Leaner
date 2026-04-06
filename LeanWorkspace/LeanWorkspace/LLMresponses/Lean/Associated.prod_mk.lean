import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem prod_mk {p : Multiset M} : (p.map Associates.mk).prod = Associates.mk p.prod := by
  induction p using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, ih]
      simpa using (Associates.mk_mul_mk : Associates.mk a * Associates.mk s.prod = Associates.mk (a * s.prod))
