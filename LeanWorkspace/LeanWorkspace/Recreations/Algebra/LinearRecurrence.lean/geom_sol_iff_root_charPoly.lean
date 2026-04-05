import Mathlib

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

theorem geom_sol_iff_root_charPoly (q : R) :
    (E.IsSolution fun n ↦ q ^ n) ↔ E.charPoly.IsRoot q := by
  rw [LinearRecurrence.charPoly, Polynomial.IsRoot.def, Polynomial.eval]
  simp only [Polynomial.eval₂_finset_sum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.mp h, mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring

