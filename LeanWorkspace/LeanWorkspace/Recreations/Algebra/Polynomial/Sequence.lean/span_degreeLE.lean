import Mathlib

open scoped Function

variable (R : Type*)

variable [Ring R] (S : Sequence R)

theorem span_degreeLE {m : ℕ} (hCoeff : ∀ i ≤ m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iic m) = degreeLE R m := by
  rw [← Set.Iio_succ_eq_Iic, Polynomial.Sequence.span_degreeLT _ (fun i hi => hCoeff i (Order.lt_succ_iff.mp hi))]
  simp [← Polynomial.degreeLT_succ_eq_degreeLE]

