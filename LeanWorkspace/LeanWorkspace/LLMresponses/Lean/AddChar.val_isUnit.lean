FAIL
import Mathlib

theorem val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) := by
  simpa using φ.isUnit a
