import Mathlib

open scoped Function in -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => Polynomial.X - Polynomial.C (s i)) := fun _ _ hij =>
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit

