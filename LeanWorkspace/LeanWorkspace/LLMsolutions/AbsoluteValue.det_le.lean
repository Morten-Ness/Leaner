import Mathlib

open scoped Nat

variable {R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_le {A : Matrix n n R} {abv : AbsoluteValue R S} {x : S} (hx : ∀ i j, abv (A i j) ≤ x) :
    abv A.det ≤ (Fintype.card n)! • x ^ Fintype.card n := by
  simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    Matrix.det_le (A := A) (abv := abv) (x := x) hx
