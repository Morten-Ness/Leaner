import Mathlib

variable {R S F K : Type*}

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

theorem prod_X_sub_C_eq [CommRing S] {x y z : S} :
    (Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C y) * (Polynomial.X - Polynomial.C z) =
      Cubic.toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩ := by
  rw [← one_mul <| Polynomial.X - Polynomial.C x, ← C_1, Cubic.C_mul_prod_X_sub_C_eq, one_mul, one_mul, one_mul]

