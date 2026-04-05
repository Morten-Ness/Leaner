import Mathlib

variable {R S F K : Type*}

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

theorem C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} :
    Polynomial.C w * (Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C y) * (Polynomial.X - Polynomial.C z) =
      Cubic.toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ := by
  simp only [Cubic.toPoly, C_neg, C_add, C_mul]
  ring1

