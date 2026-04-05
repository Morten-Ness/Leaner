import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem _root_.IsSMulRegular.polynomial {S : Type*} [SMulZeroClass S R] {a : S}
    (ha : IsSMulRegular R a) : IsSMulRegular R[X] a
  | ⟨_x⟩, ⟨_y⟩, h => congr_arg _ <| ha.finsupp (Polynomial.ofFinsupp.inj h)
