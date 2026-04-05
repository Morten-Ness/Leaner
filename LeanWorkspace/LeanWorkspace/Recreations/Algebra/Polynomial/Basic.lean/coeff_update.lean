import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_update (p : R[X]) (n : ℕ) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a := by
  ext
  simp only [Polynomial.coeff, Function.update, Function.update_apply, coe_update, AddMonoidAlgebra.update, ofCoeff,
    AddMonoidAlgebra.coeff]

