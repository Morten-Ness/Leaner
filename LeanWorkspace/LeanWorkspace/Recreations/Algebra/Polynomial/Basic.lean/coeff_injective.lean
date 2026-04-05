import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem coeff_injective : Function.Injective (Polynomial.coeff : R[X] → ℕ → R) := by
  rintro ⟨p⟩ ⟨q⟩
  simp only [Polynomial.coeff, DFunLike.coe_fn_eq, imp_self, ofFinsupp.injEq]

