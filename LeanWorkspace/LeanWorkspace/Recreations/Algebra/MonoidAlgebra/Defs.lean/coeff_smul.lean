import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable {A : Type*} [SMulZeroClass A R]

theorem coeff_smul (a : A) (x : R[M]) : MonoidAlgebra.coeff (a • x) = a • MonoidAlgebra.coeff x := rfl

