import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [AddCommMonoidWithOne R]

theorem C_ofNat (n : ℕ) [n.AtLeastTwo] :
    (.C (ofNat(n) : R) : QuadraticAlgebra R a b) = ofNat(n) := by
  ext <;> rfl

