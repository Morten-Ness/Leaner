import Mathlib

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem leftMulMatrix_injective : Function.Injective (Algebra.leftMulMatrix b) := fun x x' h ↦
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).injective h]
    _ = x' := mul_one x'

