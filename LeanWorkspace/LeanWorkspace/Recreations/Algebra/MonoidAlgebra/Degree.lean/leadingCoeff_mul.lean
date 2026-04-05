import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem leadingCoeff_mul [NoZeroDivisors R]
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).leadingCoeff D = p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [AddMonoidAlgebra.leadingCoeff_zero, zero_mul, AddMonoidAlgebra.leadingCoeff_zero]
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [AddMonoidAlgebra.leadingCoeff_zero, mul_zero, AddMonoidAlgebra.leadingCoeff_zero]
  rw [← AddMonoidAlgebra.apply_supDegree_add_supDegree hD hadd, ← AddMonoidAlgebra.supDegree_mul hD hadd ?_ hp hq, AddMonoidAlgebra.leadingCoeff]
  apply mul_ne_zero <;> rwa [Ne, AddMonoidAlgebra.leadingCoeff_eq_zero hD]

