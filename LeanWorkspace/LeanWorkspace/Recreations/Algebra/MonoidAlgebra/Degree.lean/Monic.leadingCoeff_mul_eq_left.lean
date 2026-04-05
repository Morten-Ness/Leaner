import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem Monic.leadingCoeff_mul_eq_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hq : q.Monic D) :
    (p * q).leadingCoeff D = p.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_mul]
  rw [AddMonoidAlgebra.leadingCoeff, hq.supDegree_mul_of_ne_zero_left hD hadd hp,
    AddMonoidAlgebra.apply_supDegree_add_supDegree hD hadd, hq, mul_one]

