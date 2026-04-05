import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem Monic.leadingCoeff_mul_eq_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hp : p.Monic D) :
    (p * q).leadingCoeff D = q.leadingCoeff D := by
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero]
  rw [AddMonoidAlgebra.leadingCoeff, hp.supDegree_mul_of_ne_zero_right hD hadd hq,
    AddMonoidAlgebra.apply_supDegree_add_supDegree hD hadd, hp, one_mul]

