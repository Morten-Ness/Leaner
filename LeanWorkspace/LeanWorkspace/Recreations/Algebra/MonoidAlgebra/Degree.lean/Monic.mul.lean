import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem Monic.mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q.Monic D) : (p * q).Monic D := by
  rw [Monic, hq.leadingCoeff_mul_eq_left hD hadd]; exact hp

