import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

variable {A B : Type*} [AddMonoid A] [AddMonoid B] [LinearOrder B] [OrderBot B]
  [AddLeftStrictMono B] [AddRightStrictMono B]
  {D : A → B} {p : R[A]} {n : ℕ}

theorem Monic.pow
    (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    (hp : p.Monic D) : (p ^ n).Monic D := by
  induction n with
  | zero => rw [pow_zero]; exact AddMonoidAlgebra.monic_one hD
  | succ n ih => rw [pow_succ']; exact hp.mul hD hadd ih

