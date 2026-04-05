import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem Monic.supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hbot : (⊥ : B) + ⊥ = ⊥) (hp : p.Monic D) (hq : q.Monic D) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R
  · simp_rw [Subsingleton.eq_zero p, Subsingleton.eq_zero q, mul_zero, AddMonoidAlgebra.supDegree_zero, hbot]
  exact hq.supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero

