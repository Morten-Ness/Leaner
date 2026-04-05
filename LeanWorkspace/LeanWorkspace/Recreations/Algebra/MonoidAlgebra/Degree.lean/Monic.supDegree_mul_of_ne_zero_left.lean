import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem Monic.supDegree_mul_of_ne_zero_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hq : q.Monic D) (hp : p ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hp (Subsingleton.elim _ _)).elim
  apply AddMonoidAlgebra.supDegree_mul hD hadd ?_ hp hq.ne_zero
  simp_rw [hq, mul_one, Ne, AddMonoidAlgebra.leadingCoeff_eq_zero hD, hp, not_false_eq_true]

