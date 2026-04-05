import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem Monic.supDegree_mul_of_ne_zero_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hq (Subsingleton.elim _ _)).elim
  apply AddMonoidAlgebra.supDegree_mul hD hadd ?_ hp.ne_zero hq
  simp_rw [hp, one_mul, Ne, AddMonoidAlgebra.leadingCoeff_eq_zero hD, hq, not_false_eq_true]

