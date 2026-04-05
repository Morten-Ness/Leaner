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

theorem Monic.supDegree_pow
    (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    [Nontrivial R] (hp : p.Monic D) :
    (p ^ n).supDegree D = n • p.supDegree D := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, one_def, AddMonoidAlgebra.supDegree_single 0 1, if_neg one_ne_zero, hzero]
  | succ n ih => rw [pow_succ', (hp.pow hadd hD).supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero,
      ih, succ_nsmul']

