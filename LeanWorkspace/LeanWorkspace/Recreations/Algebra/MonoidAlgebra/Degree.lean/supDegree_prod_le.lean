import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

variable {p q : R[A]}

variable [AddZeroClass A]

variable [Add B]

theorem supDegree_prod_le {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
    [SemilatticeSup B] [OrderBot B]
    [AddLeftMono B] [AddRightMono B]
    {D : A → B} (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    {ι} {s : Finset ι} {f : ι → R[A]} :
    (∏ i ∈ s, f i).supDegree D ≤ ∑ i ∈ s, (f i).supDegree D := by
  classical
  refine s.induction ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, AddMonoidAlgebra.supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (AddMonoidAlgebra.supDegree_mul_le hadd).trans (by gcongr)

