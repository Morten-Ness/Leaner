import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

set_option backward.isDefEq.respectTransparency false in
theorem supDegree_sub_lt_of_leadingCoeff_eq (hD : D.Injective) {R} [Ring R] {p q : R[A]}
    (hd : p.supDegree D = q.supDegree D) (hc : p.leadingCoeff D = q.leadingCoeff D) :
    (p - q).supDegree D < p.supDegree D ∨ p = q := by
  rw [or_iff_not_imp_right]
  refine fun he => (AddMonoidAlgebra.supDegree_sub_le.trans ?_).lt_of_ne ?_
  · rw [hd, sup_idem]
  · rw [← sub_eq_zero, ← AddMonoidAlgebra.leadingCoeff_eq_zero hD, AddMonoidAlgebra.leadingCoeff] at he
    refine fun h => he ?_
    rwa [h, Finsupp.sub_apply, ← AddMonoidAlgebra.leadingCoeff, hd, ← AddMonoidAlgebra.leadingCoeff, sub_eq_zero]

