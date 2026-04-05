import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

set_option backward.isDefEq.respectTransparency false in
theorem leadingCoeff_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).leadingCoeff D = p.leadingCoeff D := by
  obtain ⟨a, he⟩ := AddMonoidAlgebra.supDegree_mem_range D (AddMonoidAlgebra.ne_zero_of_not_supDegree_le h.not_ge)
  rw [AddMonoidAlgebra.leadingCoeff, AddMonoidAlgebra.supDegree_add_eq_left h, Finsupp.add_apply, ← AddMonoidAlgebra.leadingCoeff,
    AddMonoidAlgebra.apply_eq_zero_of_not_le_supDegree (D := D), add_zero]
  rw [← he, Function.apply_invFun_apply (f := D), he]; exact h.not_ge

