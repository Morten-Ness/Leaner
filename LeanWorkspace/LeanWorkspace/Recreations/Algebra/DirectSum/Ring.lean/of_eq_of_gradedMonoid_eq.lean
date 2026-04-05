import Mathlib

variable {ι : Type*} [DecidableEq ι]

theorem of_eq_of_gradedMonoid_eq {A : ι → Type*} [∀ i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i}
    {b : A j} (h : GradedMonoid.mk i a = GradedMonoid.mk j b) :
    DirectSum.of A i a = DirectSum.of A j b := DFinsupp.single_eq_of_sigma_eq h

