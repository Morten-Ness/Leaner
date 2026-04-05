import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) :
    spectrum R (a : A) ⊆ spectrum R a := Set.compl_subset_compl.mpr fun _ ↦ IsUnit.map (SubalgebraClass.val s)

