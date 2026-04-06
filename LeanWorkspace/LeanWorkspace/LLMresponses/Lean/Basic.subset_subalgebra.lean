import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) :
    spectrum R (a : A) ⊆ spectrum R a := by
  intro k hk
  rw [spectrum.mem_iff] at hk ⊢
  intro h
  apply hk
  let f : s →+* A :=
    { toFun := fun x => x.1
      map_one' := rfl
      map_mul' := fun x y => rfl
      map_zero' := rfl
      map_add' := fun x y => rfl }
  simpa [f] using h.map f
