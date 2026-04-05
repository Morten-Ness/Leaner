import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem linearIndependent : LinearIndependent R b := fun x y hxy => by
    rw [← b.repr_linearCombination x, hxy, b.repr_linearCombination y]

protected lemma linearIndepOn (s : Set ι) : LinearIndepOn R b s :=
  b.linearIndependent.linearIndepOn s

