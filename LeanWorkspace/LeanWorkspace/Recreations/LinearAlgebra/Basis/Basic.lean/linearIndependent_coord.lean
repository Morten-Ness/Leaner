import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem linearIndependent_coord {R : Type*} [CommSemiring R] [Module R M] (b : Module.Basis ι R M) :
    LinearIndependent R b.coord := by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s l₁ l₂ h j hj ↦ ?_
  simpa [hj, Finsupp.single_apply] using congr($h (b j))

