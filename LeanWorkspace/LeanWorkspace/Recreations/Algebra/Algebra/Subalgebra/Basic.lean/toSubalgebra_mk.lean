import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (p : Submodule R A)

theorem toSubalgebra_mk (s : Submodule R A) (h1 hmul) :
    s.toSubalgebra h1 hmul =
      Subalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, Subalgebra.add_mem s, Subalgebra.zero_mem s⟩
        (by intro r; rw [Algebra.algebraMap_eq_smul_one]; apply Subalgebra.smul_mem s _ h1) := rfl

