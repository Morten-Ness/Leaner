import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toSubmodule_injective : Function.Injective (Subalgebra.toSubmodule : Subalgebra R A → Submodule R A) := fun _S₁ _S₂ h => SetLike.ext (SetLike.ext_iff.mp h :)

