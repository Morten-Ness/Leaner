import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable (f : A →ₐ[R] B)

theorem _root_.AlgHom.subalgebraMap_surjective : Function.Surjective (f.subalgebraMap S) := f.toAddMonoidHom.addSubmonoidMap_surjective S.toAddSubmonoid

