import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem le_equalizer {φ ψ : F} {S : Subalgebra R A} : S ≤ AlgHom.equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl

