import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem mem_equalizer (φ ψ : F) (x : A) : x ∈ AlgHom.equalizer φ ψ ↔ φ x = ψ x := Iff.rfl

