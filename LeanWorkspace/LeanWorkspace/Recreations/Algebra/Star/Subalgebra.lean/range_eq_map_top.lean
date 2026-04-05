import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R A]

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

variable [StarModule R B]

theorem range_eq_map_top (φ : A →⋆ₐ[R] B) : φ.range = (⊤ : StarSubalgebra R A).map φ := StarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

