import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem star_mono : Monotone (star : Subalgebra R A → Subalgebra R A) := fun _ _ h _ hx => h hx

