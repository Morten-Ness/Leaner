import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [MulOneClass M]

theorem ringHom_ext' [Semiring S] {f g : R[M] →+* S}
    (h₁ : f.comp MonoidAlgebra.singleOneRingHom = g.comp MonoidAlgebra.singleOneRingHom)
    (h_of : (f : R[M] →* S).comp (MonoidAlgebra.of R M) =
      (g : R[M] →* S).comp (MonoidAlgebra.of R M)) : f = g := MonoidAlgebra.ringHom_ext (by simpa [DFunLike.ext_iff] using h₁) (by simpa [DFunLike.ext_iff] using h_of)

