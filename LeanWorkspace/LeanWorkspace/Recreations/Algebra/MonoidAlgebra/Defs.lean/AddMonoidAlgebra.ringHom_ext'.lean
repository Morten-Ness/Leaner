import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R]

theorem ringHom_ext' [Semiring S] [AddMonoid M] {f g : R[M] →+* S}
    (h₁ : f.comp singleZeroRingHom = g.comp singleZeroRingHom)
    (h_of : (f : R[M] →* S).comp (AddMonoidAlgebra.of R M) = (g : R[M] →* S).comp (AddMonoidAlgebra.of R M)) :
    f = g := MonoidAlgebra.ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)

