import Mathlib

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    (DirectSum.coeRingHom A : _ →+* R) (of (fun i => A i) i x) = x := DirectSum.toSemiring_of _ _ _ _ _

