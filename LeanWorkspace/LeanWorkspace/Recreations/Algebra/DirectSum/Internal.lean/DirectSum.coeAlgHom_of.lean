import Mathlib

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x := DirectSum.toSemiring_of _ (by rfl) (fun _ _ => (by rfl)) _ _

