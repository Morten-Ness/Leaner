import Mathlib

variable {ι : Type*}

variable {R : Type*}

theorem SetLike.coe_gnpow {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@GradedMonoid.GMonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x : R) ^ n := rfl

