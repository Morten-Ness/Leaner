import Mathlib

variable {ι : Type*}

variable {R : Type*}

theorem SetLike.coe_gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) := rfl

