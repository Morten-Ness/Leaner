import Mathlib

variable {ιA ιB ιM : Type*}

variable {R : Type*}

theorem SetLike.coe_GSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA → S) (B : ιB → N) [SetLike.GradedSMul A B] {i : ιA} {j : ιB} (x : A i) (y : B j) :
    (@GradedMonoid.GSMul.smul ιA ιB (fun i ↦ A i) (fun i ↦ B i) _ _ i j x y : M) = x.1 • y.1 := rfl

