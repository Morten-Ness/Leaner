import Mathlib

open scoped DirectSum

variable {ιA ιB : Type*} (A : ιA → Type*) (M : ιB → Type*)

variable [AddMonoid ιA] [VAdd ιA ιB] [∀ i : ιA, AddCommMonoid (A i)] [∀ i, AddCommMonoid (M i)]

theorem smul_def [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [DirectSum.Gmodule A M]
    (x : ⨁ i, A i) (y : ⨁ i, M i) :
    x • y = DirectSum.Gmodule.smulAddMonoidHom _ _ x y := rfl

