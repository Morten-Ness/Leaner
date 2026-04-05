import Mathlib

variable {ιA ιB : Type*} (A : ιA → Type*) (M : ιB → Type*)

variable [AddMonoid ιA] [VAdd ιA ιB] [∀ i : ιA, AddCommMonoid (A i)] [∀ i, AddCommMonoid (M i)]

theorem smulAddMonoidHom_apply_of_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [DirectSum.Gmodule A M]
    {i j} (x : A i) (y : M j) :
    DirectSum.Gmodule.smulAddMonoidHom A M (DirectSum.of A i x) (of M j y) = of M (i +ᵥ j) (GSMul.smul x y) := by
  simp [DirectSum.Gmodule.smulAddMonoidHom]

