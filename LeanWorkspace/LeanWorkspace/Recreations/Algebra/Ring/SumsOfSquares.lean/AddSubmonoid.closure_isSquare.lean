import Mathlib

variable {R : Type*}

theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = AddSubmonoid.sumSq R := by
  refine closure_eq_of_le (fun x hx ↦ IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  induction hx <;> aesop

