FAIL
import Mathlib

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := CharTwo.add_sq


theorem list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x) l).sum := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons]
      rw [← sqAddMonoidHom.map_add]
      simp only [sqAddMonoidHom, pow_two]
      exact congrArg (fun x => a * a + x) ih
