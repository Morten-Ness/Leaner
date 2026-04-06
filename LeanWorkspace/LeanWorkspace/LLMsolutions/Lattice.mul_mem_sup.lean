FAIL
import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := by
  refine Subalgebra.mul_mem ?_ ?_
  · exact show x ∈ S ⊔ T from SetLike.mem_of_subset (show S ≤ S ⊔ T from le_sup_left) hx
  · exact show y ∈ S ⊔ T from SetLike.mem_of_subset (show T ≤ S ⊔ T from le_sup_right) hy
