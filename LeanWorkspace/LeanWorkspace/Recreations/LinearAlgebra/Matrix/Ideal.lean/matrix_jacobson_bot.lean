import Mathlib

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

set_option backward.privateInPublic true in
private theorem jacobson_matrix_le (I : TwoSidedIdeal R) :
    (I.matrix n).jacobson ≤ I.jacobson.matrix n := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  intro M Mmem p q
  simp only [zero_apply, ← mem_iff]
  rw [mem_jacobson_iff]
  replace Mmem := mul_mem_right _ _ (single q p 1) Mmem
  rw [mem_jacobson_iff] at Mmem
  intro y
  specialize Mmem (y • single p p 1)
  have ⟨N, NxMI⟩ := Mmem
  use N p p
  simpa [mul_apply, single, ite_and] using NxMI p p


theorem matrix_jacobson_bot :
    (⊥ : TwoSidedIdeal R).jacobson.matrix n = (⊥ : TwoSidedIdeal (Matrix n n R)).jacobson := TwoSidedIdeal.matrix_bot n (R := R) ▸ (TwoSidedIdeal.jacobson_matrix _).symm

