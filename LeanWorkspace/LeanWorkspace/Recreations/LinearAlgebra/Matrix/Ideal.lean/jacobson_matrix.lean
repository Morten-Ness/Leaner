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


theorem jacobson_matrix (I : TwoSidedIdeal R) :
    (I.matrix n).jacobson = I.jacobson.matrix n := by
  apply le_antisymm
  · apply jacobson_matrix_le
  · change asIdeal (I.matrix n).jacobson ≥ asIdeal (I.jacobson.matrix n)
    simp [asIdeal_jacobson, TwoSidedIdeal.asIdeal_matrix, Ideal.matrix_jacobson_le]

