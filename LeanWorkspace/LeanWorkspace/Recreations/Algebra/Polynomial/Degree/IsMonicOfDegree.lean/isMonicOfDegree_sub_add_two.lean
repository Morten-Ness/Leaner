import Mathlib

variable {R : Type*}

variable [Ring R]

variable [Nontrivial R]

theorem isMonicOfDegree_sub_add_two (a b : R) : IsMonicOfDegree (X ^ 2 - C a * X + C b) 2 := by
  rw [sub_add]
  exact (Polynomial.isMonicOfDegree_X_pow R 2).add_right <| by
    rw [natDegree_neg]
    calc
    _ ≤ max (C a * X).natDegree (C b).natDegree := natDegree_sub_le ..
    _ = (C a * X).natDegree := by simp
    _ < 2 := natDegree_C_mul_le .. |>.trans natDegree_X_le |>.trans_lt one_lt_two

