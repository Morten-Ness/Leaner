import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem isMonicOfDegree_add_add_two (a b : R) : IsMonicOfDegree (X ^ 2 + C a * X + C b) 2 := by
  rw [add_assoc]
  exact (Polynomial.isMonicOfDegree_X_pow R 2).add_right <|
    calc
    _ ≤ max (C a * X).natDegree (C b).natDegree := natDegree_add_le ..
    _ = (C a * X).natDegree := by simp
    _ < 2 := natDegree_C_mul_le .. |>.trans natDegree_X_le |>.trans_lt one_lt_two

