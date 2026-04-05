import Mathlib

variable {ι α β M N P G : Type*}

variable [CommGroup G]

theorem prod_map_ite_eq {A : Type*} [DecidableEq A] (l : List A) (f g : A → G) (a : A) :
    (l.map fun x => if x = a then f x else g x).prod
      = (f a / g a) ^ (l.count a) * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, count_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : x = a
    · simp only [hx, ite_true, pow_add, pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      mul_inv_cancel_left, beq_self_eq_true]
    · simp only [hx, ite_false, add_zero, mul_assoc, mul_comm (g x) _, beq_iff_eq]

