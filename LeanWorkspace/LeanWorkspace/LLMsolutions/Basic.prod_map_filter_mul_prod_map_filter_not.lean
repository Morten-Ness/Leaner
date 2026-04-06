FAIL
import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_map_filter_mul_prod_map_filter_not (p : α → Prop) [DecidablePred p] (f : α → M)
    (l : List α) :
    ((l.filter p).map f).prod * ((l.filter fun x => ¬p x).map f).prod = (l.map f).prod := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      by_cases hx : p x
      · simp [hx, List.prod_cons, ih, mul_assoc]
      · simp [hx, List.prod_cons, ih, mul_assoc, mul_left_comm, mul_comm]
