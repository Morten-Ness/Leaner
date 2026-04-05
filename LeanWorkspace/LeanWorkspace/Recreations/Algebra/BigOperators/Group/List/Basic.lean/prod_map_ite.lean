import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_map_ite (p : α → Prop) [DecidablePred p] (f g : α → M) (l : List α) :
    (l.map fun a => if p a then f a else g a).prod =
      ((l.filter p).map f).prod * ((l.filter fun a ↦ ¬p a).map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, filter_cons, prod_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : p x
    · simp only [hx, ↓reduceIte, decide_not, decide_true, map_cons, prod_cons, not_true_eq_false,
        decide_false, Bool.false_eq_true, mul_assoc]
    · simp only [hx, ↓reduceIte, decide_not, decide_false, Bool.false_eq_true, not_false_eq_true,
      decide_true, map_cons, prod_cons, mul_left_comm]

