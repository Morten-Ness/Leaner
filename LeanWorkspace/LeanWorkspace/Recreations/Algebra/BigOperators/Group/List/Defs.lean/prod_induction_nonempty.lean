import Mathlib

variable {ι M N : Type*}

variable [MulOneClass M] {l : List M} {a : M}

theorem prod_induction_nonempty
    (p : M → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (hl : l ≠ []) (base : ∀ x ∈ l, p x) :
    p l.prod := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases hl_empty : l = []
    · simp [*]
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih hl_empty base.2)

