import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_cons (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → M) i) = x * ∏ i : Fin n, f i := by
  simp_rw [Fin.prod_univ_succ, cons_zero, cons_succ]

