import Mathlib

variable {ι κ M M₀ R : Type*}

theorem dvd_sum [NonUnitalSemiring R] {a} {l : List R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.sum := by
  induction l with
  | nil => exact dvd_zero _
  | cons x l ih =>
    rw [List.sum_cons]
    exact dvd_add (h _ mem_cons_self) (ih fun x hx ↦ h x (mem_cons_of_mem _ hx))

