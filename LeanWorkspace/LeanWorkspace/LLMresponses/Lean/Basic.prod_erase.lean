import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_erase [DecidableEq M] (ha : a ∈ l) : a * (l.erase a).prod = l.prod := by
  induction l with
  | nil =>
      cases ha
  | cons b t ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp
      · simp [List.erase_cons_tail, ha, ih ha, mul_left_comm, mul_assoc]
