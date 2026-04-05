import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_erase_of_comm [DecidableEq M] (ha : a ∈ l) (comm : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x) :
    a * (l.erase a).prod = l.prod := by
  induction l with
  | nil => simp only [not_mem_nil] at ha
  | cons b l ih =>
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem ha
    · simp only [erase_cons_head, prod_cons]
    rw [List.erase, beq_false_of_ne ne.symm, List.prod_cons, List.prod_cons, ← mul_assoc,
      comm a ha b mem_cons_self, mul_assoc,
      ih h fun x hx y hy ↦ comm _ (List.mem_cons_of_mem b hx) _ (List.mem_cons_of_mem b hy)]

