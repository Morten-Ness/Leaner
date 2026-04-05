import Mathlib

variable {ι M M₀ R : Type*}

variable [NonUnitalSemiring R] {s : Multiset R} {a : R}

theorem dvd_sum : (∀ x ∈ s, a ∣ x) → a ∣ s.sum := Multiset.induction_on s (fun _ ↦ dvd_zero _) fun x s ih h ↦ by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy ↦ h _ <| mem_cons.2 <| Or.inr hy)

