import Mathlib

section

variable {α M G : Type*}

variable [DivisionMonoid G] (f g : α → G)

theorem mulSupport_div : (mulSupport fun x => f x / g x) ⊆ mulSupport f ∪ mulSupport g := mulSupport_binop_subset (· / ·) one_div_one f g

end

section

variable {α M G : Type*}

theorem mulSupport_mul [MulOneClass M] (f g : α → M) :
    (mulSupport fun x ↦ f x * g x) ⊆ mulSupport f ∪ mulSupport g := mulSupport_binop_subset (· * ·) (one_mul _) f g

end

section

variable {α M G : Type*}

variable [DivisionMonoid G] (f g : α → G)

theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) ⊆ mulSupport f ∪ mulSupport g := mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

end

section

variable {α M G : Type*}

theorem mulSupport_pow [Monoid M] (f : α → M) (n : ℕ) :
    (mulSupport fun x => f x ^ n) ⊆ mulSupport f := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hfn =>
    simpa only [pow_succ'] using (Function.mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

end
