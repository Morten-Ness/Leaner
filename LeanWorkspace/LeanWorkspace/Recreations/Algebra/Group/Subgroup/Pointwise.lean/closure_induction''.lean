import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_induction'' {p : (g : G) → g ∈ closure s → Prop}
    (mem : ∀ x (hx : x ∈ s), p x (subset_closure hx))
    (inv_mem : ∀ x (hx : x ∈ s), p x⁻¹ (inv_mem (subset_closure hx)))
    (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ closure s) : p x h := Subgroup.closure_induction_left one (fun x hx y _ hy => mul x y _ _ (mem x hx) hy)
    (fun x hx y _ => mul x⁻¹ y _ _ <| inv_mem x hx) h

