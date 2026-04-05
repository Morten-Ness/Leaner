import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_induction_right {p : (x : G) → x ∈ closure s → Prop} (one : p 1 (one_mem _))
    (mul_right : ∀ (x) hx, ∀ y (hy : y ∈ s), p x hx → p (x * y) (mul_mem hx (subset_closure hy)))
    (mul_inv_cancel : ∀ (x) hx, ∀ y (hy : y ∈ s), p x hx →
      p (x * y⁻¹) (mul_mem hx (inv_mem (subset_closure hy))))
    {x : G} (h : x ∈ closure s) : p x h := Subgroup.closure_induction_left (s := MulOpposite.unop ⁻¹' s)
    (p := fun m hm => p m.unop <| by rwa [← op_closure] at hm)
    one
    (fun _x hx _y _ => mul_right _ _ _ hx)
    (fun _x hx _y _ => mul_inv_cancel _ _ _ hx)
    (by rwa [← op_closure])

