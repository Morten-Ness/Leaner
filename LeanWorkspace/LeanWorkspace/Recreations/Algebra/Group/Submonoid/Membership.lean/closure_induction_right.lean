import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem closure_induction_right
    {s : Set M} {motive : (m : M) → m ∈ closure s → Prop} (one : motive 1 (one_mem _))
    (mul_right : ∀ x hx, ∀ y (hy : y ∈ s),
      motive x hx → motive (x * y) (mul_mem hx (subset_closure hy)))
    {x : M} (h : x ∈ closure s) : motive x h := Submonoid.closure_induction_left (s := MulOpposite.unop ⁻¹' s)
    (motive := fun m hm => motive m.unop <| by rwa [← op_closure] at hm)
    one (fun _x hx _y _ => mul_right _ _ _ hx) (by rwa [← op_closure])

