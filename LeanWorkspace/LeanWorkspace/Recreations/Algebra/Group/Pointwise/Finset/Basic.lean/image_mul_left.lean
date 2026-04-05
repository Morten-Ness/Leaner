import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) (mul_right_injective _).injOn := coe_injective <| by simp

