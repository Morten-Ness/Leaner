import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) :
    h x⁻¹ = (h x)⁻¹ := map_inv h x

