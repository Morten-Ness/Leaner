import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) :
    h (x / y) = h x / h y := map_div h x y

