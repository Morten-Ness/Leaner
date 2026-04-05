import Mathlib

variable {Q : Type*} [Quandle Q]

theorem conj_act_eq_conj {G : Type*} [Group G] (x y : Conj G) :
    x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) := rfl

