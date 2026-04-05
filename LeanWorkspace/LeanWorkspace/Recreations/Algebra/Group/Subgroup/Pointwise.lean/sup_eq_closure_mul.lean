import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem sup_eq_closure_mul (H K : Subgroup G) : H ⊔ K = closure ((H : Set G) * (K : Set G)) := le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((Subgroup.closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

