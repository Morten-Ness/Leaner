import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

theorem sup_eq_closure_mul (H K : Submonoid M) : H ⊔ K = closure ((H : Set M) * (K : Set M)) := le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((Submonoid.closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

