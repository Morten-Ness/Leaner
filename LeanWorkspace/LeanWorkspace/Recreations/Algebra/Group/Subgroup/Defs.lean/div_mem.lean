import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

theorem div_mem {x y : M} (hx : x ∈ H) (hy : y ∈ H) : x / y ∈ H := by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem hy)

