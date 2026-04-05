import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem single_add_single_eq_single_add_single {k l m n : ι} {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) := by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv

