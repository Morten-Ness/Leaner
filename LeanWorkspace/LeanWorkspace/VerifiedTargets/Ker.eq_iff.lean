import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem eq_iff (f : G →* M) {x y : G} : f x = f y ↔ y⁻¹ * x ∈ f.ker := by
  constructor <;> intro h
  · rw [MonoidHom.mem_ker, map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  · rw [← one_mul x, ← mul_inv_cancel y, mul_assoc, map_mul, MonoidHom.mem_ker.1 h, mul_one]

