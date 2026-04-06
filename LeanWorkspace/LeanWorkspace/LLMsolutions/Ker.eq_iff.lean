import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [Group M]

theorem eq_iff (f : G →* M) {x y : G} : f x = f y ↔ y⁻¹ * x ∈ f.ker := by
  constructor
  · intro h
    rw [MonoidHom.mem_ker]
    change f (y⁻¹ * x) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  · intro h
    rw [MonoidHom.mem_ker] at h
    change f (y⁻¹ * x) = 1 at h
    rw [map_mul, map_inv] at h
    have h' := congrArg (fun z => f y * z) h
    simpa [mul_assoc] using h'
