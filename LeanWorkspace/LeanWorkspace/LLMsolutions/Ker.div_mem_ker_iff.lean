FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [Group M]

theorem div_mem_ker_iff (f : G →* M) {x y : G} : x / y ∈ MonoidHom.ker f ↔ f x = f y := by
  constructor
  · intro h
    rw [MonoidHom.mem_ker] at h
    have h' := congrArg (fun z => z * f y) h
    simpa [div_eq_mul_inv, mul_assoc] using h'
  · intro h
    rw [MonoidHom.mem_ker]
    rw [div_eq_mul_inv, map_mul, map_inv, h, inv_mul_cancel]
