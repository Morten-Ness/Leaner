import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mul_injective_of_disjoint {H₁ H₂ : Subgroup G} (h : Disjoint H₁ H₂) :
    Function.Injective (fun g => g.1 * g.2 : H₁ × H₂ → G) := by
  intro x y hxy
  rw [← inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_inv_eq_one, mul_assoc] at hxy
  replace hxy := Subgroup.disjoint_iff_mul_eq_one.mp h (y.1⁻¹ * x.1).prop (x.2 * y.2⁻¹).prop hxy
  rwa [coe_mul, coe_mul, coe_inv, coe_inv, inv_mul_eq_one, mul_inv_eq_one, ← Subtype.ext_iff, ←
    Subtype.ext_iff, eq_comm, ← Prod.ext_iff] at hxy

