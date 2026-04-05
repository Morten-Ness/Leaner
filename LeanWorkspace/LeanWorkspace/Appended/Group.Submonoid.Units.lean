import Mathlib

section

variable {M : Type*} [Monoid M]

theorem coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.inv_mul

end

section

variable {M : Type*} [Monoid M]

theorem coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.mul_inv

end

section

variable {M : Type*} [Monoid M]

theorem isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (hx : x ∈ S.ofUnits) : IsUnit x := match hx with
  | ⟨_, _, h⟩ => ⟨_, h⟩

end

section

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem mem_iff_toUnits_mem_units (H : Subgroup G) (x : G) : toUnits x ∈ H.units ↔ x ∈ H := by
  simp_rw [Subgroup.mem_units_iff_val_mem, val_toUnits_apply]

end

section

variable {M : Type*} [Monoid M]

theorem mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x ∈ S.ofUnits ↔ ∃ h : IsUnit x, h.unit ∈ S := ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
  fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

end

section

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G) : x ∈ H.ofUnits ↔ (toUnits x) ∈ H := by
  simp_rw [Subgroup.mem_ofUnits_iff, toUnits.surjective.exists, val_toUnits_apply, exists_eq_right]

end

section

variable {M : Type*} [Monoid M]

theorem mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) ∈ S.ofUnits) : y ∈ S := match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

end

section

variable {M : Type*} [Monoid M]

theorem unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
    (h₂ : x ∈ S.ofUnits) : h₁.unit ∈ S := S.unit_eq_unit_of_mem_ofUnits h₁ h₂ ▸ (S.unit_of_mem_ofUnits_spec_mem)

end

section

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem val_mem_ofUnits_iff_mem (H : Subgroup Gˣ) (x : Gˣ) : (x : G) ∈ H.ofUnits ↔ x ∈ H := by
  simp_rw [Subgroup.mem_ofUnits_iff_toUnits_mem, toUnits_val_apply]

end
