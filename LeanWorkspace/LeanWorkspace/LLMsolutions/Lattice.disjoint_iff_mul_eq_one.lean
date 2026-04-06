FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_iff_mul_eq_one {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x * y = 1 → x = 1 ∧ y = 1 := by
  constructor
  · intro h x y hx hy hxy
    have hx'y : x = y⁻¹ := by
      calc
        x = x * (y * y⁻¹) := by simp
        _ = (x * y) * y⁻¹ := by simp [mul_assoc]
        _ = 1 * y⁻¹ := by rw [hxy]
        _ = y⁻¹ := by simp
    have hyx : y⁻¹ ∈ H₂ := H₂.inv_mem hy
    have hxmem : x ∈ H₁ ⊓ H₂ := ⟨hx, by simpa [hx'y] using hyx⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := h.le_bot hxmem
    have hxone : x = 1 := by simpa using hxbot
    have hyone : y = 1 := by
      calc
        y = (y⁻¹)⁻¹ := by simp
        _ = x⁻¹ := by rw [hx'y]
        _ = 1 := by simp [hxone]
    exact ⟨hxone, hyone⟩
  · intro h
    rw [Subgroup.disjoint_def]
    ext z
    constructor
    · intro hz
      have h' := h hz.1 hz.2 (by
        change z * z⁻¹ = 1
        simp)
      simpa using h'.1
    · intro hz
      simpa [hz]
