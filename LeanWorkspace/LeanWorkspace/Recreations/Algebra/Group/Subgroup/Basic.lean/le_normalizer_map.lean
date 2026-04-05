import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem le_normalizer_map (f : G →* N) : (normalizer H).map f ≤ normalizer (H.map f) := fun _ => by
  simp only [and_imp, mem_map, exists_imp, mem_normalizer_iff]
  rintro x hx rfl n
  constructor
  · rintro ⟨y, hy, rfl⟩
    use x * y * x⁻¹, (hx y).1 hy
    simp
  · rintro ⟨y, hyH, hy⟩
    use x⁻¹ * y * x
    rw [hx]
    simp [hy, hyH, mul_assoc]

