FAIL
import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

theorem smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a ↦ x.2 / f x.1 * f a := by
  ext y
  rcases y with ⟨a, b⟩
  simp only [Set.mem_smul_set, Set.mem_graphOn]
  constructor
  · rintro ⟨⟨u, fu⟩, ⟨hu, rfl⟩, hxy⟩
    rcases Prod.mk.inj hxy with ⟨ha, hb⟩
    subst ha
    refine ⟨u, ?_, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · simp only [hb]
      rw [div_eq_mul_inv]
      calc
        x.2 * f u = x.2 * (f x.1)⁻¹ * (f x.1 * f u) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
        _ = x.2 / f x.1 * f (x.1 * u) := by
          simp [map_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  · rintro ⟨u, ⟨v, hv, hvu⟩, hb⟩
    subst hvu
    refine ⟨(v, f v), ?_, ?_⟩
    · exact ⟨hv, rfl⟩
    · apply Prod.mk.inj_iff.mpr
      constructor
      · rfl
      · rw [hb]
        simp [map_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
