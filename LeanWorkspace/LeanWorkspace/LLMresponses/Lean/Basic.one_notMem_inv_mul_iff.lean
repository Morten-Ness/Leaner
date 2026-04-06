FAIL
import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := by
  simpa [Finset.disjoint_left, Finset.mem_mul, Finset.mem_inv, eq_mul_inv_iff_mul_eq, mul_assoc] using
    (not_exists.trans <| by
      constructor
      · intro h x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, z, hz, hyz⟩
          refine ⟨z, hz, ?_⟩
          have : y * z = 1 := hyz
          calc
            y = z⁻¹ := by simpa using eq_inv_iff_mul_eq_one.mpr this
            _⁻¹ = z := by simp
        · intro hx
          rcases hx with ⟨z, hz, hz'⟩
          refine ⟨z⁻¹, ?_, z, hz, ?_⟩
          · rw [Finset.mem_inv]
            exact ⟨z, hz', by simp⟩
          · simp
      · intro h
        rcases h with ⟨x, hxS, hxT⟩
        refine ⟨x⁻¹, ?_, x, hxS, by simp⟩
        rw [Finset.mem_inv]
        exact ⟨x, hxT, by simp⟩)
