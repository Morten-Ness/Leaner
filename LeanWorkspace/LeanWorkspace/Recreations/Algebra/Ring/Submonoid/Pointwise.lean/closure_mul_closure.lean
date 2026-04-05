import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

theorem closure_mul_closure (S T : Set R) : closure S * closure T = closure (S * T) := by
  apply le_antisymm
  · refine AddSubmonoid.mul_le.2 fun a ha b hb => ?_
    rw [← AddMonoidHom.mulRight_apply, ← AddSubmonoid.mem_comap]
    refine (closure_le.2 fun a' ha' => ?_) ha
    change b ∈ (closure (S * T)).comap (AddMonoidHom.mulLeft a')
    refine (closure_le.2 fun b' hb' => ?_) hb
    change a' * b' ∈ closure (S * T)
    exact subset_closure (Set.mul_mem_mul ha' hb')
  · rw [closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact AddSubmonoid.mul_mem_mul (subset_closure ha) (subset_closure hb)

