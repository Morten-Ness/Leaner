import Mathlib

variable {R M : Type*}

theorem isTorsion_iff_isTorsion_nat [AddCommMonoid M] :
    AddMonoid.IsTorsion M ↔ Module.IsTorsion ℕ M := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, h0, hn⟩ := (h x).exists_nsmul_eq_zero
    exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero <| ne_of_gt h0⟩, hn⟩
  · rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    exact ⟨n, Nat.pos_of_ne_zero (nonZeroDivisors.coe_ne_zero _), hn⟩

