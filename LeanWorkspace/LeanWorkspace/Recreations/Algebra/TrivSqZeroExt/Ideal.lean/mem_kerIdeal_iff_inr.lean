import Mathlib

variable (R M : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem mem_kerIdeal_iff_inr (x : TrivSqZeroExt R M) : x ∈ TrivSqZeroExt.kerIdeal R M ↔ x = inr x.snd := by
  obtain ⟨r, m⟩ := x
  simp only [TrivSqZeroExt.kerIdeal, RingHom.mem_ker, fstHom_apply, fst_mk]
  exact ⟨fun hr => by rw [hr]; rfl, fun hrm => by rw [← fst_mk r m, hrm, fst_inr]⟩

