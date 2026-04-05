import Mathlib

variable {R M : Type*}

theorem torsionBy_eq_span_singleton {R : Type w} [CommRing R] (a b : R) (ha : a ∈ R⁰) :
    Submodule.torsionBy R (R ⧸ R ∙ a * b) a = R ∙ Ideal.Quotient.mk (R ∙ a * b) b := by
  ext x; rw [Submodule.mem_torsionBy_iff, Submodule.mem_span_singleton]
  obtain ⟨x, rfl⟩ := mk_surjective x; constructor <;> intro h
  · rw [← mk_eq_mk, ← Ideal.Quotient.mk_smul, Ideal.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at h
    obtain ⟨c, h⟩ := h
    rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_assoc, mul_cancel_left_mem_nonZeroDivisors ha,
      mul_comm] at h
    use c
    rw [← h, ← mk_eq_mk, ← Ideal.Quotient.mk_smul, smul_eq_mul, mk_eq_mk]
  · obtain ⟨c, h⟩ := h
    rw [← h, smul_comm, ← mk_eq_mk, ← Ideal.Quotient.mk_smul,
      (Ideal.Quotient.mk_eq_zero _).mpr <| mem_span_singleton_self _, smul_zero]

