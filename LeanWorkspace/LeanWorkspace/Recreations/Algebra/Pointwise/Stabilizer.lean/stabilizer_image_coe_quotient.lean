import Mathlib

open scoped Pointwise

variable {G : Type*} [CommGroup G] (s : Set G)

theorem stabilizer_image_coe_quotient : stabilizer Q (q '' s) = ⊥ := by
  ext a
  induction a using QuotientGroup.induction_on with | _ a
  simp only [mem_stabilizer_iff, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have : q a • q '' s = q '' (a • s) :=
    (image_smul_distrib (QuotientGroup.mk' <| stabilizer G s) _ _).symm
  rw [this]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rwa [QuotientGroup.image_coe_inj, mul_smul_comm, MulAction.stabilizer_mul_self] at h

