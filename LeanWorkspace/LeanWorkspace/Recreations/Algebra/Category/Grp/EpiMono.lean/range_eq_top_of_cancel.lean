import Mathlib

open scoped Pointwise

variable {A : Type u} {B : Type v}

variable [CommGroup A] [CommGroup B]

theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ := by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1 x
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _, QuotientGroup.eq, inv_one,
      one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' f.range).ker = (1 : B →* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk'] at h

