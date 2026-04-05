import Mathlib

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

theorem isEpi_iff_forall_one_tmul_eq :
    Algebra.IsEpi R A ↔ ∀ a : A, 1 ⊗ₜ[R] a = a ⊗ₜ[R] 1 := by
  refine ⟨fun h a ↦ IsEpi.injective_lift_mul <| by simp, fun h ↦ ⟨fun x y hxy ↦ ?_⟩⟩
  have h' (x : A ⊗[R] A) : ∃ a : A, x = a ⊗ₜ 1 := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul u v =>
      use u * v
      calc u ⊗ₜ[R] v = u ⊗ₜ[R] 1 * 1 ⊗ₜ[R] v := by simp
                   _ = u ⊗ₜ[R] 1 * v ⊗ₜ[R] 1 := by rw [h]
                   _ = (u * v) ⊗ₜ[R] 1 := by simp
    | add u v hu hv =>
      obtain ⟨u, rfl⟩ := hu
      obtain ⟨v, rfl⟩ := hv
      exact ⟨u  + v, by simp [add_tmul]⟩
  obtain ⟨a, rfl⟩ := h' x
  obtain ⟨b, rfl⟩ := h' y
  aesop

