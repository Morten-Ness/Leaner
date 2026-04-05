import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Abelian C]

theorem quasiIso_iff_of_zeros {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) :
    QuasiIso φ ↔
      (CategoryTheory.ShortComplex.mk φ.τ₂ S₂.g (by rw [φ.comm₂₃, hg₁, zero_comp])).Exact ∧ Mono φ.τ₂ := by
  have w : φ.τ₂ ≫ S₂.g = 0 := by rw [φ.comm₂₃, hg₁, zero_comp]
  rw [quasiIso_iff_isIso_liftCycles φ hf₁ hg₁ hf₂]
  constructor
  · intro h
    have : Mono φ.τ₂ := by
      rw [← S₂.liftCycles_i φ.τ₂ w]
      apply mono_comp
    refine ⟨?_, this⟩
    apply CategoryTheory.ShortComplex.exact_of_f_is_kernel
    exact IsLimit.ofIsoLimit S₂.cyclesIsKernel
      (Fork.ext (asIso (S₂.liftCycles φ.τ₂ w)).symm (by simp))
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁.lift S₂.iCycles (by simp), ?_, ?_⟩⟩
    · rw [← cancel_mono φ.τ₂, assoc, CategoryTheory.ShortComplex.Exact.lift_f h₁, liftCycles_i, id_comp]
    · rw [← cancel_mono S₂.iCycles, assoc, liftCycles_i, CategoryTheory.ShortComplex.Exact.lift_f h₁, id_comp]

