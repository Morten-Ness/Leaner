import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

theorem lift_mkRingHom_apply (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift ⟨f, w⟩ (mkRingHom r x) = f x := by
  simp_rw [lift_def, preLift_def, mkRingHom_def]
  rfl

-- note this is essentially `lift.symm_apply_eq.mp h`

