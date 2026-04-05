import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

variable {B : Type u₄} [Semiring B] [Algebra S B]

theorem liftAlgHom_mkAlgHom_apply (f : A →ₐ[S] B) {s : A → A → Prop}
    (w : ∀ ⦃x y⦄, s x y → f x = f y) (x) : (liftAlgHom S ⟨f, w⟩) ((mkAlgHom S s) x) = f x := by
  simp_rw [liftAlgHom_def, preLiftAlgHom_def, mkAlgHom_def, mkRingHom_def]
  rfl

-- note this is essentially `(liftAlgHom S).symm_apply_eq.mp h`

