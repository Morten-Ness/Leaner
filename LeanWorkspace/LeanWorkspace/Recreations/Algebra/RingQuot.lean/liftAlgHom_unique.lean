import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

variable {B : Type u₄} [Semiring B] [Algebra S B]

theorem liftAlgHom_unique (f : A →ₐ[S] B) {s : A → A → Prop} (w : ∀ ⦃x y⦄, s x y → f x = f y)
    (g : RingQuot s →ₐ[S] B) (h : g.comp (mkAlgHom S s) = f) : g = liftAlgHom S ⟨f, w⟩ := by
  ext
  simp [h]

