import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

variable {B : Type u₄} [Semiring B] [Algebra S B]

theorem ringQuot_ext' {s : A → A → Prop} (f g : RingQuot s →ₐ[S] B)
    (w : f.comp (mkAlgHom S s) = g.comp (mkAlgHom S s)) : f = g := by
  ext x
  rcases RingQuot.mkAlgHom_surjective S s x with ⟨x, rfl⟩
  exact AlgHom.congr_fun w x

irreducible_def preLiftAlgHom {s : A → A → Prop} {f : A →ₐ[S] B}
  (h : ∀ ⦃x y⦄, s x y → f x = f y) : RingQuot s →ₐ[S] B :=
{ toFun := fun x ↦ Quot.lift f
            (by
              rintro _ _ r
              induction r with
              | of r => exact h r
              | add_left _ r' => simp only [map_add, r']
              | mul_left _ r' => simp only [map_mul, r']
              | mul_right _ r' => simp only [map_mul, r'])
            x.toQuot
  map_zero' := by simp only [← RingQuot.zero_quot, map_zero]
  map_add' := by
    rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
    simp only [RingQuot.add_quot, map_add _ x y]
  map_one' := by simp only [← RingQuot.one_quot, map_one]
  map_mul' := by
    rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
    simp only [RingQuot.mul_quot, map_mul _ x y]
  commutes' := by
    rintro x
    simp [← RingQuot.one_quot, RingQuot.smul_quot, Algebra.algebraMap_eq_smul_one] }

