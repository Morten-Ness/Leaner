import Mathlib

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by have I := h1; exact r • x) = r • x) : h1 = h2 :=
  Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) := RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]

variable [Module R M] [Module A M] [IsScalarTower R A M]

theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s := congr_arg ((↑) : Submodule R M → Set M) (Submodule.restrictScalars_span R A h s)

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq <| RingHom.ext_iff.1 h

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

theorem of_algebraMap_eq [Algebra R A]
    (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A := ⟨fun x y z => by simp_rw [Algebra.smul_def, map_mul, mul_assoc, h]⟩

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [MulAction A M]

theorem of_algebraMap_smul [SMul R M] (h : ∀ (r : R) (x : M), algebraMap R A r • x = r • x) :
    IsScalarTower R A M where
  smul_assoc r a x := by rw [Algebra.smul_def, mul_smul, h]

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [MulAction A M]

theorem of_compHom : letI := MulAction.compHom M (algebraMap R A : R →* A); IsScalarTower R A M :=
  letI := MulAction.compHom M (algebraMap R A : R →* A); IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem span_algebraMap_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) := (Submodule.span_image <| Algebra.linearMap R S).trans rfl

end

section

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem span_algebraMap_image_of_tower {S T : Type*} [CommSemiring S] [Semiring T] [Module R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) := (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl

end
