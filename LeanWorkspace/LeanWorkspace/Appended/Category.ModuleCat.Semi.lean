import Mathlib

section

variable (R : Type u) [Semiring R]

set_option backward.privateInPublic true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem coe_of (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X := rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
example (M : SemimoduleCat.{v} R) : of R M = M := by with_reducible rfl

end

section

variable (R : Type u) [Semiring R]

theorem hom_bijective {M N : SemimoduleCat.{v} R} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) where
  left f g h := by cases f; cases g; simpa using h
  right f := ⟨⟨f⟩, rfl⟩

end

section

variable (R : Type u) [Semiring R]

theorem hom_injective {M N : SemimoduleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) := SemimoduleCat.hom_bijective.injective

end

section

variable (R : Type u) [Semiring R]

theorem hom_surjective {M N : SemimoduleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) := SemimoduleCat.hom_bijective.surjective

end

section

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {M N : SemimoduleCat.{v} R}

theorem isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := SemimoduleCat.subsingleton_of_isZero
  mpr _ := SemimoduleCat.isZero_of_subsingleton M

end

section

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {M N : SemimoduleCat.{v} R}

theorem isZero_of_iff_subsingleton {M : Type*} [AddCommMonoid M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := SemimoduleCat.isZero_iff_subsingleton

end

section

variable (R : Type u) [Semiring R]

theorem isZero_of_subsingleton (M : SemimoduleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom (0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

end

section

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {M N : SemimoduleCat.{v} R}

theorem subsingleton_of_isZero (h : IsZero M) : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 (fun x ↦ ?_)
  rw [← LinearMap.id_apply (R := R) x, ← SemimoduleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]

end
