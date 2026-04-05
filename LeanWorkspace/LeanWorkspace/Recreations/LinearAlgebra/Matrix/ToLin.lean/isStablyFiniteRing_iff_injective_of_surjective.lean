import Mathlib

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem isStablyFiniteRing_iff_injective_of_surjective :
    IsStablyFiniteRing A ↔ ∀ n (f : Module.End A (Fin n → A)), Function.Surjective f → Function.Injective f := by
  simp_rw [isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd, isDedekindFiniteMonoid_iff]
  refine ⟨fun h n f surj ↦ ?_, fun h n f g eq ↦ ?_⟩
  · have ⟨g, eq⟩ := Module.projective_lifting_property _ .id surj
    exact injective_of_comp_eq_id _ _ (h _ eq)
  · have surj := surjective_of_comp_eq_id _ _ eq
    have := (LinearEquiv.ofBijective f ⟨h _ _ surj, surj⟩).symm_comp
    rwa [← left_inv_eq_right_inv this eq]

