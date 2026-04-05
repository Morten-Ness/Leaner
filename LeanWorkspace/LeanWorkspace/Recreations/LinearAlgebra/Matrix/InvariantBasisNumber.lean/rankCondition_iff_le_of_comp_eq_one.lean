import Mathlib

variable {R : Type*} [Semiring R]

theorem rankCondition_iff_le_of_comp_eq_one : RankCondition R ↔ ∀ n m
    (f : (Fin n → R) →ₗ[R] Fin m → R) (g : (Fin m → R) →ₗ[R] Fin n → R), f ∘ₗ g = 1 → m ≤ n := (rankCondition_iff R).trans ⟨fun h _ _ f _ eq ↦ h f (surjective_of_comp_eq_id _ _ eq),
    fun h _ _ _ hf ↦ have ⟨_, eq⟩ := Module.projective_lifting_property _ .id hf; h _ _ _ _ eq⟩

