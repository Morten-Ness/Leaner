import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem NonUnitalAlgHom.quasispectrum_apply_subset' {F R : Type*} (S : Type*) {A B : Type*}
    [CommSemiring R] [Semiring S] [NonUnitalRing A] [NonUnitalRing B] [Module R S]
    [Module S A] [Module R A] [Module S B] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B]
    [FunLike F A B] [NonUnitalAlgHomClass F S A B] (φ : F) (a : A) :
    quasispectrum R (φ a) ⊆ quasispectrum R a := by
  refine Set.compl_subset_compl.mp fun x ↦ ?_
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not,
    forall_exists_index]
  refine fun hx this ↦ ⟨hx, ?_⟩
  rw [Units.smul_def, ← smul_one_smul S] at this ⊢
  simpa [-smul_assoc] using this.map φ

