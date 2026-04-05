import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq_span : Subalgebra.toSubmodule (Algebra.adjoin R s) = span R (Submonoid.closure s) := by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction L with
    | nil => exact zero_mem _
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons, List.sum_cons]
    refine Submodule.add_mem _ ?_ (ih HL.2)
    replace HL := HL.1
    clear ih tl
    suffices ∃ (z r : _) (_hr : r ∈ Submonoid.closure s), z • r = List.prod hd by
      rcases this with ⟨z, r, hr, hzr⟩
      rw [← hzr]
      exact smul_mem _ _ (subset_span hr)
    induction hd with
    | nil => exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rcases ih HL.2 with ⟨z, r, hr, hzr⟩
    rw [List.prod_cons, ← hzr]
    rcases HL.1 with (⟨hd, rfl⟩ | hs)
    · refine ⟨hd * z, r, hr, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, (algebraMap _ _).map_mul, _root_.mul_assoc]
    · exact
        ⟨z, hd * r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr,
          (mul_smul_comm _ _ _).symm⟩
  refine span_le.2 ?_
  change Submonoid.closure s ≤ (Algebra.adjoin R s).toSubsemiring.toSubmonoid
  exact Submonoid.closure_le.2 Algebra.subset_adjoin

