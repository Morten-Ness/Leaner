import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem range_liftHom (B : QuaternionAlgebra.Basis A c₁ c₂ c₃) :
    (QuaternionAlgebra.Basis.liftHom B).range = Algebra.adjoin R {B.i, B.j, B.k} := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact algebraMap_mem _ _
    all_goals
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin <| by simp) _
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | rfl | rfl)
      <;> [use (QuaternionAlgebra.Basis.self R).i; use (QuaternionAlgebra.Basis.self R).j; use (QuaternionAlgebra.Basis.self R).k]
    all_goals simp [QuaternionAlgebra.Basis.lift]

