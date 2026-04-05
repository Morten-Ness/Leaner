import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem map_mul {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') :
    map f.toLinearMap (M * N) = map f.toLinearMap M * map f.toLinearMap N := calc
    map f.toLinearMap (M * N) = ⨆ i : M, (N.map (LinearMap.mul R A i)).map f.toLinearMap := by
      rw [Submodule.mul_eq_map₂]; apply map_iSup
    _ = map f.toLinearMap M * map f.toLinearMap N := by
      rw [Submodule.mul_eq_map₂]
      apply congr_arg sSup
      ext S
      constructor <;> rintro ⟨y, hy⟩
      · use ⟨f y, mem_map.mpr ⟨y.1, y.2, rfl⟩⟩
        refine Eq.trans ?_ hy
        ext
        simp
      · obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2
        use ⟨y', hy'⟩
        refine Eq.trans ?_ hy
        rw [f.toLinearMap_apply] at fy_eq
        ext
        simp [fy_eq]

