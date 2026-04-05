import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_coe_image_includeRight_eq_center_tensorProduct
    (S : Set B) [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight '' S) =
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (Subalgebra.centralizer R (S : Set B)).val).range := by
  have eq1 := Subalgebra.centralizer_coe_image_includeLeft_eq_center_tensorProduct R B A S
  apply_fun Subalgebra.comap (Algebra.TensorProduct.comm R A B).toAlgHom at eq1
  convert eq1
  · ext x
    simpa [mem_centralizer_iff] using
      ⟨fun h b hb ↦ (Algebra.TensorProduct.comm R A B).symm.injective <| by aesop, fun h b hb ↦
        (Algebra.TensorProduct.comm R A B).injective <| by aesop⟩
  · ext x
    simp only [AlgHom.mem_range, AlgEquiv.toAlgHom_eq_coe, mem_comap, AlgHom.coe_coe]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Algebra.TensorProduct.comm R _ _) x,
        by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(Algebra.TensorProduct.comm R _ _) y, (Algebra.TensorProduct.comm R A B).injective ?_⟩
      rw [← hy, comm_comp_map_apply, ← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]

