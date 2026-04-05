import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_coe_image_includeLeft_eq_center_tensorProduct
    (S : Set A) [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft (S := R) '' S) =
    (Algebra.TensorProduct.map (Subalgebra.centralizer R (S : Set A)).val
      (AlgHom.id R B)).range := by
  classical
  ext w
  constructor
  · intro hw
    rw [mem_centralizer_iff] at hw
    let ℬ := Module.Free.chooseBasis R B
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ w
    refine Subalgebra.sum_mem _ fun j hj => ⟨⟨b j, ?_⟩ ⊗ₜ[R] ℬ j, by simp⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro x hx
    suffices x • b = b.mapRange (· * x) (by simp) from Finsupp.ext_iff.1 this j
    specialize hw (x ⊗ₜ[R] 1) ⟨x, hx, rfl⟩
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at hw
    refine TensorProduct.sum_tmul_basis_right_injective ℬ ?_
    simp only [Finsupp.coe_lsum]
    rw [sum_of_support_subset (s := b.support) (hs := Finsupp.support_smul) (h := by simp),
      sum_of_support_subset (s := b.support) (hs := support_mapRange) (h := by simp)]
    simpa only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, LinearMap.flip_apply,
      TensorProduct.mk_apply, Finsupp.mapRange_apply] using hw
  · rintro ⟨w, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp [Subalgebra.mem_centralizer_iff _ |>.1 b.2 x hx]
    | add y z hy hz => rw [map_add, mul_add, hy, hz, add_mul]

