import Mathlib

section

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem Algebra.TensorProduct.includeLeft_map_center_le :
    (Subalgebra.center K B).map includeLeft ≤ Subalgebra.center K (B ⊗[K] C) := by
  intro x hx
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨b, hb0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b' c => simp [hb0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

end

section

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem Algebra.TensorProduct.includeRight_map_center_le :
    (Subalgebra.center K C).map includeRight ≤ Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨c, hc0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c' => simp [hc0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

end

section

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem left_of_tensor (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
    [hbc : Algebra.IsCentral K (B ⊗[K] C)] : Algebra.IsCentral K B where
  out := (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ ↦ ⟨k, includeLeft_injective (S := K) inj hk⟩

end

section

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem left_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial C]
    [Algebra K B] [Algebra K C] [Algebra.IsCentral K (B ⊗[K] C)] : Algebra.IsCentral K B := Algebra.IsCentral.left_of_tensor K B C <| FaithfulSMul.algebraMap_injective K C

end

section

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem right_of_tensor (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
    [Algebra.IsCentral K (B ⊗[K] C)] : Algebra.IsCentral K C := have : Algebra.IsCentral K (C ⊗[K] B) := Algebra.IsCentral.of_algEquiv K _ _ <| Algebra.TensorProduct.comm _ _ _
  Algebra.IsCentral.left_of_tensor K C B inj

end

section

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem right_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial B]
    [Algebra K B] [Algebra K C] [Algebra.IsCentral K (B ⊗[K] C)] : Algebra.IsCentral K C := Algebra.IsCentral.right_of_tensor K B C <| FaithfulSMul.algebraMap_injective K B

end
