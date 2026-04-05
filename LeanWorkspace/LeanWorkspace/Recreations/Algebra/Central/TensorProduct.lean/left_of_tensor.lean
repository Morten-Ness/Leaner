import Mathlib

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem left_of_tensor (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
    [hbc : Algebra.IsCentral K (B ⊗[K] C)] : Algebra.IsCentral K B where
  out := (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ ↦ ⟨k, includeLeft_injective (S := K) inj hk⟩

