import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem comap_map_eq (f : A →ₐ[R] B) (S : Subalgebra R A) :
    (S.map f).comap f = S ⊔ Algebra.adjoin R (f ⁻¹' {0}) := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap, mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y ∈ f ⁻¹' {0} := by simp [hxy]
    rw [← Algebra.adjoin_eq S, ← Algebra.adjoin_union, ← add_sub_cancel y x]
    exact Subalgebra.add_mem _
      (Algebra.subset_adjoin <| Or.inl hy) (Algebra.subset_adjoin <| Or.inr hxy)
  · rw [← map_le, Algebra.map_sup, AlgHom.map_adjoin f]
    apply le_of_eq
    rw [sup_eq_left, Algebra.adjoin_le_iff]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (S.map f).zero_mem)

