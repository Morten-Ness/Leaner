import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem mem_div_iff_smul_subset {x : A} {I J : Submodule R A} : x ∈ I / J ↔ x • (J : Set A) ⊆ I := ⟨fun h y ⟨y', hy', xy'_eq_y⟩ => by rw [← xy'_eq_y]; exact h _ hy',
    fun h _ hy => h (Set.smul_mem_smul_set hy)⟩

