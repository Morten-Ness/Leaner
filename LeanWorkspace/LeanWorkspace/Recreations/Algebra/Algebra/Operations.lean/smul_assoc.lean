import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_assoc {B} [Semiring B] [Module R B] [Module A B] [Module B M]
    [IsScalarTower R A B] [IsScalarTower R B M] [IsScalarTower A B M]
    (I : Submodule R A) (J : Submodule R B) (N : Submodule R M) :
    (I • J) • N = I • J • N := le_antisymm
    (Submodule.smul_le.2 fun _ hrsij t htn ↦ Submodule.smul_induction_on hrsij
      (fun r hr s hs ↦ smul_assoc r s t ▸ Submodule.smul_mem_smul hr (Submodule.smul_mem_smul hs htn))
      fun x y ↦ (add_smul x y t).symm ▸ add_mem)
    (Submodule.smul_le.2 fun r hr _ hsn ↦ Submodule.smul_induction_on hsn
      (fun j hj n hn ↦ (smul_assoc r j n).symm ▸ Submodule.smul_mem_smul (Submodule.smul_mem_smul hr hj) hn)
      fun m₁ m₂ ↦ (smul_add r m₁ m₂) ▸ add_mem)

