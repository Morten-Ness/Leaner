import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)

set_option backward.isDefEq.respectTransparency false in
theorem δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (CochainComplex.mappingCone.descCochain φ α β h) =
      (CochainComplex.mappingCone.fst φ).1.comp (δ m n α +
          n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (by lia) +
      (CochainComplex.mappingCone.snd φ).comp (δ n n' β) (zero_add n') := by
  dsimp only [CochainComplex.mappingCone.descCochain]
  simp only [δ_add, Cochain.comp_add, δ_comp (CochainComplex.mappingCone.fst φ).1 α _ 2 n n' hn' (by lia) (by lia),
    Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero,
    δ_comp (CochainComplex.mappingCone.snd φ) β (zero_add n) 1 n' n' hn' (zero_add 1) hn', CochainComplex.mappingCone.δ_snd, Cochain.neg_comp,
    smul_neg, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_units_smul, ← hn',
    Int.negOnePow_succ, Units.neg_smul, Cochain.comp_neg]
  abel

