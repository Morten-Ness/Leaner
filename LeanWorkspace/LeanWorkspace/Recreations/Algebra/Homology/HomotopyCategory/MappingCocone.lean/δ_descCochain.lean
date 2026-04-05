import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

set_option backward.isDefEq.respectTransparency false in
theorem δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ m n (CochainComplex.mappingCocone.descCochain φ α β h) =
      (Cochain.ofHom (CochainComplex.mappingCocone.fst φ)).comp
        (δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (zero_add n) +
      (CochainComplex.mappingCocone.snd φ).comp (δ n n' β) (by lia) := by
  dsimp [CochainComplex.mappingCocone.descCochain, CochainComplex.mappingCocone.fst, CochainComplex.mappingCocone.snd, CochainComplex.mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by lia
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by lia),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ (p + -1) (by lia),
    Cochain.leftShift_v (n := m + 2) _ (-1) _ _ _ q _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.comp_v (n₁ := 1) _ _ _ (p + -1) p _ (by lia) hpq,
    Cochain.comp_v (n₂ := m + 2) _ _ _ p (p + -1) q rfl (by lia),
    smul_smul, Int.negOnePow_add, Int.negOnePow_even 2 ⟨1, rfl⟩]
  grind

