import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

set_option backward.isDefEq.respectTransparency false in
theorem δ_liftCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (CochainComplex.mappingCocone.liftCochain φ α β h) =
      (δ n n' α).comp (CochainComplex.mappingCocone.inl φ) (add_zero _) -
        (δ m n β + α.comp (Cochain.ofHom φ) (add_zero n)).comp (CochainComplex.mappingCocone.inr φ).1 hn' := by
  dsimp [CochainComplex.mappingCocone.liftCochain, CochainComplex.mappingCocone.inl, CochainComplex.mappingCocone.inr]
  ext p q hpq
  simp [mappingCone.δ_liftCochain _ _ _ _ n' hn',
    Cochain.δ_rightShift _ (-1) _ n' _ n  (by lia),
    Cochain.rightShift_v (n := n) _ _ _ _ p _ _ (q + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (q + -1)),
    Cochain.comp_v _ _ _ p q _ hpq rfl,
    Cochain.comp_v (n₁ := n) (n₂ := 1) _ _ _ p (q + -1) q (by lia) (by lia)]
  grind

