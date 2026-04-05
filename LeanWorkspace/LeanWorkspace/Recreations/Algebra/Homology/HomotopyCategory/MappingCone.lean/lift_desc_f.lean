import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem lift_desc_f {K L : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (α' : Cochain F L (-1)) (β' : G ⟶ L)
    (eq' : δ (-1) 0 α' = Cochain.ofHom (φ ≫ β')) (n n' : ℤ) (hnn' : n + 1 = n') :
    (CochainComplex.mappingCone.lift φ α β eq).f n ≫ (CochainComplex.mappingCone.desc φ α' β' eq').f n =
    α.1.v n n' hnn' ≫ α'.v n' n (by omega) + β.v n n (add_zero n) ≫ β'.f n := by
  simp only [CochainComplex.mappingCone.lift, CochainComplex.mappingCone.desc, Cocycle.homOf_f, liftCocycle_coe, descCocycle_coe, Cocycle.ofHom_coe,
    CochainComplex.mappingCone.liftCochain_v_descCochain_v φ α.1 β α' (Cochain.ofHom β') (zero_add 1) (neg_add_cancel 1) 0
    (add_zero 0) n n n (add_zero n) (add_zero n) n' hnn', Cochain.ofHom_v]

