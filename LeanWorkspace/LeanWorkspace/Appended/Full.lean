import Mathlib

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ := e.toEquiv.apply_eq_iff_eq_symm_apply

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem constVAdd_nsmul (n : ℕ) (v : V₁) : AffineEquiv.constVAdd k P₁ (n • v) = AffineEquiv.constVAdd k P₁ v ^ n := (AffineEquiv.constVAddHom k P₁).map_pow _ _

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem constVAdd_zsmul (z : ℤ) (v : V₁) : AffineEquiv.constVAdd k P₁ (z • v) = AffineEquiv.constVAdd k P₁ v ^ z := (AffineEquiv.constVAddHom k P₁).map_zpow _ _

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable {R' : Type*} [CommRing R'] [Module R' V₁]

theorem homothety_neg_one_apply (c p : P₁) : AffineMap.homothety c (-1 : R') p = AffineEquiv.pointReflection R' c p := by
  simp [AffineMap.homothety_apply, Equiv.pointReflection_apply]

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s := f.symm.toEquiv.image_eq_preimage_symm _

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem injective_pointReflection_left_of_injective_two_nsmul
    (h : Function.Injective (2 • · : V₁ → V₁)) (y : P₁) :
    Function.Injective fun x : P₁ => AffineEquiv.pointReflection k x y := Equiv.injective_pointReflection_left_of_injective_two_nsmul h y

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem injective_pointReflection_left_of_module [Invertible (2 : k)] :
    ∀ y, Function.Injective fun x : P₁ => AffineEquiv.pointReflection k x y := AffineEquiv.injective_pointReflection_left_of_injective_two_nsmul k fun x y h => by
    dsimp at h
    rwa [two_nsmul, two_nsmul, ← two_smul k x, ← two_smul k y,
      (isUnit_of_invertible (2 : k)).smul_left_cancel] at h

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem lineMap_vadd (v v' : V₁) (p : P₁) (c : k) :
    AffineMap.lineMap v v' c +ᵥ p = AffineMap.lineMap (v +ᵥ p) (v' +ᵥ p) c := AffineEquiv.apply_lineMap (AffineEquiv.vaddConst k p) v v' c

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem lineMap_vsub (p₁ p₂ p₃ : P₁) (c : k) :
    AffineMap.lineMap p₁ p₂ c -ᵥ p₃ = AffineMap.lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₃) c := AffineEquiv.apply_lineMap (AffineEquiv.vaddConst k p₃).symm p₁ p₂ c

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable {k V P : Type*}

variable [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem ofLinearEquiv_refl (p : P) :
    AffineEquiv.ofLinearEquiv (.refl k V) p p = .refl k P := by
  ext x
  simp [AffineEquiv.ofLinearEquiv_apply]

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P₁}
    (h : Function.Injective (2 • · : V₁ → V₁)) : AffineEquiv.pointReflection k x y = y ↔ y = x := Equiv.pointReflection_fixed_iff_of_injective_two_nsmul h

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem pointReflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} :
    AffineEquiv.pointReflection k x y = y ↔ y = x := ((AffineEquiv.injective_pointReflection_left_of_module k y).eq_iff' (AffineEquiv.pointReflection_self k y)).trans eq_comm

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem pointReflection_symm (x : P₁) : (AffineEquiv.pointReflection k x).symm = AffineEquiv.pointReflection k x := AffineEquiv.toEquiv_injective <| Equiv.pointReflection_symm x

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem preimage_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s := (AffineEquiv.image_symm f.symm _).symm

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem self_trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans e.symm = AffineEquiv.refl k P₁ := AffineEquiv.ext AffineEquiv.symm_apply_apply e

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem symm_trans_self (e : P₁ ≃ᵃ[k] P₂) : e.symm.trans e = AffineEquiv.refl k P₂ := AffineEquiv.ext AffineEquiv.apply_symm_apply e

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e = e' := AffineEquiv.toAffineMap_injective.eq_iff

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem toAffineMap_injective : Function.Injective (AffineEquiv.toAffineMap : (P₁ ≃ᵃ[k] P₂) → P₁ →ᵃ[k] P₂) := by
  rintro ⟨e, el, h⟩ ⟨e', el', h'⟩ H
  simp_all

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem toEquiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toEquiv = e'.toEquiv ↔ e = e' := AffineEquiv.toEquiv_injective.eq_iff

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem toEquiv_injective : Function.Injective (AffineEquiv.toEquiv : (P₁ ≃ᵃ[k] P₂) → P₁ ≃ P₂) := fun _ _ H =>
  AffineEquiv.ext <| Equiv.ext_iff.1 H

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem vadd_lineMap (v : V₁) (p₁ p₂ : P₁) (c : k) :
    v +ᵥ AffineMap.lineMap p₁ p₂ c = AffineMap.lineMap (v +ᵥ p₁) (v +ᵥ p₂) c := AffineEquiv.apply_lineMap (AffineEquiv.constVAdd k P₁ v) p₁ p₂ c

end

section

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem vsub_lineMap (p₁ p₂ p₃ : P₁) (c : k) :
    p₁ -ᵥ AffineMap.lineMap p₂ p₃ c = AffineMap.lineMap (p₁ -ᵥ p₂) (p₁ -ᵥ p₃) c := AffineEquiv.apply_lineMap (AffineEquiv.constVSub k p₁) p₂ p₃ c

end
