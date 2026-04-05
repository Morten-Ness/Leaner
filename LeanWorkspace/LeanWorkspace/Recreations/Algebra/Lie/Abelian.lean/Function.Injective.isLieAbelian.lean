import Mathlib

theorem Function.Injective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ →ₗ⁅R⁆ L₂}
    (h₁ : Function.Injective f) (_ : IsLieAbelian L₂) : IsLieAbelian L₁ := { trivial := fun x y => h₁ <|
      calc
        f ⁅x, y⁆ = ⁅f x, f y⁆ := LieHom.map_lie f x y
        _ = 0 := trivial_lie_zero _ _ _ _
        _ = f 0 := (map_zero _).symm }

