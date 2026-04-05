import Mathlib

variable {R : Type u} [Ring R]

theorem binaryProductLimitCone_cone_π_app_left (M N : ModuleCat.{v} R) :
    (ModuleCat.binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.left⟩ = ofHom (LinearMap.fst R M N) := rfl

