import Mathlib

variable {R : Type u} [Ring R]

theorem binaryProductLimitCone_cone_π_app_right (M N : ModuleCat.{v} R) :
    (ModuleCat.binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.right⟩ = ofHom (LinearMap.snd R M N) := rfl

