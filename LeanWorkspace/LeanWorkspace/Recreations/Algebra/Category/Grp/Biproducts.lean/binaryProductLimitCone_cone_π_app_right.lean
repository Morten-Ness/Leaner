import Mathlib

theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGrpCat.{u}) :
    (AddCommGrpCat.binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = ofHom (AddMonoidHom.snd G H) := rfl

