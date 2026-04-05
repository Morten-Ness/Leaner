import Mathlib

theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGrpCat.{u}) :
    (AddCommGrpCat.binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = ofHom (AddMonoidHom.fst G H) := rfl

