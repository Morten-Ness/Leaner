import Mathlib

set_option backward.privateInPublic true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g := Hom.ext hf

