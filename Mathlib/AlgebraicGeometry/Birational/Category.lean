/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Birational.BirationalMap

/-!
# The category of irreducible schemes with dominant rational maps

## TODO

-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

namespace Scheme

@[ext]
structure BirationalCat where
  carrier : Scheme.{u}
  [isIrreducible : IrreducibleSpace carrier]

attribute [instance] BirationalCat.isIrreducible

instance : Coe BirationalCat.{u} Scheme.{u} where
  coe := BirationalCat.carrier

def toBirationalCat (X : Scheme.{u}) [IrreducibleSpace X] : BirationalCat.{u} := ⟨X⟩

@[simp]
lemma toBirationalCat_coe (X : Scheme.{u}) [IrreducibleSpace X] :
    X.toBirationalCat.carrier = X := rfl

@[ext]
structure BirationalCat.Hom (X Y : BirationalCat.{u}) where
  hom : X ⤏ Y
  [isDominant : hom.IsDominant]

attribute [instance] BirationalCat.Hom.isDominant

noncomputable instance : Category (BirationalCat.{u}) where
  Hom X Y := BirationalCat.Hom X Y
  id X := ⟨RationalMap.id X.carrier⟩
  comp f g := ⟨f.hom.comp g.hom⟩
  assoc f g h := by ext; exact f.hom.comp_assoc g.hom h.hom
  id_comp f := by ext; exact f.hom.id_comp
  comp_id f := by ext; exact f.hom.comp_id

set_option backward.isDefEq.respectTransparency false in
def RationalMap.toBirationalCatHom
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⤏ Y) [f.IsDominant] :
    X.toBirationalCat ⟶ Y.toBirationalCat :=
  ⟨f⟩

-- TODO
def BirationalCat.equivIso (X Y : BirationalCat.{u}) : (X ≅ Y) ≃ BirationalMap X Y := sorry

abbrev Cremona (n : Type v) (S : Scheme.{max u v}) [IrreducibleSpace S] :=
  Aut (𝔸(n; S).toBirationalCat)

end Scheme

end AlgebraicGeometry
