/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
/-!

# The category of irreducible schemes with dominant rational maps

## TODO

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

namespace Scheme

structure BirationalCat where
  private mk ::
  carrier : Scheme.{u}
  [isIrreducible : IrreducibleSpace carrier]

attribute [instance] BirationalCat.isIrreducible

structure BirationalCat.Hom (X Y : BirationalCat.{u}) where
  hom : X.carrier ⤏ Y.carrier
  [isDominant : hom.IsDominant]

attribute [instance] BirationalCat.Hom.isDominant

noncomputable instance : Category (BirationalCat.{u}) where
  Hom X Y := BirationalCat.Hom X Y
  id X := ⟨RationalMap.id X.carrier⟩
  comp f g := ⟨f.hom.comp g.hom⟩
  assoc := by
    simp
  id_comp := by simp
  comp_id := by simp

end Scheme

end AlgebraicGeometry
