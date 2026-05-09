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

structure BirationalScheme where
  private mk ::
  carrier : Scheme.{u}
  [isIrreducible : IrreducibleSpace carrier]

attribute [instance] BirationalScheme.isIrreducible

structure BirationalScheme.Hom (X Y : BirationalScheme.{u}) where
  hom : X.carrier ⤏ Y.carrier
  [isDominant : hom.IsDominant]

attribute [instance] BirationalScheme.Hom.isDominant

noncomputable instance : Category (BirationalScheme.{u}) where
  Hom X Y := BirationalScheme.Hom X Y
  id X := ⟨RationalMap.id X.carrier⟩
  comp f g := by
    exact ⟨f.hom.comp g.hom⟩
  assoc := sorry
  id_comp := sorry
  comp_id := sorry

end Scheme

end AlgebraicGeometry
