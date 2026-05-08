/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Birational maps between schemes

TODO

-/

@[expose] public section

universe u v

open CategoryTheory hiding Quotient

namespace AlgebraicGeometry

namespace Scheme

variable {X Y Z S : Scheme.{u}}

/--
A partial isomorphism from `X` to `Y` (`X.BipartialMap Y`) is... TODO
-/
structure PartialIso (X Y : Scheme.{u}) where
  /-- The domain of definition of a partial iso. -/
  domain : X.Opens
  dense_domain : Dense (domain : Set X)
  /-- The target of a partial iso. -/
  target : Y.Opens
  dense_target : Dense (target : Set Y)
  /-- The underlying isomorphism of a partial iso. -/
  iso : domain.toScheme ≅ target.toScheme

namespace PartialIso

variable (S) in
abbrev IsOver (f : X.PartialIso Y) [X.Over S] [Y.Over S] : Prop :=
  f.iso.hom.IsOver S

def refl : X.PartialIso X where
  domain := ⊤
  dense_domain := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _

def symm (f : X.PartialIso Y) : Y.PartialIso X where
  domain := f.target
  dense_domain := f.dense_target
  target := f.domain
  dense_target := f.dense_domain
  iso := f.iso.symm

def toPartialMap (f : X.PartialIso Y) : X.PartialMap Y where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := f.iso.hom ≫ f.target.ι

lemma ext_iff (f g : X.PartialIso Y) :
    f = g ↔ ∃ (e : f.domain = g.domain) (e' : g.target = f.target),
      f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e' := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]
lemma ext (f g : X.PartialIso Y) (e : f.domain = g.domain) (e' : g.target = f.target)
    (H : f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e') : f = g := by
  rw [ext_iff]
  exact ⟨e, e', H⟩

/-- The composition of a partial map and a morphism on the right. -/
@[simps]
noncomputable def compIso (f : X.PartialIso Y) (g : Y ≅ Z) : X.PartialIso Z where
  domain := f.domain
  dense_domain := f.dense_domain
  target := g.hom ''ᵁ f.target
  dense_target := by sorry
  iso := f.iso ≪≫ g.hom.isoImage f.target

noncomputable
def _root_.CategoryTheory.Iso.toPartialIso (f : X ≅ Y) : X.PartialIso Y where
  domain := ⊤
  dense_domain := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm

end PartialIso

variable (X Y) in
def Birational : Prop :=
  Nonempty (PartialIso X Y)

variable (X Y S) in
def BirationalOver [X.Over S] [Y.Over S] :=
  ∃ f : PartialIso X Y, f.IsOver S

def RationalOver [X.Over S] : Prop :=
  ∃ n, BirationalOver X (AffineSpace (Fin n) S) S

end Scheme

end AlgebraicGeometry
