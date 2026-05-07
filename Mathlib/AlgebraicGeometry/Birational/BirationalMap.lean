/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Birational maps between schemes

TODO

-/

@[expose] public section

universe u

open CategoryTheory hiding Quotient

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

namespace Scheme

/--
A bipartial map from `X` to `Y` (`X.BipartialMap Y`) is... TODO
-/
structure BipartialMap (X Y : Scheme.{u}) where
  /-- The domain of definition of a bipartial map. -/
  domain : X.Opens
  dense_domain : Dense (domain : Set X)
  /-- The target of a bipartial map. -/
  target : Y.Opens
  dense_target : Dense (target : Set Y)
  /-- The underlying morphism of a partial map. -/
  hom : domain.toScheme ≅ target.toScheme

namespace BipartialMap

def symm (f : X.BipartialMap Y) : Y.BipartialMap X where
  domain := f.target
  dense_domain := f.dense_target
  target := f.domain
  dense_target := f.dense_domain
  hom := f.hom.symm

def toPartialMap (f : X.BipartialMap Y) : X.PartialMap Y where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := f.hom.hom ≫ f.target.ι

lemma ext_iff (f g : X.BipartialMap Y) :
    f = g ↔ ∃ (e : f.domain = g.domain) (e' : g.target = f.target),
      f.hom = X.isoOfEq e ≪≫ g.hom ≪≫ Y.isoOfEq e' := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [mk.injEq, forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]
lemma ext (f g : X.BipartialMap Y) (e : f.domain = g.domain) (e' : g.target = f.target)
    (H : f.hom = X.isoOfEq e ≪≫ g.hom ≪≫ Y.isoOfEq e') : f = g := by
  rw [ext_iff]
  exact ⟨e, e', H⟩

/-- The restriction of a partial map to a smaller domain. -/
/- @[simps hom domain] -/
noncomputable
def restrict (f : X.BipartialMap Y) (U : X.Opens) (hU : Dense (U : Set X)) : X.BipartialMap Y where
  domain := U
  dense_domain := hU
  target := opensRestrict _ (f.hom.hom ''ᵁ ⊤)
  dense_target := by
    simp
    sorry
  hom := by
    simp
    sorry


/-- The composition of a partial map and a morphism on the right. -/
@[simps]
noncomputable def compIso (f : X.BipartialMap Y) (g : Y ≅ Z) : X.BipartialMap Z where
  domain := f.domain
  dense_domain := f.dense_domain
  target := g.hom ''ᵁ f.target
  dense_target := by sorry
  hom := f.hom ≪≫ g.hom.isoImage f.target

noncomputable
def _root_.CategoryTheory.Iso.toBipartialMap (f : X ≅ Y) : X.BipartialMap Y where
  domain := ⊤
  dense_domain := dense_univ
  target := ⊤
  dense_target := dense_univ
  hom := X.topIso ≪≫ f ≪≫ Y.topIso.symm

end BipartialMap

end Scheme

end AlgebraicGeometry
