/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import TauCeti.RepresentationTheory.OfMulAction.CosetLift
public import TauCeti.RepresentationTheory.Smooth.Colimits

/-!
# Smooth representations form a Grothendieck category

Smooth representations of a topological group over a ring have exact filtered colimits and a
generator. In particular, they have enough injectives and Ext groups. No invertibility of group
orders in the coefficient ring is needed.

Filtered colimits are computed on the underlying modules, so their exactness follows from
exactness of filtered colimits of abelian groups. For any coinitial family of open subgroups,
the permutation representations `A[G ⧸ U]` form a separating family: every vector of a smooth
representation is the image of the identity coset under a coset lift. Their coproduct is therefore
a generator. In a weakly locally compact nonarchimedean group one may use all compact open
subgroups, or any coinitial family of them.

The representation modules and the generator live in universe `max u v`, where `A : Type u` and
`G : Type v`. Exactness of filtered colimits is also provided for modules in an independent
universe.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987,
  §§1.1–1.2, pp. 3–4 (generators and exact filtered colimits).
-/

public section

open CategoryTheory Limits Representation

universe w u v

namespace TauCeti.SmoothRep

variable (A : Type u) [Ring A] (G : Type v) [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

/-- Filtered colimits of smooth representations are exact, with no restriction on the
coefficient characteristic. -/
instance ab5 : AB5OfSize.{w, w} (SmoothRep.{w} A G) where
  ofShape J _ _ := by
    have : PreservesFiniteLimits (ι.{w} A G) :=
      Functor.preservesFiniteLimits_of_preservesKernels _
    exact HasExactColimitsOfShape.domain_of_functor J
      (ι.{w} A G ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A) ⋙
        forget₂ (ModuleCat.{w} A) AddCommGrpCat.{w})

variable {G}

-- The family of open subgroups is in universe `v`, while its permutation modules are in
-- universe `max u v`. Use the existing colimits also for this smaller indexing universe.
local instance : HasColimitsOfSize.{v, v} (SmoothRep.{max u v} A G) :=
  hasColimitsOfSizeOfUnivLE.{max u v, max u v, v, v} _

/-- Permutation representations on the cosets of a coinitial family of open subgroups
separate morphisms of smooth representations. -/
theorem isSeparating_of_isCoinitial (S : Set (OpenSubgroup G)) (hS : IsCoinitial S) :
    ObjectProperty.IsSeparating (.ofObj (fun U : S ↦
      (of (ofMulAction A G (G ⧸ (U.val : Subgroup G))) : SmoothRep.{max u v} A G))) := by
  intro X Y f g h
  ext x
  obtain ⟨U, hUx⟩ : ∃ U : S, (U.val : Subgroup G) ≤ X.obj.ρ.stabilizer x := by
    obtain ⟨U, hU, hUx⟩ := hS ⟨X.obj.ρ.stabilizer x, IsSmooth.isOpen_stabilizer x⟩
    exact ⟨⟨U, hU⟩, hUx⟩
  let l : of (ofMulAction A G (G ⧸ (U.val : Subgroup G))) ⟶ X :=
    ObjectProperty.homMk (Rep.ofHom (X.obj.ρ.cosetLift U.val x hUx))
  have hl : l ≫ f = l ≫ g := h _ (ObjectProperty.ofObj_apply _ U) l
  have hv := congrArg (fun k ↦ k.hom.hom
    (MonoidAlgebra.single ((1 : G) : G ⧸ (U.val : Subgroup G)) 1)) hl
  simpa only [ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp,
    IntertwiningMap.comp_apply, l, ObjectProperty.homMk_hom, Rep.hom_ofHom,
    cosetLift_single, map_one, one_apply_eq_self, one_smul,
    IntertwiningMap.coe_toLinearMap] using hv

/-- The coproduct of the coset permutation representations over a coinitial family of open
subgroups is a generator of the smooth category. -/
theorem isSeparator_coproduct_of_isCoinitial (S : Set (OpenSubgroup G)) (hS : IsCoinitial S) :
    IsSeparator (∐ (fun U : S ↦
      (of (ofMulAction A G (G ⧸ (U.val : Subgroup G))) : SmoothRep.{max u v} A G))) :=
  (isSeparating_of_isCoinitial A S hS).isSeparator_coproduct

/-- The coproduct of the permutation representations over all open subgroups is a generator. -/
instance hasSeparator : HasSeparator (SmoothRep.{max u v} A G) where
  hasSeparator := ⟨_, isSeparator_coproduct_of_isCoinitial A Set.univ
    (fun U ↦ ⟨U, Set.mem_univ U, le_rfl⟩)⟩

variable (G)

/-- The category of smooth representations of a topological group over a ring is Grothendieck
abelian. Consequently Mathlib supplies enough injectives and Ext groups. -/
instance grothendieck : IsGrothendieckAbelian.{max u v} (SmoothRep.{max u v} A G) where

variable {G} [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- The compact-open coset permutation representations form a separating family. -/
theorem isSeparating_isCompact :
    ObjectProperty.IsSeparating (.ofObj (fun U : {U : OpenSubgroup G // IsCompact (U : Set G)} ↦
      (of (ofMulAction A G (G ⧸ (U.val : Subgroup G))) : SmoothRep.{max u v} A G))) :=
  isSeparating_of_isCoinitial A _ NonarchimedeanGroup.isCoinitial_isCompact_openSubgroup

/-- The coproduct of the compact-open coset permutation representations is a generator. -/
theorem isSeparator_coproduct_isCompact :
    IsSeparator (∐ (fun U : {U : OpenSubgroup G // IsCompact (U : Set G)} ↦
      (of (ofMulAction A G (G ⧸ (U.val : Subgroup G))) : SmoothRep.{max u v} A G))) :=
  (isSeparating_isCompact A).isSeparator_coproduct

end TauCeti.SmoothRep
