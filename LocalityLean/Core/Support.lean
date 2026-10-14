/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LinearAQFT.Net.Basic
import LinearAQFT.Causal.Basic

/-!
# Supports: the lattice causal index and causal nets

The regions of a lattice are all subsets of the site type `Λ`. Two regions are orthogonal when
they are disjoint, and a region depends on every region containing it: this is the lattice causal
index (M1a, statement 1), LinearAQFT's `subsetCausalIndex`, shared with QCALean's
`latticeIndex`. A net `𝒜 : Net (Set Λ) A`
(LinearAQFT) is causal for it when the local algebras of disjoint regions commute.

## Main definitions

* `LocalityLean.latticeIndex Λ`.

## Main statements

* `LocalityLean.latticeIndex_orthogonal_iff`, `LocalityLean.latticeIndex_dependent_iff`.
* `LocalityLean.commute_of_isCausal_of_disjoint`: in a causal net, `a ∈ 𝒜 X`, `b ∈ 𝒜 Y` and
  `Disjoint X Y` give `Commute a b`.
-/

namespace LocalityLean

open LinearAQFT

/-- The lattice causal index on the subsets of a site set: disjoint sets are orthogonal, and a
set depends on every set containing it (M1a, statement 1). -/
def latticeIndex (Λ : Type*) : CausalIndex (Set Λ) := subsetCausalIndex Λ

variable {Λ : Type*}

theorem latticeIndex_orthogonal_iff (X Y : Set Λ) :
    (latticeIndex Λ).Orthogonal X Y ↔ Disjoint X Y := Iff.rfl

theorem latticeIndex_dependent_iff (X Y : Set Λ) :
    (latticeIndex Λ).Dependent X Y ↔ X ⊆ Y := Iff.rfl

variable {A : Type*} [CStarAlgebra A]

/-- In a net that is causal for the lattice index, elements of the local algebras of disjoint
regions commute. -/
theorem commute_of_isCausal_of_disjoint {𝒜 : Net (Set Λ) A}
    (hc : Net.IsCausal (latticeIndex Λ) 𝒜) {X Y : Set Λ} (hXY : Disjoint X Y) {a b : A}
    (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) : Commute a b :=
  hc hXY a ha b hb

end LocalityLean
