/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Generator

/-!
# The graded bracket (definition only)

For the fermionic instance (M4) the bracket of two homogeneous elements is the anticommutator
when both are odd and the commutator otherwise (M1a, Section 4). Only the bracket and its norm
bound are defined here, so that M4 changes no definition of M1a; the graded net, parity
preservation and the graded master lemma are M4's.

## Main definitions

* `LocalityLean.gradedComm`: `[a, b]_± = a b - (-1)^{|a||b|} b a`, with the parities given as
  Booleans (`true` = odd).

## Main statements

* `LocalityLean.gradedComm_false_left`, `gradedComm_false_right`: the commutator when either
  element is even; `gradedComm_true_true`: the anticommutator when both are odd.
* `LocalityLean.norm_gradedComm_le`: `‖[a, b]_±‖ ≤ 2 ‖a‖ ‖b‖`.
-/

namespace LocalityLean

variable {A : Type*} [CStarAlgebra A]

/-- The graded bracket `[a, b]_± = a b - (-1)^{|a||b|} b a`, the anticommutator when both
parities are odd (`true`) and the commutator otherwise. -/
def gradedComm (oddA oddB : Bool) (a b : A) : A :=
  a * b - (if oddA && oddB then -1 else 1 : ℂ) • (b * a)

theorem gradedComm_false_left (oddB : Bool) (a b : A) :
    gradedComm false oddB a b = comm a b := by
  simp [gradedComm, comm]

theorem gradedComm_false_right (oddA : Bool) (a b : A) :
    gradedComm oddA false a b = comm a b := by
  simp [gradedComm, comm]

theorem gradedComm_true_true (a b : A) : gradedComm true true a b = a * b + b * a := by
  simp [gradedComm, sub_eq_add_neg]

/-- `‖[a, b]_±‖ ≤ 2 ‖a‖ ‖b‖` for every choice of parities. -/
theorem norm_gradedComm_le (oddA oddB : Bool) (a b : A) :
    ‖gradedComm oddA oddB a b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  have hsign : ‖(if oddA && oddB then -1 else 1 : ℂ)‖ = 1 := by split_ifs <;> simp
  calc ‖gradedComm oddA oddB a b‖
      ≤ ‖a * b‖ + ‖(if oddA && oddB then -1 else 1 : ℂ) • (b * a)‖ := norm_sub_le _ _
    _ = ‖a * b‖ + ‖b * a‖ := by rw [norm_smul, hsign, one_mul]
    _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖a‖ * ‖b‖ := by ring

end LocalityLean
