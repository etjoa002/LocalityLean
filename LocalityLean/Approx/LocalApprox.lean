/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Generator

/-!
# Nets with local approximation

A net has *local approximation* when every region `X` carries a map `P X` into its local
algebra with `‖c - P X c‖ ≤ N_{Xᶜ}(c)`: an element that nearly commutes with everything outside
`X` is nearly local to `X` (M3, Definition 2.2 and Theorem 3.5). The converse inequality
`N_Y(c) ≤ 2 ‖c - p‖` holds on every causal net for every `p ∈ 𝒜 X` and every `Y` disjoint from
`X`. The qudit net has local approximation through its conditional expectation
(`LocalityLean/Approx/Twirl.lean`).

The approximate locality of a map, `IsApproxLocalWith 𝒜 T nbhd ε` (M3, Definition 2.3), is the
statement shape of the truncated dynamics: every `x ∈ 𝒜 O` is sent within `ε ‖x‖` of
`𝒜 (nbhd O)`. At `ε = 0` it is the locality condition of a quantum cellular automaton,
`T x ∈ 𝒜 (nbhd O)`.

## Main definitions

* `LocalityLean.LocalApprox`, `LocalityLean.IsApproxLocalWith`.

## Main statements

* `LocalityLean.commNorm_le_two_mul_norm_sub`, `LocalityLean.isApproxLocalWith_zero_iff`.
-/

noncomputable section

namespace LocalityLean

open LinearAQFT

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]

/-- A net with local approximation: maps `P X` into `𝒜 X` with `‖c - P X c‖ ≤ N_{Xᶜ}(c)`
(M3, Definition 2.2 with Theorem 3.5). -/
structure LocalApprox (𝒜 : Net (Set Λ) A) where
  /-- The approximant of `c` in the local algebra of `X`. -/
  P : Set Λ → A → A
  P_mem : ∀ X c, P X c ∈ 𝒜 X
  norm_sub_P_le : ∀ X c, ‖c - P X c‖ ≤ commNorm 𝒜 Xᶜ c

/-- M3, Theorem 3.5, the converse inequality on any causal net: `N_Y(c) ≤ 2 ‖c - p‖` for
`p ∈ 𝒜 X` and `Y` disjoint from `X`. -/
theorem commNorm_le_two_mul_norm_sub {𝒜 : Net (Set Λ) A} (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    {X Y : Set Λ} (hXY : Disjoint X Y) {c p : A} (hp : p ∈ 𝒜 X) :
    commNorm 𝒜 Y c ≤ 2 * ‖c - p‖ :=
  commNorm_le_of_forall 𝒜 Y fun b hb hb1 => by
    have h0 : comm p b = 0 :=
      comm_eq_zero_of_commute (commute_of_isCausal_of_disjoint hc hXY hp hb)
    have h1 : comm c b = comm (c - p) b := by rw [comm_sub_left, h0, sub_zero]
    rw [h1]
    calc ‖comm (c - p) b‖ ≤ 2 * ‖c - p‖ * ‖b‖ := norm_comm_le _ _
      _ ≤ 2 * ‖c - p‖ * 1 := by gcongr
      _ = 2 * ‖c - p‖ := mul_one _

namespace LocalApprox

variable {𝒜 : Net (Set Λ) A} (Q : LocalApprox 𝒜)

/-- The two-sided estimate: `N_{Xᶜ}(c) ≤ 2 ‖c - P X c‖`. -/
theorem commNorm_compl_le (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X : Set Λ) (c : A) :
    commNorm 𝒜 Xᶜ c ≤ 2 * ‖c - Q.P X c‖ :=
  commNorm_le_two_mul_norm_sub hc disjoint_compl_right (Q.P_mem X c)

end LocalApprox

/-- M3, Definition 2.3: `T` is `ε`-local with neighbourhood map `nbhd` if every `x ∈ 𝒜 O` is
within `ε ‖x‖` of `𝒜 (nbhd O)`. -/
def IsApproxLocalWith (𝒜 : Net (Set Λ) A) (T : A → A) (nbhd : Set Λ → Set Λ) (ε : ℝ) : Prop :=
  ∀ O : Set Λ, ∀ x ∈ 𝒜 O, ∃ y ∈ 𝒜 (nbhd O), ‖T x - y‖ ≤ ε * ‖x‖

/-- At `ε = 0`, approximate locality is the locality condition of a quantum cellular
automaton: `T` maps `𝒜 O` into `𝒜 (nbhd O)`. -/
theorem isApproxLocalWith_zero_iff {𝒜 : Net (Set Λ) A} {T : A → A} {nbhd : Set Λ → Set Λ} :
    IsApproxLocalWith 𝒜 T nbhd 0 ↔ ∀ O : Set Λ, ∀ x ∈ 𝒜 O, T x ∈ 𝒜 (nbhd O) := by
  constructor
  · intro h O x hx
    obtain ⟨y, hy, hxy⟩ := h O x hx
    rw [zero_mul] at hxy
    have : T x = y := sub_eq_zero.mp (norm_le_zero_iff.mp hxy)
    rw [this]
    exact hy
  · intro h O x hx
    exact ⟨T x, h O x hx, by simp⟩

theorem IsApproxLocalWith.mono {𝒜 : Net (Set Λ) A} {T : A → A} {nbhd : Set Λ → Set Λ}
    {ε ε' : ℝ} (h : IsApproxLocalWith 𝒜 T nbhd ε) (hε : ε ≤ ε') :
    IsApproxLocalWith 𝒜 T nbhd ε' := fun O x hx =>
  let ⟨y, hy, hxy⟩ := h O x hx
  ⟨y, hy, hxy.trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _))⟩

end LocalityLean

end
