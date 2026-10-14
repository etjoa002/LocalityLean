/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Qudit.Config
import LocalityLean.Core.Derivation
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The published bounds for qudit interactions

A qudit interaction is a finite family of Hermitian matrices on the letters of finite supports
(M2, Definition 2.4); its terms are the embedded matrices, self-adjoint and local, so the
interaction is a Hamiltonian family on the qudit net (M2, Proposition 5.1) and the closed forms
of M1b apply with `κ_i = ‖Φ_i‖` (M2, Theorem 5.2). The `F`-norm of Nachtergaele-Sims-Young 2019,
eq. (3.14), is the smallest `F`-bound on a finite site set (M2, Proposition 5.3), and the
exponential weighting of a decay kernel keeps its reproducing constant (M2, Proposition 5.4).

## Main definitions

* `LocalityLean.Qudit.QuditInteraction`, `QuditInteraction.toInteraction`.
* `LocalityLean.LocalGenerators.fNorm`, `LocalityLean.DecayKernel.expWeight`.

## Main statements

* `QuditInteraction.liebRobinson_walk`, `liebRobinson_matrixExp`, `liebRobinson_decay`,
  `liebRobinson_boundedGeometry`, `liebRobinson_cone`.
* `LocalGenerators.isFBound_fNorm`, `LocalGenerators.fNorm_le_of_isFBound`.
-/

noncomputable section

namespace LocalityLean

open LinearAQFT

/-! ### The `F`-norm (M2, Proposition 5.3) -/

namespace LocalGenerators

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

variable [Fintype Λ] [Nonempty Λ]

/-- The `F`-norm `‖Φ‖_F = max_{x,y} h_{xy} / F(x,y)` on a finite nonempty site set
(Nachtergaele-Sims-Young 2019, eq. (3.14)). -/
def fNorm (F : Λ → Λ → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun p : Λ × Λ => G.siteMatrix p.1 p.2 / F p.1 p.2

theorem div_le_fNorm (F : Λ → Λ → ℝ) (x y : Λ) : G.siteMatrix x y / F x y ≤ G.fNorm F :=
  Finset.le_sup' (fun p : Λ × Λ => G.siteMatrix p.1 p.2 / F p.1 p.2) (Finset.mem_univ (x, y))

/-- M2, Proposition 5.3: the `F`-norm is an `F`-bound when `F > 0`. -/
theorem isFBound_fNorm (K : DecayKernel Λ) (hF : ∀ x y, 0 < K.F x y) :
    G.IsFBound K (G.fNorm K.F) := by
  refine ⟨?_, fun x y => ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty Λ›
    exact (div_nonneg (G.siteMatrix_nonneg x x) (hF x x).le).trans (G.div_le_fNorm K.F x x)
  · exact (div_le_iff₀ (hF x y)).mp (G.div_le_fNorm K.F x y)

/-- M2, Proposition 5.3: every `F`-bound dominates the `F`-norm when `F > 0`. -/
theorem fNorm_le_of_isFBound (K : DecayKernel Λ) (hF : ∀ x y, 0 < K.F x y) {N : ℝ}
    (hN : G.IsFBound K N) : G.fNorm K.F ≤ N := by
  refine Finset.sup'_le _ _ fun p _ => ?_
  exact (div_le_iff₀ (hF p.1 p.2)).mpr (hN.2 p.1 p.2)

end LocalGenerators

/-! ### Exponential weighting (M2, Proposition 5.4) -/

namespace DecayKernel

variable {Λ : Type*}

/-- M2, Proposition 5.4: `e^{-μ d(x,y)} F(x,y)` is a decay kernel with the same constant when
`d` satisfies the triangle inequality and `μ ≥ 0` (Nachtergaele-Sims-Young 2019, eq. (3.11)). -/
def expWeight (K : DecayKernel Λ) (d : Λ → Λ → ℝ) (hd : ∀ x y z, d x y ≤ d x z + d z y)
    {μ : ℝ} (hμ : 0 ≤ μ) : DecayKernel Λ where
  F x y := Real.exp (-μ * d x y) * K.F x y
  CF := K.CF
  CF_pos := K.CF_pos
  F_nonneg x y := mul_nonneg (Real.exp_pos _).le (K.F_nonneg x y)
  reproducing x y T' := by
    calc ∑ z ∈ T', Real.exp (-μ * d x z) * K.F x z * (Real.exp (-μ * d z y) * K.F z y)
        ≤ ∑ z ∈ T', Real.exp (-μ * d x y) * (K.F x z * K.F z y) := by
          refine Finset.sum_le_sum fun z _ => ?_
          have h1 : Real.exp (-μ * d x z) * Real.exp (-μ * d z y) ≤ Real.exp (-μ * d x y) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            nlinarith [hd x y z]
          have h2 : 0 ≤ K.F x z * K.F z y := mul_nonneg (K.F_nonneg x z) (K.F_nonneg z y)
          calc Real.exp (-μ * d x z) * K.F x z * (Real.exp (-μ * d z y) * K.F z y)
              = (Real.exp (-μ * d x z) * Real.exp (-μ * d z y)) * (K.F x z * K.F z y) := by ring
            _ ≤ Real.exp (-μ * d x y) * (K.F x z * K.F z y) :=
              mul_le_mul_of_nonneg_right h1 h2
      _ = Real.exp (-μ * d x y) * ∑ z ∈ T', K.F x z * K.F z y := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-μ * d x y) * (K.CF * K.F x y) :=
          mul_le_mul_of_nonneg_left (K.reproducing x y T') (Real.exp_pos _).le
      _ = K.CF * (Real.exp (-μ * d x y) * K.F x y) := by ring

theorem expWeight_F (K : DecayKernel Λ) (d : Λ → Λ → ℝ) (hd : ∀ x y z, d x y ≤ d x z + d z y)
    {μ : ℝ} (hμ : 0 ≤ μ) (x y : Λ) :
    (K.expWeight d hd hμ).F x y = Real.exp (-μ * d x y) * K.F x y := rfl

theorem expWeight_CF (K : DecayKernel Λ) (d : Λ → Λ → ℝ) (hd : ∀ x y z, d x y ≤ d x z + d z y)
    {μ : ℝ} (hμ : 0 ≤ μ) : (K.expWeight d hd hμ).CF = K.CF := rfl

end DecayKernel

/-! ### Qudit interactions (M2, Proposition 5.1 and Theorem 5.2) -/

namespace Qudit

variable {Λ : Type*} {σ : Λ → Type*}

theorem star_embed (X : Set Λ) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    star (embed X m) = embed X (star m) := by
  ext s s'
  rw [Matrix.star_apply, embed_apply, embed_apply]
  by_cases h : AgreesOff X s s'
  · simp [h, h.symm, Matrix.star_apply]
  · have h' : ¬ AgreesOff X s' s := fun h' => h h'.symm
    simp [h, h']

theorem isSelfAdjoint_embed (X : Set Λ) {m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ}
    (hm : Matrix.IsHermitian m) : IsSelfAdjoint (embed X m) := by
  rw [IsSelfAdjoint, star_embed, Matrix.star_eq_conjTranspose, hm.eq]

variable [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)]
  [∀ u, Nonempty (σ u)]

open scoped Matrix.Norms.L2Operator

/-- M2, Definition 2.4: a qudit interaction, Hermitian matrices on the letters of finite
supports. -/
structure QuditInteraction (ι : Type*) [Fintype ι] (σ : Λ → Type*) where
  /-- The support of the `i`-th term. -/
  supp : ι → Finset Λ
  /-- The matrix of the `i`-th term on the letters of its support. -/
  mat : ∀ i, Matrix ((x : (↑(supp i) : Set Λ)) → σ x) ((x : (↑(supp i) : Set Λ)) → σ x) ℂ
  mat_isHermitian : ∀ i, Matrix.IsHermitian (mat i)

namespace QuditInteraction

variable {ι : Type*} [Fintype ι] (Φ : QuditInteraction ι σ)

/-- The `i`-th term `Φ_i = embed_{S_i} m_i`. -/
def term (i : ι) : QuditAlgebra σ := embed (↑(Φ.supp i)) (Φ.mat i)

/-- M2, Proposition 5.1: a qudit interaction is a Hamiltonian family on the qudit net. -/
def toInteraction : Interaction ι (quditNet σ) where
  supp := Φ.supp
  term := Φ.term
  term_mem _ := embed_mem _ _
  term_selfAdjoint i := isSelfAdjoint_embed _ (Φ.mat_isHermitian i)

/-- The local generators of a qudit interaction, with `κ_i = ‖Φ_i‖`. -/
def toGenerators : LocalGenerators ι (quditNet σ) := Φ.toInteraction.toGenerators

@[simp] theorem toGenerators_kappa (i : ι) : Φ.toGenerators.kappa i = ‖Φ.term i‖ := rfl

@[simp] theorem toGenerators_supp : Φ.toGenerators.supp = Φ.supp := rfl

theorem toGenerators_negContractive : Φ.toGenerators.NegContractive :=
  Φ.toInteraction.toGenerators_negContractive

/-- The dynamics `A(t) = U_t a U_t^*`. -/
theorem evolve_eq_conj (t : ℝ) (a : QuditAlgebra σ) :
    Φ.toGenerators.evolve t a =
      Φ.toInteraction.unitaryAt t * a * star (Φ.toInteraction.unitaryAt t) :=
  Φ.toInteraction.evolve_eq_conj t a

open Classical in
/-- M2, Theorem 5.2 (i), the walk form for every real `t`. -/
theorem liebRobinson_walk (X Y : Set Λ) {a b : QuditAlgebra σ} (ha : a ∈ localAlgebra X)
    (hb : b ∈ localAlgebra Y) (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        min (∑' k, Φ.toGenerators.walkTerm X Y |t| k)
          (∑' k, Φ.toGenerators.walkTerm Y X |t| k)) :=
  Φ.toInteraction.liebRobinson_walk_min quditNet_isCausal X Y ha hb t

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- M2, Theorem 5.2 (i), the matrix exponential for every real `t`: the walk series is
`Σ_{y ∈ ∂Y, x ∈ X ∩ T} (e^{2|t|h} - 1)_{yx}` (the review's eq. (3.36), sharpened). The general
statement is `LocalGenerators.liebRobinson_matrixExp_abs` (`Core/Derivation.lean`); the
exponential of the site matrix is that of the topological ring `Matrix Λ Λ ℝ`, stated here
without opening the scoped `ℓ∞`-operator norm, which on the qudit algebra (itself a matrix
type) would compete with the C*-norm. -/
theorem liebRobinson_matrixExp (X Y : Set Λ) {a b : QuditAlgebra σ} (ha : a ∈ localAlgebra X)
    (hb : b ∈ localAlgebra Y) (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        ∑ y ∈ Φ.toGenerators.boundary Y, ∑ x ∈ Φ.toGenerators.regionSites X,
          (NormedSpace.exp ((2 * |t|) • Φ.toGenerators.toMatrix) y x - (1 : Matrix Λ Λ ℝ) y x)) :=
  Φ.toGenerators.liebRobinson_matrixExp_abs quditNet_isCausal Φ.toGenerators_negContractive X Y
    ha hb t

open Classical in
/-- M2, Theorem 5.2 (ii), the decay form for every real `t` with the smaller kernel sum
(Nachtergaele-Sims-Young 2019, eqs. (3.23)-(3.24)). -/
theorem liebRobinson_decay (K : DecayKernel Λ) {N : ℝ} (hN : Φ.toGenerators.IsFBound K N)
    (X Y : Set Λ) {a b : QuditAlgebra σ} (ha : a ∈ localAlgebra X) (hb : b ∈ localAlgebra Y)
    (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Real.exp (2 * N * K.CF * |t|) - 1) / K.CF *
          min (Φ.toGenerators.kernelSum K X Y) (Φ.toGenerators.kernelSum K Y X)) :=
  Φ.toInteraction.liebRobinson_decay_min quditNet_isCausal K hN X Y ha hb t

open Classical in
/-- M2, Theorem 5.2 (iii), bounded geometry (the review's Proposition 3.5 with our constants). -/
theorem liebRobinson_boundedGeometry (B : Φ.toGenerators.BoundedGeometry) (X Y : Set Λ) {r : ℕ}
    (hr : 1 ≤ r)
    (hd : ∀ y ∈ Φ.toGenerators.boundary Y, ∀ x ∈ Φ.toGenerators.regionSites X,
      ((r : ℝ) - 1) * B.rho < B.d y x)
    {a b : QuditAlgebra σ} (ha : a ∈ localAlgebra X) (hb : b ∈ localAlgebra Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Φ.toGenerators.boundary Y).card *
          ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) :=
  Φ.toGenerators.liebRobinson_boundedGeometry quditNet_isCausal B X Y hr hd ha hb ht

open Classical in
/-- M2, Theorem 5.2 (iv), the exponential light cone (the review's Example 3.6). -/
theorem liebRobinson_cone (B : Φ.toGenerators.BoundedGeometry) (X Y : Set Λ) {r : ℕ}
    (hr : 1 ≤ r)
    (hd : ∀ y ∈ Φ.toGenerators.boundary Y, ∀ x ∈ Φ.toGenerators.regionSites X,
      ((r : ℝ) - 1) * B.rho < B.d y x)
    (μ : ℝ) {a b : QuditAlgebra σ} (ha : a ∈ localAlgebra X) (hb : b ∈ localAlgebra Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Φ.toGenerators.boundary Y).card * (Real.exp (B.v * t) *
          (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  Φ.toGenerators.liebRobinson_cone quditNet_isCausal B X Y hr hd μ ha hb ht

end QuditInteraction

end Qudit

end LocalityLean

end
