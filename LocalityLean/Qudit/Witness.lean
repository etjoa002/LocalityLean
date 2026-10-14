/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Qudit.SiteOp
import LocalityLean.Qudit.Bounds
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The two-qubit witness

The dynamics of a Hamiltonian family is not trivial: on two qubits with `H = σ^x_0 σ^x_1`,
`a = σ^z_0` and `b = σ^z_1`, the commutator `[a, b]` vanishes (causality) while
`[i[H, a], b] = -4i σ^y_0 σ^y_1 ≠ 0`, so the derivative of `t ↦ [A(t), b]` at `t = 0` is nonzero
and `[A(t), b] ≠ 0` for some `t > 0` (M2, Lemma 6.1 and Theorem 6.2). The derivative route
avoids computing the matrix exponential; the one concrete computation is the double commutator
of single-site operators (M2, Section 6).

## Main statements

* `LocalityLean.hasDerivAt_comm_evolve`, `LocalityLean.exists_pos_ne_zero_of_hasDerivAt`.
* `LocalityLean.Qudit.TwoQubit.comm_obsA_obsB`, `TwoQubit.comm_comm_ne_zero`,
  `TwoQubit.exists_comm_evolve_ne_zero`.
-/

noncomputable section

namespace LocalityLean

open NormedSpace LinearAQFT

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]

/-! ### The derivative of the commutator (M2, Lemma 6.1) -/

/-- The derivative of `t ↦ [e^{tL} a, b]` at `t = 0` is `[L a, b]`. -/
theorem hasDerivAt_comm_evolve {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A}
    (G : LocalGenerators ι 𝒜) (a b : A) :
    HasDerivAt (fun t : ℝ => comm (G.evolve t a) b) (comm (G.total a) b) 0 := by
  have h := hasDerivAt_exp_smul_const G.total (0 : ℝ)
  have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((ContinuousLinearMap.apply ℂ A a).restrictScalars ℝ).hasFDerivAt h
  have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((LocalGenerators.commRight b).restrictScalars ℝ).hasFDerivAt h1
  simpa [LocalGenerators.evolve, LocalGenerators.commRight_apply, Function.comp_def] using h2

/-- A function vanishing on `(0, ∞)` and at `0` has derivative `0` at `0`. -/
theorem eq_zero_of_hasDerivAt_of_eqOn {f : ℝ → A} {f' : A} (hf : HasDerivAt f f' 0)
    (h0 : f 0 = 0) (hpos : ∀ t, 0 < t → f t = 0) : f' = 0 := by
  have h1 : HasDerivWithinAt f f' (Set.Ioi 0) 0 := hf.hasDerivWithinAt
  have h2 : HasDerivWithinAt f 0 (Set.Ioi 0) 0 := by
    refine (hasDerivWithinAt_const (0 : ℝ) (Set.Ioi 0) (0 : A)).congr ?_ h0
    intro t ht; exact hpos t ht
  exact (uniqueDiffWithinAt_Ioi (0 : ℝ)).eq_deriv _ h1 h2

/-- M2, Lemma 6.1: a function with `f 0 = 0` and nonzero derivative at `0` is nonzero at some
`t > 0`. -/
theorem exists_pos_ne_zero_of_hasDerivAt {f : ℝ → A} {f' : A} (hf : HasDerivAt f f' 0)
    (h0 : f 0 = 0) (hne : f' ≠ 0) : ∃ t : ℝ, 0 < t ∧ f t ≠ 0 := by
  by_contra h
  exact hne (eq_zero_of_hasDerivAt_of_eqOn hf h0 fun t ht => by
    by_contra h'
    exact h ⟨t, ht, h'⟩)

/-! ### Two qubits (M2, Theorem 6.2) -/

namespace Qudit.TwoQubit

open scoped Matrix.Norms.L2Operator

/-- The two-qubit algebra. -/
abbrev Alg := QuditAlgebra (fun _ : Fin 2 => Fin 2)

/-- A two-qubit configuration. -/
abbrev Cfg := Config (fun _ : Fin 2 => Fin 2)

/-- `σ^x`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- `σ^z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `σ^x σ^z - σ^z σ^x = -2i σ^y`. -/
def pauliC : Matrix (Fin 2) (Fin 2) ℂ := pauliX * pauliZ - pauliZ * pauliX

theorem star_pauliX : star pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.star_apply]

theorem pauliC_apply_zero_one : pauliC 0 1 = -2 := by
  simp [pauliC, pauliX, pauliZ]
  norm_num

theorem zero_ne_one' : (0 : Fin 2) ≠ 1 := by decide

/-- The Hamiltonian `H = σ^x_0 σ^x_1`. -/
def ham : Alg := siteOp (0 : Fin 2) pauliX * siteOp (1 : Fin 2) pauliX

/-- The observable `a = σ^z_0`. -/
def obsA : Alg := siteOp (0 : Fin 2) pauliZ

/-- The probe `b = σ^z_1`. -/
def obsB : Alg := siteOp (1 : Fin 2) pauliZ

theorem ham_mem : ham ∈ localAlgebra ({0, 1} : Set (Fin 2)) :=
  mul_mem ((isLocal_siteOp 0 pauliX).mono (by simp)) ((isLocal_siteOp 1 pauliX).mono (by simp))

theorem ham_selfAdjoint : IsSelfAdjoint ham := by
  unfold ham
  rw [IsSelfAdjoint, star_mul, star_siteOp, star_siteOp, star_pauliX]
  exact (siteOp_commute_of_ne zero_ne_one' pauliX pauliX).eq.symm

/-- The two-qubit Hamiltonian family: one term with support `{0, 1}`. -/
def interaction : Interaction Unit (quditNet (fun _ : Fin 2 => Fin 2)) where
  supp _ := {0, 1}
  term _ := ham
  term_mem _ := by
    change ham ∈ localAlgebra ((({0, 1} : Finset (Fin 2)) : Set (Fin 2)))
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact ham_mem
  term_selfAdjoint _ := ham_selfAdjoint

/-- M2, Proposition 4.5: `σ^x` at site `1` is not local to `{0}`. -/
theorem siteOp_one_pauliX_not_mem :
    siteOp (1 : Fin 2) pauliX ∉ localAlgebra ({0} : Set (Fin 2)) := by
  intro h
  have h1 : ¬ AgreesOff ({0} : Set (Fin 2)) (![0, 0] : Cfg) (![0, 1] : Cfg) := by
    intro h1
    have := h1 1 (by simp)
    simp at this
  have := h.1 (![0, 0] : Cfg) (![0, 1] : Cfg) h1
  rw [siteOp_apply, ite_eq_left (by intro u hu; fin_cases u <;> simp_all)] at this
  simp [pauliX] at this

/-- M2, Proposition 4.5: `σ^x` and `σ^z` at the same site do not commute. -/
theorem siteOp_pauliX_pauliZ_not_commute :
    siteOp (0 : Fin 2) pauliX * siteOp (0 : Fin 2) pauliZ ≠
      siteOp (0 : Fin 2) pauliZ * siteOp (0 : Fin 2) pauliX := by
  intro h
  have h' : siteOp (0 : Fin 2) pauliC = 0 := by
    rw [pauliC, siteOp_sub, ← siteOp_mul_same, ← siteOp_mul_same, h, sub_self]
  have := congrFun (congrFun h' (![0, 0] : Cfg)) (![1, 0] : Cfg)
  rw [siteOp_apply, ite_eq_left (by intro u hu; fin_cases u <;> simp_all), Matrix.zero_apply]
    at this
  simp [pauliC_apply_zero_one] at this

/-- `[a, b] = 0` (causality). -/
theorem comm_obsA_obsB : comm obsA obsB = 0 :=
  comm_eq_zero_of_commute (siteOp_commute_of_ne zero_ne_one' _ _)

theorem comm_ham_obsA : comm ham obsA = siteOp (0 : Fin 2) pauliC * siteOp (1 : Fin 2) pauliX := by
  have c : siteOp (1 : Fin 2) pauliX * siteOp (0 : Fin 2) pauliZ =
      siteOp (0 : Fin 2) pauliZ * siteOp (1 : Fin 2) pauliX :=
    (siteOp_commute_of_ne zero_ne_one' _ _).eq.symm
  rw [comm_def, ham, obsA, mul_assoc, c, ← mul_assoc, ← mul_assoc, siteOp_mul_same,
    siteOp_mul_same, ← sub_mul, ← siteOp_sub]
  rfl

/-- `[i[H, a], b] = i σ^c_0 σ^c_1` with `σ^c = σ^x σ^z - σ^z σ^x`. -/
theorem comm_comm_eq :
    comm (Complex.I • comm ham obsA) obsB =
      Complex.I • (siteOp (0 : Fin 2) pauliC * siteOp (1 : Fin 2) pauliC) := by
  rw [comm_ham_obsA, comm_smul_left, obsB]
  congr 1
  have c : siteOp (1 : Fin 2) pauliZ * siteOp (0 : Fin 2) pauliC =
      siteOp (0 : Fin 2) pauliC * siteOp (1 : Fin 2) pauliZ :=
    (siteOp_commute_of_ne zero_ne_one' _ _).eq.symm
  rw [comm_def, mul_assoc, ← mul_assoc (siteOp 1 pauliZ), c, mul_assoc, siteOp_mul_same,
    siteOp_mul_same, ← mul_sub, ← siteOp_sub]
  rfl

theorem agreesOff_univ_two (s s' : Cfg) :
    AgreesOff (({0} : Set (Fin 2)) ∪ {1}) s s' := by
  intro u hu
  exact absurd (by fin_cases u <;> simp) hu

/-- M2, Theorem 6.2: the double commutator is nonzero. -/
theorem comm_comm_ne_zero : comm (Complex.I • comm ham obsA) obsB ≠ 0 := by
  rw [comm_comm_eq]
  intro h
  have := congrFun (congrFun h (![0, 0] : Cfg)) (![1, 1] : Cfg)
  rw [Matrix.smul_apply, siteOp_mul_apply_of_ne zero_ne_one' _ _ _ _ (agreesOff_univ_two _ _),
    Matrix.zero_apply] at this
  simp [pauliC_apply_zero_one] at this

/-- M2, Theorem 6.2: a nonzero commutator at some positive time. -/
theorem exists_comm_evolve_ne_zero :
    ∃ t : ℝ, 0 < t ∧ comm (interaction.toGenerators.evolve t obsA) obsB ≠ 0 := by
  refine exists_pos_ne_zero_of_hasDerivAt (hasDerivAt_comm_evolve _ obsA obsB) ?_ ?_
  · simp [LocalGenerators.evolve, comm_obsA_obsB]
  · rw [Interaction.toGenerators_total, Interaction.hamiltonian, Fintype.sum_unique,
      derivation_apply]
    exact comm_comm_ne_zero

end Qudit.TwoQubit

end LocalityLean

end
