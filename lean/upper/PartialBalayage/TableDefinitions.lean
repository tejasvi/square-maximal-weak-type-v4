/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Independent concrete operators and exact table constants

All mathematical definitions used by the compared statements occupy one standalone
Mathlib-only module. The same transparent block is repeated in `Challenge.lean`.
This keeps generated volume-instance proof sharing identical across the environments.
No analytical certificate or solution theorem determines any operator or constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set FourierTransform
open scoped ENNReal

namespace PartialBalayage

/-- The centred maximal function over axis-parallel cubes of side `2r`. -/
def cubeMaximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ

/-- `C` bounds the weak type `(1,1)` inequality for every integrable real input over cubes. -/
def IsCubeWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : (Fin d → ℝ) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < cubeMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The least weak type `(1,1)` bound for the centred cube maximal operator. -/
def cubeWeakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsCubeWeakTypeBound d C}

/-- The centred maximal function over open Euclidean balls of radius `r`. -/
def ballMaximalFunction {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ

/-- `C` bounds the weak type `(1,1)` inequality for every integrable real input over balls. -/
def IsBallWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < ballMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The least weak type `(1,1)` bound for the centred Euclidean-ball maximal operator. -/
def ballWeakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsBallWeakTypeBound d C}

/-- The standard Poisson kernel on Euclidean `n`-space at height `t > 0`. -/
def poissonKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) *
    t / (t ^ 2 + ‖x‖ ^ 2) ^ (((n : ℝ) + 1) / 2)

/-- The standard heat kernel at time `t > 0`, with generator `Δ`. -/
def heatKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- The Poisson maximal function is the supremum over all positive heights of `p_t * |f|`. -/
def poissonMaximalFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), ∫⁻ y, ENNReal.ofReal (poissonKernel n t (x - y)) * ‖f y‖ₑ

/-- The heat maximal function is the supremum over all positive times of `h_t * |f|`. -/
def heatMaximalFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), ∫⁻ y, ENNReal.ofReal (heatKernel n t (x - y)) * ‖f y‖ₑ

/-- A weak type `(1,1)` bound for the Poisson maximal operator for all integrable real inputs. -/
def IsPoissonWeakTypeBound (n : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < poissonMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- A weak type `(1,1)` bound for the heat maximal operator for all integrable real inputs. -/
def IsHeatWeakTypeBound (n : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < heatMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The least weak type `(1,1)` bound for the Poisson maximal operator. -/
def poissonWeakTypeConstant (n : ℕ) : ℝ≥0∞ := sInf {C | IsPoissonWeakTypeBound n C}

/-- The least weak type `(1,1)` bound for the heat maximal operator. -/
def heatWeakTypeConstant (n : ℕ) : ℝ≥0∞ := sInf {C | IsHeatWeakTypeBound n C}

/-- The article's exact Poisson bound formula, before choosing its tangency parameters. -/
def poissonBoundFormula (n : ℕ) (a b : ℝ) : ℝ :=
  Real.Gamma (((n : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((n : ℝ) / 2)) *
    (2 * b ^ ((n : ℝ) / 2) / ((n : ℝ) * (1 + a) ^ (((n : ℝ) + 1) / 2)) +
      ∫ z in Set.Ioi b, z ^ ((n : ℝ) / 2 - 1) / (1 + z) ^ (((n : ℝ) + 1) / 2))

/-- The article's exact heat bound formula, before choosing its tangency parameters. -/
def heatBoundFormula (n : ℕ) (a b : ℝ) : ℝ :=
  (Real.Gamma ((n : ℝ) / 2))⁻¹ *
    (2 * b ^ ((n : ℝ) / 2) * Real.exp (-a) / (n : ℝ) +
      ∫ z in Set.Ioi b, z ^ ((n : ℝ) / 2 - 1) * Real.exp (-z))

/-- The one-dimensional Poisson row's exact constant, rather than its rounded approximation. -/
def poissonOneBound : ℝ :=
  1 + 2 / Real.pi * (Real.sqrt 5 / 3 - Real.arctan (2 / Real.sqrt 5))

namespace Constants

/-- The article's exact squared-radius joining ratio. -/
def rho (n : ℕ) : ℝ :=
  if n = 2 then Real.exp 1 else ((n : ℝ) / 2) ^ (2 / ((n : ℝ) - 2))

end Constants

open Constants

def IsHeatTangencyParameter (n : ℕ) (a : ℝ) : Prop :=
  a ∈ Ioo ((n : ℝ) / (2 * rho n)) ((n : ℝ) / 2) ∧
    Real.exp (-(rho n - 1) * a) = 1 - 2 * a / (n : ℝ)

def IsPoissonTangencyParameter (n : ℕ) (a : ℝ) : Prop :=
  a ∈ Ioo ((n : ℝ) / (3 * rho n)) ((n : ℝ) / 3) ∧
    (1 - a / (n : ℝ)) / (1 + a) ^ (((n : ℝ) + 3) / 2) =
      1 / (1 + rho n * a) ^ (((n : ℝ) + 1) / 2)

def heatTangencyParameter (n : ℕ) : ℝ := Classical.epsilon (IsHeatTangencyParameter n)

def poissonTangencyParameter (n : ℕ) : ℝ := Classical.epsilon (IsPoissonTangencyParameter n)

def complementaryErrorFunction (r : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ s in Set.Ioi r, Real.exp (-(s ^ 2))

end PartialBalayage

namespace PartialBalayage

section Fourier

variable {n : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The exact inverse Fourier transform of the actual symbol action on the Fourier input. -/
def canonicalL2FourierOperator
    (m : EuclideanSpace ℝ (Fin n) → E → F)
    (f : Lp E 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) F).symm
    (Classical.epsilon (fun g : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ↦
      ∀ᵐ ξ, g ξ = m ξ ((𝓕 f : Lp E 2 volume) ξ)))

end Fourier

/-- The full Euclidean vector Riesz symbol with its harmless zero-frequency value. -/
def fourierRieszSymbol {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  (Complex.I / (‖ξ‖ : ℂ)) • WithLp.toLp 2 (fun i ↦ (ξ i : ℂ))

/-- The full Riesz vector transform on real input, defined by its actual Fourier symbol. -/
def rieszFourierOperator {n : ℕ}
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z • fourierRieszSymbol ξ)
    (Complex.ofRealCLM.compLp f)

/-- The full complex-input Riesz vector, defined by its genuine Fourier symbol. -/
def complexRieszFourierOperator {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z • fourierRieszSymbol ξ) f

/-- The complex-input planar Beurling multiplier. -/
def beurlingFourierOperator
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) :=
  canonicalL2FourierOperator
    (fun ξ z ↦ (((ξ 0 : ℂ) - (ξ 1 : ℂ) * Complex.I) ^ 2 / (‖ξ‖ ^ 2 : ℂ)) * z) f

/-- The full second-order Riesz matrix symbol, with its genuine Frobenius norm. -/
def fourierHessianSymbol {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  ((-1 : ℂ) / (‖ξ‖ : ℂ) ^ (2 : ℕ)) •
    WithLp.toLp 2 (fun ij ↦ (ξ ij.1 : ℂ) * (ξ ij.2 : ℂ))

/-- The full Frobenius-matrix Hessian transform defined by its actual Fourier symbol. -/
def hessianFourierOperator {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z • fourierHessianSymbol ξ) f

/-- The traceless full Frobenius-matrix transform defined by its actual Fourier symbol. -/
def tracelessHessianFourierOperator {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z •
    (if ξ = 0 then 0 else fourierHessianSymbol ξ + ((n : ℂ)⁻¹) •
      WithLp.toLp 2 (fun ij : Fin n × Fin n ↦ if ij.1 = ij.2 then 1 else 0))) f

/-- The true gradient projection action on a complex Euclidean frequency vector. -/
def gradientFourierAction {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  ((‖ξ‖ ^ (2 : ℕ) : ℝ)⁻¹ : ℂ) •
    (inner ℂ (WithLp.toLp 2 (fun i ↦ (ξ i : ℂ))) z •
      WithLp.toLp 2 (fun i ↦ (ξ i : ℂ)))

/-- The actual gradient projection on vector fields, defined directly in Fourier space. -/
def gradientFourierOperator {n : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator gradientFourierAction f

/-- The actual Leray projection on vector fields, defined directly in Fourier space. -/
def lerayFourierOperator {n : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  canonicalL2FourierOperator (fun ξ z ↦ z - gradientFourierAction ξ z) f

section WeakConstants

variable {X E F 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A genuine linear all-L¹ extension, with exact L² agreement and every-level weak bound. -/
def IsLinearWeakTypeBound (T₂ : Lp E 2 μ → Lp F 2 μ) (C : ℝ≥0∞) : Prop :=
  ∃ T₁ : Lp E 1 μ →ₗ[𝕜] AEEqFun X F μ,
    (∀ (f₁ : Lp E 1 μ) (f₂ : Lp E 2 μ), (f₁ : X → E) =ᵐ[μ] f₂ →
      (T₁ f₁ : X → F) =ᵐ[μ] T₂ f₂) ∧
    ∀ (f₁ : Lp E 1 μ) (α : ℝ≥0∞),
      α * μ {x | α < ‖T₁ f₁ x‖ₑ} ≤ C * ∫⁻ x, ‖f₁ x‖ₑ ∂μ

/-- The true weak constant of the canonical all-L¹ extension of the specified L² operator. -/
def linearWeakTypeConstant (T₂ : Lp E 2 μ → Lp F 2 μ) : ℝ≥0∞ :=
  sInf {C | IsLinearWeakTypeBound (𝕜 := 𝕜) T₂ C}

end WeakConstants

end PartialBalayage

namespace PartialBalayage

/-- The exact positive stationary Hessian parameter in dimension `n`. -/
def hessianParameter (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) /
    ((n : ℝ) + 1 + Real.sqrt (((n : ℝ) + 1) ^ 2 + 4 * ((n : ℝ) - 2))))

/-- The full Frobenius Hessian coefficient before optimizing its cap. -/
def hessianCoefficient (n : ℕ) (a : ℝ) : ℝ :=
  1 / a + ((n : ℝ) - 1) * a / ((n : ℝ) - a ^ 2)

/-- The exact cubic defining the projection parameter. -/
def projectionCubic (a : ℝ) : ℝ := a ^ 3 - 2 * a ^ 2 + 6 * a - 4

/-- The unique cubic root in `(0,1)`, whose existence and uniqueness are proved separately. -/
def projectionParameter : ℝ :=
  Classical.epsilon (fun a : ℝ ↦ a ∈ Set.Ioo 0 1 ∧ projectionCubic a = 0)

/-- The exact projection coefficient before optimizing its cap. -/
def projectionCoefficient (a : ℝ) : ℝ := 1 / a + a / (2 - a) ^ 2

end PartialBalayage
