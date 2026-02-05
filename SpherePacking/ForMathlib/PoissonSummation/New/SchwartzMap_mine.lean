/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Yongxi Lin

Reference: Loukas Grafakos, *Classical Fourier Analysis*
-/

import Mathlib

/-!
# Summability of mFourier coefficients of Schwartz Functions on ℝⁿ
-/

open Set Algebra Submodule MeasureTheory UnitAddTorus FourierTransform Asymptotics

open Asymptotics TopologicalSpace Real Filter ContinuousMap ZLattice Submodule

variable {d : Type*} [Fintype d] {f : EuclideanSpace ℝ d → ℂ}

#synth InnerProductSpace ℝ (EuclideanSpace ℝ d)

/- I am using EuclideanSpace ℝ d instead of d → ℝ because the first one has an instance of
InnerProductSpace. We need this instance for Real.fourierIntegral 𝓕.
-/

namespace RpowDecay

#check Function.Periodic.lift

def Periodicization (f : EuclideanSpace ℝ d → ℂ) : UnitAddTorus d → ℂ :=
  -- fun x ↦ Quotient.liftOn' x f
  by admit
  /- In the proof of the one dimensional case for the Poisson summation formula. They first use
  `f : ℝ → ℂ` to get a periodic function defined by `∑' (n : ℤ), f (x + n)`. They then use
  `Function.Periodic.lift` to get a function defined on the circle.

  Here's one approach to define the d dimensional periodicization. Just like the one dimensional
  case, we use `periodic_tsum_comp_add_zsmul` to get a periodic function defined by
  ∑' n : d → ℤ, f (x + n). We then use Function.Periodic.lift to get a function defined on
  (ℝ/ℤ)ᵈ. However, we are not done yet because in Mathlib, UnitAddTorus d is defined as (ℝ/ℤ)ᵈ.
  We need to use an isomorphism between ℝᵈ/ℤᵈ and (ℝ/ℤ)ᵈ to get a function in UnitAddTorus d → ℂ.
  -/

lemma Summable_mFourier_coeff {b : ℝ} (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b)))
    (h_sum : Summable fun n : d → ℤ => 𝓕 f fun i => n i) :
    Summable (mFourierCoeff (Periodicization f)) := by
  -- Use `tendstoUniformly_tsum_nat` but somehow generalise statement by replacing ℕ with countable
  admit

/- For each (n : d → ℤ) 𝓕 f (fun i => n i)) = mFourierCoeff (Periodicization f) n. -/
lemma mFourierCoeff_Periodicization_eq_FourierTransform {b : ℝ} (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b))) (n : d → ℤ) :
    𝓕 f (fun i => n i) = mFourierCoeff (Periodicization f) n := by admit

/- Periodicization is continuous. -/
lemma cont_Periodicization {b : ℝ} (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b))) (n : d → ℤ) :
    Continuous (Periodicization f) := by admit
/- We assume f decays very fast so that ∑' n : d → ℤ, f (x + n) is dominated by a convergent
  series. We can then deduce that ∑' n : d → ℤ, f (x + n) converges uniformly by the Weierstrass M-
  test. ∑' n : d → ℤ, f (x + n) is thus continuous as the uniform limit of continuous functions.
  -/

/-- **Poisson summation formula** for continuous functions with fast decay and and its Fourier
transform is summable. -/
theorem tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay_of_summable {b : ℝ}
    (hc : Continuous f) (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b)))
    (h_sum : Summable fun n : d → ℤ => 𝓕 f fun i => n i)
    (x : EuclideanSpace ℝ d) :
    ∑' n : d → ℤ, f (fun i => (n i + x i : ℝ)) =
    ∑' n : d → ℤ, 𝓕 f (fun i => n i) • mFourier n (fun i => x i) := by
  admit

noncomputable def euclideanNorm : (d → ℝ) → ℝ :=
  fun v ↦ @Norm.norm (EuclideanSpace ℝ d) _ v

def toReal : ℤ → ℝ := fun x ↦ x /- Is this defined somewhere? -/

@[simp]
lemma toReal_def {x : ℤ} : toReal x = x := rfl

lemma toReal_injective : Function.Injective toReal :=
    Isometry.injective fun _ ↦ congrFun rfl

@[simp]
lemma euclideanNorm_def {v : d → ℝ} :
    euclideanNorm v = @Norm.norm (EuclideanSpace ℝ d) _ v :=
  rfl

lemma supNorm_le_euclideanNorm {v : d → ℝ} : ‖v‖ ≤ euclideanNorm v := by
  calc
    ‖v‖ = Finset.univ.sup fun i ↦ ‖v i‖₊ := by rw[Pi.norm_def]
    _ ≤ NNReal.sqrt (∑ i, ‖v i‖₊ ^ 2) := by
      norm_cast
      rw[Finset.sup_le_iff]
      intro k _
      rw[NNReal.le_sqrt_iff_sq_le]
      calc
        ‖v k‖₊ ^ 2 = ∑ i ∈ {k}, ‖v i‖₊ ^ 2 := by rw[Finset.sum_singleton]
        _ ≤ ∑ i, ‖v i‖₊ ^ 2 := by
          refine Finset.sum_le_univ_sum_of_nonneg ?_
          intro i
          exact sq_nonneg _
    _ = euclideanNorm v := by
      rw[euclideanNorm_def, PiLp.norm_eq_of_L2]
      norm_cast
      simp

lemma euclideanNorm_le_sqrt_d_mul_supNorm {v : d → ℝ} : euclideanNorm v ≤ Fintype.card d * ‖v‖ := by
  calc
    euclideanNorm v = Real.sqrt (∑ i, (‖v i‖) ^ 2) := by
      rw[euclideanNorm_def, PiLp.norm_eq_of_L2]
    _ ≤ Real.sqrt (∑ i, (‖v‖) ^ 2) := by
      apply sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      rw[sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
      exact Finset.le_sup (α := NNReal) (f := fun b ↦ ‖v b‖₊) (Finset.mem_univ i)
    _ = Real.sqrt (Fintype.card d * ‖v‖ ^ 2) := by
      congr
      rw[Fintype.card_eq_sum_ones]
      sorry /-continue-/
    _ = Real.sqrt (Fintype.card d) * ‖v‖ := by
      rw[sqrt_mul (Nat.cast_nonneg _), sqrt_sq (norm_nonneg _)]
  sorry

/-- d-dimensional analogue of the absolute convergence of p-series
  (∞-norm version) -/
lemma summable_norm_rpow_iff {p : ℝ} (hd : Fintype.card d > 0) :
    Summable (fun (v : d → ℤ) ↦ ‖toReal ∘ v‖ ^ (-p)) ↔
    p > Fintype.card d := by
  sorry

/-- d-dimensional analogue of the absolute convergence of p-series
  (Euclidean norm version) -/
lemma summable_abs_int_rpow_iff {p : ℝ} (hd : Fintype.card d > 0) :
    Summable (fun (v : d → ℤ) ↦ (euclideanNorm (toReal ∘ v)) ^ (-p)) ↔
    p > Fintype.card d := by
  rw[← summable_norm_rpow_iff]
  constructor
  · intro hd
    refine summable_of_isBigO hd ?_
    if hp : p < 0 then
      apply IsBigO.rpow
      · linarith
      · apply Filter.univ_mem'
        simp
      · apply isBigO_of_le
        simp
        exact (fun v ↦ supNorm_le_euclideanNorm)
     else
      sorry /- Resume here -/

lemma summable_abs_int_rpow {p : ℝ} (hp : Fintype.card d < p) :
    Summable (fun (v : d → ℤ) ↦ euclideanNorm (toReal ∘ v) ^ (-p)) := by
  sorry

example {a b : NNReal} (hab : (a : ℝ) ≤ (b : ℝ)) : a ≤ b := by
  exact hab

/-- The inclusion from ℤᵈ to ℝᵈ maps the filter of cofinite sets to the filter of cocompact sets.
This is the d-dimensional analogue of `Int.tendsto_coe_cofinite`. -/
lemma IntLattice.tendsto_coe_cofinite :
    Filter.Tendsto (fun n : d → ℤ => fun i => (n i : ℝ))
    Filter.cofinite (Filter.cocompact (EuclideanSpace ℝ d)) := by sorry

/-- **Poisson summation formula**, assuming that both `f` and its Fourier transform decay fast. -/
theorem tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay {b : ℝ}
    (hc : Continuous f) (hb : Fintype.card d < b)
    (hf : f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b)))
    (hFf : 𝓕 f =O[cocompact (EuclideanSpace ℝ d)] (‖·‖ ^ (-b))) (x : EuclideanSpace ℝ d) :
    ∑' n : d → ℤ, f (fun i => n i + x i) =
    ∑' n : d → ℤ, 𝓕 f (fun i => n i) * mFourier n (fun i => x i) := by
  refine tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay_of_summable hc hb hf
    (summable_of_isBigO (summable_abs_int_rpow hb) ?_) x
  suffices h : (𝓕 f ∘ fun n : d → ℤ => fun i => n i) =O[cofinite]
    ((fun x ↦ @Norm.norm (EuclideanSpace ℝ d) (PiLp.instNorm 2 fun x ↦ ℝ) x ^ (-b)) ∘ fun n : d → ℤ
    => fun i => n i) from by
    exact h
  exact hFf.comp_tendsto IntLattice.tendsto_coe_cofinite

end RpowDecay

namespace SchwartzMap

/-- **Poisson summation formula** for Schwartz maps. -/
theorem tsum_mFourier_coeff_eq_tsum_fourierIntegral (f : 𝓢(EuclideanSpace ℝ d, ℂ))
    (x : EuclideanSpace ℝ d) :
    ∑' n : d → ℤ, f (fun i => n i + x i) =
    ∑' n : d → ℤ, 𝓕 f (fun i => n i) * mFourier n (fun i => x i) :=
  RpowDecay.tsum_mFourier_coeff_eq_tsum_fourierIntegralof_rpow_decay f.continuous
    (by simp : (Fintype.card d : ℝ) < Fintype.card d + 1)
    (f.isBigO_cocompact_rpow (-(Fintype.card d + 1)))
    ((fourierTransformCLM ℝ f).isBigO_cocompact_rpow (-(Fintype.card d + 1))) x

variable (Λ : Submodule ℤ (EuclideanSpace ℝ d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- This is the analogue of `UnitAddTorus.mFourier` for a general ZLattice. There should
exsts a scaling factor related to the volume of the fundamental area of this ZLattice, but I
didn't include it yet as I am not sure how to define it. -/
def _root_.ZLattice.mFourier (n : Λ) : C(UnitAddTorus d, ℂ) where
  toFun x := by admit
  continuous_toFun := by admit

/-- **Poisson summation formula** for a general lattice. We need to use
`integral_image_eq_integral_abs_det_fderiv_smul`. -/
theorem _root_.ZLattice.tsum_mFourier_coeff_eq_tsum_fourierIntegral (f : 𝓢(EuclideanSpace ℝ d, ℂ))
  (x : EuclideanSpace ℝ d) :
  ∑' n : Λ, f (fun i => n.val i + x i) =
  ∑' n : Λ, 𝓕 f (fun i => n.val i) * ZLattice.mFourier Λ n (fun i => x i) := by admit

end SchwartzMap

#min_imports
