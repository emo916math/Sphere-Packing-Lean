/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

This file is more of a scratch file for asymptotics. If there is anything here that is not in
Mathlib, which should not be the case, then we can PR it.
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Asymptotics Filter

variable {α E E' F' : Type*}
variable [LinearOrder α] -- [Nonempty α]
variable [NormedDivisionRing E]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
variable {f' : α → E'} {g' : α → F'}
variable {l : Filter α}

-- Wonder why exact? didn't work...
theorem mul_isBigO_mul {f g F G : α → E} (hf : f =O[atTop] F) (hg : g =O[atTop] G) :
    (f * g) =O[atTop] (F * G) := IsBigO.mul hf hg
-- by
-- simp [isBigO_iff] at hf hg ⊢
-- obtain ⟨cf, af, hf⟩ := hf
-- obtain ⟨cg, ag, hg⟩ := hg
-- use cf * cg, max af ag
-- intro n hn
-- specialize hf n (le_of_max_le_left hn)
-- specialize hg n (le_of_max_le_right hn)
-- calc ‖f n‖ * ‖g n‖
-- _ ≤ cf * ‖F n‖ * ‖g n‖ := by gcongr
-- _ ≤ cf * ‖F n‖ * (cg * ‖G n‖) := by
-- gcongr
-- exact Preorder.le_trans 0 ‖f n‖ (cf * ‖F n‖) (norm_nonneg _) hf
-- _ = cf * cg * (‖F n‖ * ‖G n‖) := by ring

example {f g F G : α → ℝ} (hf : f =O[atTop] F) (hg : g =O[atTop] G) :
    (f * g) =O[atTop] (F * G) := mul_isBigO_mul hf hg

example {f g F G : ℤ → ℝ} (hf : f =O[atTop] F) (hg : g =O[atTop] G) :
    (f * g) =O[atTop] (F * G) := mul_isBigO_mul hf hg

-- variable [Nonempty α]

theorem isBigO_pow {f F : α → E} {n : ℕ} (hf : f =O[atTop] F) :
    (fun x => (f x) ^ n) =O[atTop] (fun x => (F x) ^ n) := by
  exact IsBigO.pow hf n
  -- induction' n with n hn
  -- · simp only [pow_zero]
  -- exact (isBigO_const_const_iff atTop).mpr fun a ↦ a
  -- · simp only [pow_succ]
  -- exact IsBigO.mul hn hf

/-
A variant of IsTheta.rpow that does not require the exponent to be nonnegative, and in which
the conclusion is a Theta relation between norms.
-/
theorem IsTheta.rpow' (h : f' =Θ[l] g') (c : ℝ) :
    (fun x ↦ ‖f' x‖ ^ c) =Θ[l] fun x ↦ ‖g' x‖ ^ c := by
  wlog hc : c ≥ 0
  · rw[← isTheta_inv]
    have : (fun x ↦ ‖f' x‖ ^ (-c)) =Θ[l] fun x ↦ (‖g' x‖ ^ (-c)) := this h (-c) (by linarith)
    convert this using 2 <;> exact (Real.rpow_neg (norm_nonneg _) _).symm
  refine IsTheta.rpow hc ?_ ?_ (by rwa[isTheta_norm_left, isTheta_norm_right]) <;>
    exact Filter.Eventually.of_forall fun x ↦ norm_nonneg _
