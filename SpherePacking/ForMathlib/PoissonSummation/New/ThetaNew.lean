import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/- Additions to Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean for Mathlib -/

open Filter

open Topology

namespace Asymptotics

/- The following variables are among those in
Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean -/
variable {α E' F' : Type*}
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
variable {f' : α → E'} {g' : α → F'}
variable {l : Filter α}

theorem IsTheta.rpow' (h : f' =Θ[l] g') (c : ℝ) :
    (fun x ↦ ‖f' x‖ ^ c) =Θ[l] fun x ↦ ‖g' x‖ ^ c := by
  wlog hc : c ≥ 0
  · rw[← isTheta_inv]
    have : (fun x ↦ ‖f' x‖ ^ (-c)) =Θ[l] fun x ↦ (‖g' x‖ ^ (-c)) := this h (-c) (by linarith)
    convert this using 2 <;> exact (Real.rpow_neg (norm_nonneg _) _).symm
  refine IsTheta.rpow hc ?_ ?_ (by rwa[isTheta_norm_left, isTheta_norm_right]) <;>
    exact Filter.Eventually.of_forall fun x ↦ norm_nonneg _

#check IsTheta.rpow
#check IsTheta.rpow'

end Asymptotics
