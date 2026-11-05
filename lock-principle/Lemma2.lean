import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
set_option linter.style.emptyLine false
set_option linter.style.cdot false

noncomputable section

namespace LockPrinciple

def hyperbolicRotate (θ u v : ℝ) : ℝ × ℝ :=
  (Real.cosh θ * u - Real.sinh θ * v,
   Real.cosh θ * v - Real.sinh θ * u)

def jumpVector
    (θ hMinus hPlus a ξ : ℝ) : ℝ × ℝ :=
  let y := hyperbolicRotate θ hMinus a
  (y.1 - hPlus, y.2 - ξ)

def InFutureCone (x : ℝ × ℝ) : Prop :=
  |x.2| ≤ x.1

lemma inFutureCone_iff (x : ℝ × ℝ) :
    InFutureCone x ↔
      0 ≤ x.1 + x.2 ∧ 0 ≤ x.1 - x.2 := by
  rw [InFutureCone, abs_le]
  constructor
  · rintro ⟨hLower, hUpper⟩
    constructor <;> linarith
  · rintro ⟨hAdd, hSub⟩
    constructor <;> linarith

lemma jumpVector_fst
    (θ hMinus hPlus a ξ : ℝ) :
    (jumpVector θ hMinus hPlus a ξ).1 =
      Real.cosh θ * hMinus -
        Real.sinh θ * a - hPlus := by
  rfl

lemma jumpVector_snd
    (θ hMinus hPlus a ξ : ℝ) :
    (jumpVector θ hMinus hPlus a ξ).2 =
      Real.cosh θ * a -
        Real.sinh θ * hMinus - ξ := by
  rfl

lemma product_identity
    {HMinus HPlus a ξ : ℝ}
    (hξ :
      ξ ^ 2 = HPlus ^ 2 - HMinus ^ 2 + a ^ 2) :
    (HPlus + ξ) * (HPlus - ξ) =
      (HMinus + a) * (HMinus - a) := by
  nlinarith

theorem lemma2
    {S : Type*}
    (hMinus hPlus : S → ℝ)
    (HMinus HPlus a : ℝ)
    (hHMinus : 0 < HMinus)
    (hHPlus : 0 < HPlus)
    (ha : 0 ≤ a)
    (hMinusBound : ∀ x, HMinus ≤ hMinus x)
    (hPlusBound : ∀ x, hPlus x ≤ HPlus)
    (hrad :
      0 ≤ HPlus ^ 2 - HMinus ^ 2 + a ^ 2) :
    let ξ :=
      Real.sqrt (HPlus ^ 2 - HMinus ^ 2 + a ^ 2)
    ∃ θ : ℝ, ∀ x : S,
      InFutureCone
        (jumpVector θ (hMinus x) (hPlus x) a ξ) := by
  dsimp only

  let r : ℝ :=
    HPlus ^ 2 - HMinus ^ 2 + a ^ 2

  let ξ : ℝ := Real.sqrt r

  have hr : 0 ≤ r := by
    simpa [r] using hrad

  have hξNonneg : 0 ≤ ξ := by
    exact Real.sqrt_nonneg r

  have hξSq : ξ ^ 2 = r := by
    simpa [ξ] using Real.sq_sqrt hr

  have hξFormula :
      ξ ^ 2 =
        HPlus ^ 2 - HMinus ^ 2 + a ^ 2 := by
    simpa [r] using hξSq

  have hdenPos : 0 < HMinus + a := by
    linarith

  have hdenNe : HMinus + a ≠ 0 :=
    ne_of_gt hdenPos

  have hnumPos : 0 < HPlus + ξ := by
    linarith

  have hnumNe : HPlus + ξ ≠ 0 :=
    ne_of_gt hnumPos

  let q : ℝ :=
    (HPlus + ξ) / (HMinus + a)

  have hqPos : 0 < q := by
    dsimp [q]
    exact div_pos hnumPos hdenPos

  have hqNonneg : 0 ≤ q :=
    hqPos.le

  let θ : ℝ := -Real.log q

  have hcoshTheta :
      Real.cosh θ = (q + q⁻¹) / 2 := by
    dsimp [θ]
    rw [Real.cosh_neg]
    exact Real.cosh_log hqPos

  have hsinhTheta :
      Real.sinh θ = -(q - q⁻¹) / 2 := by
    dsimp [θ]
    rw [Real.sinh_neg]
    rw [Real.sinh_log hqPos]
    ring

  have hproduct :
      (HPlus + ξ) * (HPlus - ξ) =
        (HMinus + a) * (HMinus - a) := by
    exact product_identity hξFormula

  have hqMulPlus :
      q * (HMinus + a) = HPlus + ξ := by
    dsimp [q]
    field_simp [hdenNe]

  have hqInvMulMinus :
      q⁻¹ * (HMinus - a) = HPlus - ξ := by
    dsimp [q]
    rw [inv_div]
    field_simp [hnumNe, hdenNe]
    nlinarith [hproduct]

  refine ⟨θ, ?_⟩
  intro x

  change
    InFutureCone
      (jumpVector θ (hMinus x) (hPlus x) a ξ)

  rw [inFutureCone_iff]
  constructor

  ·
    have hNullAdd :
        (jumpVector θ (hMinus x) (hPlus x) a ξ).1 +
            (jumpVector θ (hMinus x) (hPlus x) a ξ).2 =
          q * (hMinus x + a) - (hPlus x + ξ) := by
      rw [jumpVector_fst, jumpVector_snd]
      rw [hcoshTheta, hsinhTheta]
      ring

    rw [hNullAdd]

    have hInnerPlus :
        HMinus + a ≤ hMinus x + a := by
      linarith [hMinusBound x]

    have hScaledPlus :
        q * (HMinus + a) ≤
          q * (hMinus x + a) := by
      exact mul_le_mul_of_nonneg_left
        hInnerPlus hqNonneg

    rw [hqMulPlus] at hScaledPlus
    linarith [hPlusBound x]

  ·
    have hNullSub :
        (jumpVector θ (hMinus x) (hPlus x) a ξ).1 -
            (jumpVector θ (hMinus x) (hPlus x) a ξ).2 =
          q⁻¹ * (hMinus x - a) -
            (hPlus x - ξ) := by
      rw [jumpVector_fst, jumpVector_snd]
      rw [hcoshTheta, hsinhTheta]
      ring

    rw [hNullSub]

    have hInnerMinus :
        HMinus - a ≤ hMinus x - a := by
      linarith [hMinusBound x]

    have hqInvNonneg : 0 ≤ q⁻¹ := by
      exact inv_nonneg.mpr hqNonneg

    have hScaledMinus :
        q⁻¹ * (HMinus - a) ≤
          q⁻¹ * (hMinus x - a) := by
      exact mul_le_mul_of_nonneg_left
        hInnerMinus hqInvNonneg

    rw [hqInvMulMinus] at hScaledMinus
    linarith [hPlusBound x]

end LockPrinciple

end
