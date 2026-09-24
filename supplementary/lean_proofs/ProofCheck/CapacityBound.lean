/-
  Formal verification of Proposition 1 (Capacity Bound)
  from "Bounded and Unbounded Latent Decoupling for Forecast
  and Reconstruction Quality"

  Core claim (n=2, k=1 case): Given diagonal Σ_x = diag(l₁, l₂)
  with l₁ > l₂ > 0, the reconstruction-optimal projection P* = e₁
  is not prediction-optimal when the dynamics matrix F has
  sufficiently large off-diagonal entries.

  Specifically, L_pred(e₁) > L_pred(e₂) when:
    l₁ F₂₁² + l₂ F₂₂² > l₁ F₁₁²

  This is the generic case when F Σ_x ≠ Σ_x F.
-/

import Mathlib.Tactic

/-- The prediction loss at P = e₁ (reconstruction-optimal). -/
noncomputable def L_pred_e1 (l₁ l₂ F₁₂ F₂₁ F₂₂ : ℝ) : ℝ :=
  l₁ * F₂₁ ^ 2 + l₂ * F₁₂ ^ 2 + l₂ * F₂₂ ^ 2

/-- The prediction loss at P = e₂. -/
noncomputable def L_pred_e2 (l₁ l₂ F₁₁ F₁₂ : ℝ) : ℝ :=
  l₁ * F₁₁ ^ 2 + l₂ * F₁₂ ^ 2

/-- Core lemma: the reconstruction-optimal projection e₁ has
strictly higher prediction loss than e₂ when the off-diagonal
coupling is large enough. -/
theorem capacity_bound_n2_k1
    (l₁ l₂ F₁₁ F₁₂ F₂₁ F₂₂ : ℝ)
    (_hl₁_pos : 0 < l₁)
    (_hl₂_pos : 0 < l₂)
    (_hl_order : l₂ < l₁)
    (h_coupling : l₁ * F₁₁ ^ 2 < l₁ * F₂₁ ^ 2 + l₂ * F₂₂ ^ 2) :
    L_pred_e2 l₁ l₂ F₁₁ F₁₂ < L_pred_e1 l₁ l₂ F₁₂ F₂₁ F₂₂ := by
  unfold L_pred_e1 L_pred_e2
  linarith

/-- The coupling condition l₁ F₂₁² + l₂ F₂₂² > l₁ F₁₁² is
generically satisfied. Here we show one concrete sufficient
condition: if |F₂₁| > |F₁₁| and F₂₂ ≠ 0. -/
theorem coupling_sufficient
    (l₁ l₂ F₁₁ F₂₁ F₂₂ : ℝ)
    (hl₁_pos : 0 < l₁)
    (hl₂_pos : 0 < l₂)
    (h_F21_gt : |F₂₁| > |F₁₁|)
    (h_F22_ne : F₂₂ ≠ 0) :
    l₁ * F₁₁ ^ 2 < l₁ * F₂₁ ^ 2 + l₂ * F₂₂ ^ 2 := by
  have h1 : F₁₁ ^ 2 < F₂₁ ^ 2 := by
    nlinarith [sq_abs F₁₁, sq_abs F₂₁, abs_nonneg F₁₁, abs_nonneg F₂₁,
               sq_nonneg (|F₂₁| - |F₁₁|)]
  have h2 : 0 < F₂₂ ^ 2 := by positivity
  nlinarith

/-- General case: replacing v_k with v_{k+1} in P increases
reconstruction loss by l_k - l_{k+1} > 0 (this is the penalty
for leaving the PCA basis). Formalised as a simple ordering lemma. -/
theorem reconstruction_penalty
    (l_k l_k1 : ℝ)
    (h_order : l_k1 < l_k) :
    0 < l_k - l_k1 := by
  linarith

/-- The measure-zero condition: the reconstruction and prediction
bases coincide only when F and Σ_x commute. For 2×2 diagonal Σ_x,
commutativity with F requires F₁₂ = 0 ∧ F₂₁ = 0 (F is also diagonal).
We show: if F and diag(l₁,l₂) commute (with l₁ ≠ l₂), then
F₁₂ = 0 and F₂₁ = 0. -/
theorem commute_implies_diagonal
    (l₁ l₂ F₁₂ F₂₁ : ℝ)
    (hl_ne : l₁ ≠ l₂)
    (h_comm_12 : l₁ * F₁₂ = F₁₂ * l₂)
    (h_comm_21 : l₂ * F₂₁ = F₂₁ * l₁) :
    F₁₂ = 0 ∧ F₂₁ = 0 := by
  constructor
  · by_contra h
    have h1 : l₁ * F₁₂ = l₂ * F₁₂ := by
      calc l₁ * F₁₂ = F₁₂ * l₂ := h_comm_12
        _ = l₂ * F₁₂ := mul_comm F₁₂ l₂
    exact hl_ne (mul_right_cancel₀ h h1)
  · by_contra h
    have h1 : l₂ * F₂₁ = l₁ * F₂₁ := by
      calc l₂ * F₂₁ = F₂₁ * l₁ := h_comm_21
        _ = l₁ * F₂₁ := mul_comm F₂₁ l₁
    exact hl_ne (mul_right_cancel₀ h h1).symm

/-
  Nonlinear extension (Corollary in the paper):

  For a nonlinear system x_{t+1} = f(x_t) + ε with Jacobian J(x) = ∇f(x),
  at each state x₀ the linear capacity bound applies with F := J(x₀).
  If J varies across the attractor, different states have different
  locally prediction-optimal projections, making a single global
  projection even more constrained.

  We formalise the core step: if the capacity bound holds for two
  different Jacobians J₁ and J₂ (at two different states), and
  they require different optimal projections, then no single
  projection can be locally optimal at both states.
-/

/-- If two dynamics matrices each make a different projection optimal,
no single projection is optimal for both. Formalised for the n=2,k=1
case: if J₁ makes e₁ suboptimal (e₂ better) and J₂ makes e₂
suboptimal (e₁ better), then neither e₁ nor e₂ is optimal everywhere. -/
theorem nonlinear_no_global_optimum
    (l₁ l₂ : ℝ)
    (J₁_₁₁ J₁_₁₂ J₁_₂₁ J₁_₂₂ : ℝ)
    (J₂_₁₁ J₂_₁₂ J₂_₂₁ J₂_₂₂ : ℝ)
    (hl₁_pos : 0 < l₁) (hl₂_pos : 0 < l₂) (hl_order : l₂ < l₁)
    (h_J1 : l₁ * J₁_₁₁ ^ 2 < l₁ * J₁_₂₁ ^ 2 + l₂ * J₁_₂₂ ^ 2)
    (h_J2 : l₁ * J₂_₂₁ ^ 2 + l₂ * J₂_₂₂ ^ 2 < l₁ * J₂_₁₁ ^ 2) :
    (L_pred_e2 l₁ l₂ J₁_₁₁ J₁_₁₂ < L_pred_e1 l₁ l₂ J₁_₁₂ J₁_₂₁ J₁_₂₂) ∧
    (L_pred_e1 l₁ l₂ J₂_₁₂ J₂_₂₁ J₂_₂₂ < L_pred_e2 l₁ l₂ J₂_₁₁ J₂_₁₂) := by
  constructor
  · exact capacity_bound_n2_k1 l₁ l₂ J₁_₁₁ J₁_₁₂ J₁_₂₁ J₁_₂₂ hl₁_pos hl₂_pos hl_order h_J1
  · unfold L_pred_e1 L_pred_e2; linarith
