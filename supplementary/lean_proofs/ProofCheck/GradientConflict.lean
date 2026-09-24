/-
  Formal verification of Proposition 2 (Gradient Conflict)
  from "Bounded and Unbounded Latent Decoupling for Forecast
  and Reconstruction Quality"
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private lemma star_real (x : ℝ) : (starRingEnd ℝ) x = x :=
  star_trivial x

/-- Part (a): The combined gradient's alignment with g_r is strictly
less than ‖g_r‖². -/
theorem gradient_conflict_part_a
    (g_r g_f : V) (phi : ℝ)
    (hphi_pos : 0 < phi) (_hphi_lt : phi < 1)
    (h_conflict : ⟪g_f, g_r⟫_ℝ < 0)
    (_h_nonzero : g_r ≠ 0) :
    ⟪(1 - phi) • g_r + phi • g_f, g_r⟫_ℝ < ⟪g_r, g_r⟫_ℝ := by
  rw [inner_add_left, inner_smul_left, inner_smul_left, star_real, star_real]
  have h_norm_pos : (0 : ℝ) < ⟪g_r, g_r⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]; positivity
  have : (1 - phi) * ⟪g_r, g_r⟫_ℝ = ⟪g_r, g_r⟫_ℝ - phi * ⟪g_r, g_r⟫_ℝ := by ring
  linarith [mul_lt_mul_of_pos_left h_conflict hphi_pos, mul_pos hphi_pos h_norm_pos]

/-- Part (a), symmetric version for g_f. -/
theorem gradient_conflict_part_a_sym
    (g_r g_f : V) (phi : ℝ)
    (_hphi_pos : 0 < phi) (hphi_lt : phi < 1)
    (h_conflict : ⟪g_r, g_f⟫_ℝ < 0)
    (_h_nonzero : g_f ≠ 0) :
    ⟪(1 - phi) • g_r + phi • g_f, g_f⟫_ℝ < ⟪g_f, g_f⟫_ℝ := by
  rw [inner_add_left, inner_smul_left, inner_smul_left, star_real, star_real]
  have h_norm_pos : (0 : ℝ) < ⟪g_f, g_f⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]; positivity
  have h_one_minus_pos : 0 < 1 - phi := by linarith
  have : phi * ⟪g_f, g_f⟫_ℝ = ⟪g_f, g_f⟫_ℝ - (1 - phi) * ⟪g_f, g_f⟫_ℝ := by ring
  linarith [mul_lt_mul_of_pos_left h_conflict h_one_minus_pos,
            mul_pos h_one_minus_pos h_norm_pos]

/-- Part (b): The squared norm of the combined gradient is reduced
by the negative cross-term. -/
theorem gradient_conflict_part_b
    (g_r g_f : V) (phi : ℝ)
    (hphi_pos : 0 < phi) (hphi_lt : phi < 1)
    (h_conflict : ⟪g_r, g_f⟫_ℝ < 0) :
    ⟪(1 - phi) • g_r + phi • g_f, (1 - phi) • g_r + phi • g_f⟫_ℝ <
    (1 - phi) ^ 2 * ⟪g_r, g_r⟫_ℝ + phi ^ 2 * ⟪g_f, g_f⟫_ℝ := by
  have h_one_minus_pos : 0 < 1 - phi := by linarith
  have h_expand : ⟪(1 - phi) • g_r + phi • g_f, (1 - phi) • g_r + phi • g_f⟫_ℝ =
    (1 - phi) ^ 2 * ⟪g_r, g_r⟫_ℝ + 2 * (1 - phi) * phi * ⟪g_r, g_f⟫_ℝ +
    phi ^ 2 * ⟪g_f, g_f⟫_ℝ := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
               star_real, real_inner_comm g_f g_r]
    ring
  rw [h_expand]
  linarith [mul_neg_of_pos_of_neg (show (0:ℝ) < 2 * (1 - phi) * phi by positivity) h_conflict]

/-- Part (c): For sufficiently large phi, the combined gradient
actively hurts the reconstruction objective. -/
theorem gradient_conflict_part_c
    (g_r g_f : V) (phi : ℝ)
    (h_conflict : ⟪g_f, g_r⟫_ℝ < 0)
    (_h_nonzero : g_r ≠ 0)
    (hphi_gt : phi * (⟪g_r, g_r⟫_ℝ + |⟪g_f, g_r⟫_ℝ|) > ⟪g_r, g_r⟫_ℝ) :
    ⟪(1 - phi) • g_r + phi • g_f, g_r⟫_ℝ < 0 := by
  suffices h : (1 - phi) * ⟪g_r, g_r⟫_ℝ + phi * ⟪g_f, g_r⟫_ℝ < 0 by
    have h1 : ⟪(1 - phi) • g_r + phi • g_f, g_r⟫_ℝ =
      (1 - phi) * ⟪g_r, g_r⟫_ℝ + phi * ⟪g_f, g_r⟫_ℝ := by
      simp [inner_add_left, inner_smul_left]
    linarith
  have h_abs : |⟪g_f, g_r⟫_ℝ| = -⟪g_f, g_r⟫_ℝ := abs_of_neg h_conflict
  rw [h_abs] at hphi_gt
  nlinarith [mul_add phi ⟪g_r, g_r⟫_ℝ (-⟪g_f, g_r⟫_ℝ),
             mul_neg phi ⟪g_f, g_r⟫_ℝ]
