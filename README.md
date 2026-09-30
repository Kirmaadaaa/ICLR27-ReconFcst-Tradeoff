# NOTE: This is an anonymous github account. Not containing any personal information about the authors of the submitted manuscript and can in no way be traced in such a way that breaks double blind reviews.

# Reproducibility Code for "The Forecast-Reconstruction Tradeoff Is an Artifact of Coupling a Single Latent to Both Objectives"

## Structure

```
code/
  Experimentation/     Experiment scripts (one per table/figure)
  Utils/               Shared utilities (seeding, training loops)
  Paper/               Figure generation from JSON results
paper/                 LaTeX source and figures
supplementary/
  lean_proofs/         Lean 4 formal verification of Propositions 1 and 2
```

## Requirements

```
pip install -r requirements.txt
```

Python >= 3.10, PyTorch >= 2.0, NumPy, SciPy, Matplotlib, tqdm.

## Reproducing Paper Results

Each script is self-contained and generates a JSON file in `code/Paper/`.
Run from the repository root or from `code/Experimentation/`.

| Paper Element | Script | Output |
|---|---|---|
| Table 1 (Head comparison) | `run_param_matched.py` | `param_matched.json` |
| Table 2 (KS-64D) | `run_param_matched_all.py` | `param_matched_all.json` |
| Table 3 (Ablation) | `run_param_matched_all.py` | `param_matched_all.json` |
| Table 4 (MTL methods) | `run_mtl_baselines.py` | `mtl_baselines.json` |
| Table 5 (mLaSDI) | `run_param_matched_all.py` | `param_matched_all.json` |
| Table 6 (Koopa) | `run_param_matched_all.py` | `param_matched_all.json` |
| Table 7 (AIKAE) | `run_param_matched_all.py` | `param_matched_all.json` |
| Table 8 (Noise robustness) | `run_noise_sweep.py` | `noise_frozen.json` |
| Table 9 (DMD noise) | `run_noise_spectral.py` | `noise_spectral.json` |
| Table 10 (Multi-horizon) | `run_param_matched.py` | `param_matched.json` |
| Table 11 (Param counts) | `run_param_matched.py` | `param_matched.json` |
| Figure 1 (Gradient conflict) | `run_gradient_conflict.py` | `gradient_conflict.json` |
| Figure 2 (Phi-sweep Pareto) | `run_phi_sweep.py` | `phi_sweep.json` |

Additional experiment scripts included for completeness:
- `run_head_comparison.py`: DMD/MLP/NeuralODE head comparison
- `run_nonautoregressive.py`: Non-autoregressive forecasting variant
- `run_ablation_baselines.py`: Ablation studies
- `run_highdim_ks.py`: KS-64D high-dimensional experiment
- `run_koopa_compare.py`: Koopa baseline comparison

## Generating Figures

After running the experiments:
```
cd code/Paper
python make_figures.py
```

## Formal Verification

The Lean 4 proofs in `supplementary/lean_proofs/` verify Propositions 1 and 2.
To check (requires Lean 4 v4.35.0-rc2 and Mathlib):

```
cd supplementary/lean_proofs
lake build
```

- `ProofCheck/CapacityBound.lean`: Proposition 1 (capacity bound, 5 theorems)
- `ProofCheck/GradientConflict.lean`: Proposition 2 (gradient conflict, 4 theorems)
