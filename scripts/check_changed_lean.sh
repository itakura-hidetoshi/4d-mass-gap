#!/usr/bin/env bash
set -euo pipefail

echo "[diagnostic] compile oriented gauge symmetry layer"
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryLimit
