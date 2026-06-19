#!/usr/bin/env bash
set -euo pipefail

echo "[diagnostic] compile oriented gauge symmetry Prokhorov layer"
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryProkhorovLimit
