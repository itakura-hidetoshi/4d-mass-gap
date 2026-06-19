#!/usr/bin/env bash
set -euo pipefail

echo "[diagnostic] build symmetry limit module"
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryTightLimit
