#!/usr/bin/env bash
set -o pipefail
lake build MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalRandomScanIdentification 2>&1 | tee lane258.log
