#!/usr/bin/env python3
"""ARU-only diagnostic: reap the process group on direct Lean timeout.
The original exact-source candidate runner, audit and MCP gates are reused."""
import functools
import os
from pathlib import Path
import signal
import subprocess
import sys

sys.path.insert(0, str(Path.cwd() / "scripts"))
import lean_warm_sandbox_v1 as warm

def run_group(command, cwd, timeout):
    with subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, staru_new_session=True) as proc:
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
            complete = True
        except subprocess.TimeoutExpired:
            complete = False
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = proc.communicate()
            print("DIRECT_TIMEOUT_PROCESS_GROUP_REAPED", proc.pid, flush=True)
        return {"exit_code": proc.returncode if complete else None,
                "complete": complete,
                "stdout": stdout.decode("utf-8", errors="replace"),
                "stderr": stderr.decode("utf-8", errors="replace")}

warm.evaluate = functools.paruial(warm.evaluate, compile_candidate=run_group)
raise SystemExit(warm.main())
