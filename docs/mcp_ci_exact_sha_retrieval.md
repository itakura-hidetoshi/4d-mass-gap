# MCP-readable Lean CI receipts (PR heads and canonical merges)

The theorem authority in this repository is
`formal/real-hilbert-uniform-coercive-strong-limit`, not the default `main`.
Always re-observe its **exact SHA** before reporting that CI has passed.

## Why a successful merge SHA may look like it has no CI

The connected GitHub MCP action `fetch_commit_workflow_runs` currently returns
only `pull_request`-triggered runs on its first page. A merge commit on the
authoritative branch is tested by a **push** event, so an empty response from
that MCP action does **not** mean that CI was absent or failed.

The `PR Lean Fast Check` workflow therefore publishes an exact-SHA GitHub
commit status under the unchanged context
`chatgpt-ci-receipt/PR Lean Fast Check` for two types of execution:

- On a same-repository `pull_request`, publish to
  `github.event.pull_request.head.sha` (not the synthetic PR merge SHA).
- On a `push` to `main` or
  `formal/real-hilbert-uniform-coercive-strong-limit`, publish to
  `github.sha` (the actual commit tested).

The workflow retains its existing path filters. A docs-only merge may not run
the fast Lean check, in which case there will be no receipt for that SHA.
The status is a **wake-up receipt**, not a substitute for the detailed
workflow/job result.

## Reliable GitHub MCP lookup

1. Fetch the authoritative branch reference afresh and take its exact
   `object.sha`. For a PR, fetch that PR and use its exact `head_sha`.
2. Call `get_commit_combined_status` with
   `repo_full_name="itakura-hidetoshi/4d-mass-gap"` and
   `commit_sha=<exact SHA>`.
3. Match status `context="chatgpt-ci-receipt/PR Lean Fast Check"`; inspect
   `state` and the provided `target_url`. The target points to
   `https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/<run ID>`.
   Do not use a status belonging to an older PR head or a different commit.
4. Retrieve the run by its ID and verify the **Changed Lean fast check** job
   and **Publish MCP CI completion receipt** job both ended
   `completed / success`. For a PR head, `fetch_commit_workflow_runs` is
   also available, but **do not rely on it for a push merge SHA**.
5. While a job is still running, `fetch_workflow_job_steps` is preferable:
   the GitHub redirected job-log endpoint can temporarily return
   `404 BlobNotFound`. Once the job is complete, use
   `fetch_workflow_job_logs` and verify the changed theorem target,
   compiler errors, and warnings. If logs are temporarily unavailable,
   do not report them as clean.
6. Treat missing receipts, pending jobs, cancelled jobs or a different SHA
   as *unverified* rather than GREEN. Use the existing exact-head CI checks
   before merge. A green PR does not automatically certify subsequent
   theorem-changing commits.

The connected MCP's PR-only workflow-run filtering and temporary log
redirect behavior are external tool limitations. This repository fixes the
missing push-commit receipt and documents the supported lookup path; it
does not change the MCP service implementation or guarantee an automatic
chat notification.
