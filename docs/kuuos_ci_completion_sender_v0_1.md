# MGAP4D → KuuOS CI Completion Sender v0.1

## Purpose

This sender connects completion of `PR Lean Fast Check` in `itakura-hidetoshi/4d-mass-gap` to the KuuOS CI Completion Reentry v1.1 receiver.

The sender is deliberately event-driven but not trust-transitive:

```text
PR Lean Fast Check completes
→ trusted default-branch workflow_run listener
→ same-repository / canonical-base gate
→ exact workflow-run jobs fetched through GitHub API
→ exact job `Changed Lean fast check`
→ exact step `Run changed Lean fast check`
→ bounded repository_dispatch packet
→ KuuOS receiver
→ fresh GitHub MCP re-observation
```

The GitHub event is a wake-up signal. It is not success evidence and it grants no merge authority.

## Why the listener lives on `main`

GitHub `workflow_run` listener workflows must exist on the repository default branch. The repository default branch is `main`, while theorem authority remains on `formal/real-hilbert-uniform-coercive-strong-limit`. The sender is therefore default-branch infrastructure and does not alter the theorem carrier.

## Security boundary

The privileged `workflow_run` job never checks out the triggering PR head. It explicitly checks out trusted `main` code and accepts only source runs whose `head_repository.full_name` is exactly `itakura-hidetoshi/4d-mass-gap`.

The runtime compiler additionally requires:

- source repository `itakura-hidetoshi/4d-mass-gap`;
- workflow `PR Lean Fast Check`;
- source event `pull_request`;
- source workflow status `completed` with a terminal conclusion;
- same-repository head;
- pull request base `formal/real-hilbert-uniform-coercive-strong-limit`;
- exact job `Changed Lean fast check`, completed with a terminal conclusion;
- exact step `Run changed Lean fast check`, completed with a terminal conclusion;
- exact 40-hex workflow head SHA.

A failure conclusion is still dispatched. That is intentional: KuuOS should receive both green and failed terminal states and decide the next route only after fresh MCP re-observation.

## Cross-repository authority

GitHub's repository-dispatch endpoint requires write authority on the destination repository. Configure the `4d-mass-gap` Actions secret:

```text
KUUOS_CI_REENTRY_TOKEN
```

with a GitHub App installation token or fine-grained personal access token scoped to `itakura-hidetoshi/KuuOS` and permitted to create repository dispatch events. For a fine-grained token, GitHub documents `Contents: write` on the destination repository for this endpoint.

The token is read only by the final dispatch step. It is never written to artifacts, summaries, JSON packets, or logs.

If the secret is absent, the sender fails closed with:

```text
KUUOS_CI_REENTRY_TOKEN_NOT_CONFIGURED: dispatch withheld fail-closed
```

and performs no cross-repository write.

## Destination packet

The destination event type is:

```text
kuuos_ci_completion_v1_1
```

The bounded `client_payload` includes repository, source run ID, workflow name, exact head SHA, branch, terminal workflow conclusion, PR number/base, exact required job and step names, source job/step conclusions, and source-event/jobs digests.

The destination receiver is expected to treat this packet only as a wake-up signal and to perform fresh MCP re-observation before verified re-entry.

## Validation

The same workflow runs a deterministic self-check on pull requests and manual dispatch:

```bash
python3 scripts/kuuos_ci_completion_sender_v0_1.py --self-check
```

The self-check covers success, terminal failure, wrong canonical base, untrusted fork head, and missing exact Lean step.
