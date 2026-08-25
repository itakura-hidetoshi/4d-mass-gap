# MGAP4D → KuuOS Durable Source Inbox v0.2

## Purpose

This layer makes CI-completion re-entry durable without requiring an active ChatGPT conversation, a continuously running MCP client, or a cross-repository credential.

The source repository already owns the trusted `workflow_run` listener for `PR Lean Fast Check`. v0.2 persists every admitted terminal completion signal as a same-repository GitHub Issue before attempting the optional KuuOS `repository_dispatch` mirror.

```text
PR Lean Fast Check completes
→ trusted main-branch workflow_run listener
→ exact source / canonical-base / same-repository-head gate
→ exact Changed Lean fast check job
→ exact Run changed Lean fast check step
→ compile bounded sender packet
→ compile deterministic source-inbox identity
→ persist deduplicated open Issue in 4d-mass-gap
→ conversation/runtime may be absent
→ later GitHub MCP client searches pending Issues
→ fresh exact run/job/step/head-SHA re-observation
→ verified success or verified non-success re-entry
→ acknowledgement comment + close Issue
```

The source Issue is a durable wake-up receipt only. It is not CI success evidence and it grants neither merge nor write authority.

## Why same-repository persistence

The source workflow's ordinary `GITHUB_TOKEN` is authorized to write Issues in `itakura-hidetoshi/4d-mass-gap` when the workflow declares `issues: write`. It is not silently treated as authority over `itakura-hidetoshi/KuuOS`.

Therefore the durable path needs no additional secret:

```text
4d-mass-gap workflow_run
→ 4d-mass-gap Issue
```

The existing cross-repository dispatch remains useful as an optional KuuOS mirror when `KUUOS_CI_REENTRY_TOKEN` is configured, but durable capture no longer depends on that token.

## Exact source contract

`scripts/kuuos_ci_completion_source_inbox_v0_2.py` accepts only a sender result already admitted by `kuuos_ci_completion_sender_v0_1.py` and rechecks:

- source repository `itakura-hidetoshi/4d-mass-gap`;
- source workflow `PR Lean Fast Check`;
- source event `pull_request`;
- workflow status `completed` with a terminal conclusion;
- exact 40-hex head SHA;
- positive PR number;
- canonical base `formal/real-hilbert-uniform-coercive-strong-limit`;
- exact required job `Changed Lean fast check`;
- exact required step `Run changed Lean fast check`;
- terminal job and step conclusions;
- destination binding `itakura-hidetoshi/KuuOS`;
- sender boundary `event_is_wakeup_signal_only = true`;
- sender boundary `fresh_mcp_reobservation_required = true`.

Both successful and failed terminal CI states are persisted. A failure is a valid re-entry signal for repair, not a success promotion.

## Durable identity and deduplication

The pending Issue title is deterministic:

```text
[KuuOS MCP CI Pending] <sha256 identity key>
```

The identity key binds:

```text
source repository + workflow run ID + workflow name + exact head SHA
```

Before Issue creation, the workflow searches for an Issue with the exact deterministic title. Duplicate workflow notifications therefore converge onto one durable queue item.

The Issue body is strict JSON containing:

- exact identity;
- PR/base/head binding;
- source workflow/job/step conclusions;
- MCP re-observation request;
- optional KuuOS mirror metadata;
- non-authority boundaries;
- source/sender digests.

No token or credential is written to the Issue or artifacts.

## MCP pickup

An MCP-capable client does not need to poll CI. When active, it only enumerates pending durable work:

```text
repository = itakura-hidetoshi/4d-mass-gap
state      = open
title      contains "[KuuOS MCP CI Pending]"
```

For each pending Issue:

1. parse its JSON body;
2. read the exact `mcp_reobserve_request`;
3. freshly re-observe the bound GitHub Actions run and its jobs through GitHub MCP;
4. require the exact workflow name and exact head SHA;
5. require the exact job `Changed Lean fast check` to be completed;
6. require the exact step `Run changed Lean fast check` to be completed with a terminal conclusion;
7. produce the v1.1 KuuOS verification packet;
8. pass that packet to `compile_source_ack(...)`;
9. only if acknowledgement is ready, add the acknowledgement JSON as an Issue comment and close the Issue.

If the MCP client disappears before verification or acknowledgement, the Issue simply stays open. The event is therefore not lost with conversational lifetime.

## Acknowledgement boundary

`compile_source_ack(...)` permits closure only if the verification packet states:

```text
status = KUUOS_GITHUB_CI_COMPLETION_REENTRY_VERIFIED
route ∈ {verified_success, verified_non_success}
fresh_mcp_reobservation = true
repository / run ID / workflow / head SHA exactly match
merge_authority_granted = false
write_authority_granted = false
```

Thus:

```text
Issue persisted
≠ CI success

Issue read by MCP
≠ CI success

fresh exact MCP re-observation
→ verified re-entry

verified re-entry
→ acknowledgement allowed

acknowledgement
≠ merge authority
≠ write authority
```

## Relationship to KuuOS durable inbox v1.3

The source Issue is the credential-free durable source of truth for wake-up delivery.

When `KUUOS_CI_REENTRY_TOKEN` is configured, the same admitted sender packet is additionally dispatched to KuuOS, where KuuOS durable inbox v1.3 may create a mirrored pending Issue. The two receipts share the same exact run identity and both still require fresh MCP re-observation before acknowledgement.

Preferred operational hierarchy:

```text
1. source same-repository durable Issue        always available
2. KuuOS repository_dispatch + durable mirror when credential configured
3. KuuOS public poller v1.2                    fallback only
```

The third path is retained for redundancy, not as the normal completion detector.

## Security boundary

The privileged `workflow_run` job still checks out only trusted `main` code. It never checks out the triggering PR head.

Issue-write authority is scoped to the source repository. Cross-repository dispatch continues to require its separately configured token. Persistence does not create any merge or code-write authority.

## Validation

```bash
python3 scripts/kuuos_ci_completion_sender_v0_1.py --self-check
python3 scripts/kuuos_ci_completion_source_inbox_v0_2.py --self-check
```

The v0.2 self-check covers terminal success, terminal failure, wrong canonical base, missing fresh-MCP boundary, verified acknowledgement, unverified acknowledgement rejection, and wrong-head acknowledgement rejection.
