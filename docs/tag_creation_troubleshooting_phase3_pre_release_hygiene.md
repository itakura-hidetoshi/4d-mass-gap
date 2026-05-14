# Tag creation troubleshooting: Phase 3 pre-release hygiene

This note records the likely failure mode and the script repair for the Phase 3 pre-release hygiene tag.

## Tag

```text
phase3-pre-release-hygiene-ci-green
```

## Target commit

```text
d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
```

## Likely failure mode

Some environments use shallow checkout or fetch only the current tip. In that state, this check may fail even though the target commit exists on GitHub:

```bash
git cat-file -e d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b^{commit}
```

## Repair added to script

The script now attempts ordinary fetch first, then repairs shallow or incomplete local history:

```bash
git fetch origin main --tags --prune

git fetch origin main --tags --unshallow
```

If the repository is not shallow, it also attempts an explicit target-commit fetch.

## Manual recovery command

If tag creation still fails locally, run:

```bash
git fetch origin main --tags --unshallow || git fetch origin main --tags --depth=100000
bash scripts/create_phase3_pre_release_hygiene_tag.sh
```

## Annotated tag note

The script creates an annotated tag. Therefore, `git ls-remote --tags` may show a tag-object SHA. The commit check should use:

```bash
git rev-list -n 1 phase3-pre-release-hygiene-ci-green
```

Expected resolved commit:

```text
d80c73f4daaf2e95ab193b6ae63d6f20b86e8e1b
```

## Boundary

```text
This troubleshooting note does not create the tag.
It only repairs the manual tag creation path.
```
