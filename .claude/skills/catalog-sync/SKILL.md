---
name: catalog-sync
description: "Sync catalogs/ after adding Lean theorems.  New atomic integers, constants, results → update appropriate catalog.  Triggered by: 'catalog sync' / 'catalog sync', 'catalog sync', 'catalog update' / 'catalog update', 'sync catalogs'."
---

# Catalog Sync

Sync the 3 sources (Lean, books, catalogs) of the 213 library.
Lean = ground truth → reflect in catalogs.

## Procedure

### Step 1: Identify changed Lean files

```bash
git diff --name-only HEAD~1..HEAD lean/E213/ | head
```

### Step 2: Extract new theorems

Identify new theorems in each changed file:
- `theorem`, `def`, `class` declarations
- result integers (in `= N` form)
- atomic expressions (using NS, NT, d)

### Step 3: Map to appropriate catalog

| New result | Update catalog |
|---|---|
| New atomic integer | catalogs/atomic-integers.md |
| Physics constant chain | catalogs/physics-constants.md |
| Element / Z atomic | catalogs/periodic-table.md |
| Measurement falsifier | catalogs/falsifiers.md |
| Multi-output integer | catalogs/correspondences.md |
| Math theorem | catalogs/math-theorems.md |

### Step 4: Add catalog entry

For each new result:
```markdown
  N = atomic_form  (file_path:line, precision)
```

### Step 5: Book update recommended (optional)

Also recommended: sync the relevant books/<track>/<field>.md narrative.

## When to Use

- At end of marathon
- Immediately after committing new results
- Before writing HANDOFF
- After migration

## Consistency Principle

  Lean = ground truth (build + decide)
  Catalogs = lookup
  Books = narrative

  Keep all three sources in sync.
