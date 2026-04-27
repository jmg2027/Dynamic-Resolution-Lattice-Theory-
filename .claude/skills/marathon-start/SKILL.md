---
name: marathon-start
description: "Start a new marathon following a blueprint.  Read blueprints/{math,physics}/<field>.md + start Phase planning.  Triggered by: 'marathon start' / 'marathon start', 'marathon start', 'start blueprint', 'begin field'."
---

# Marathon Start

Enter a new field marathon in the 213 library. Follow one of the
14+14 fields in blueprints/.

## Procedure

### Step 1: Field Selection

Based on user request or priority:

```
blueprints/math/INDEX.md      14 math fields
blueprints/physics/INDEX.md   14 physics fields
```

Top priority candidates:
- math/01 Probability, math/02 Multivariable, math/03 Topology
- math/10 Combinatorics, math/13 213 Meta
- physics/01 Atomic, physics/02 Hadron, physics/04 Cosmology
- physics/07 Yang-Mills, physics/10 Falsifier

### Step 2: Read Blueprint

For the selected `blueprints/<track>/<NN>_<field>_213.md`:

1. *Why this field* — pain points of ZFC approach
2. *213-native emergence* — natural derivation path
3. *Building blocks already in place* — starting point
4. *Phase plan* — concrete steps
5. *Connections to other tracks*
6. *Unsolved problems*

### Step 3: Start First Phase

Phase naming: `<Track><NN>` (after Phase D = E, F, ...).

Each Phase:
- Single Lean file (~80 lines)
- decide-checked theorems
- explicit doc-string (why this result is atomic)

### Step 4: Create New Directory

```
lean/E213/<Math|Physics>/<Field>/
  Phase<NN>_<topic>.lean
  ...
  Capstone.lean    (field summary)
```

### Step 5: At End of Marathon

1. Run lake-build-verify
2. Run purity-check
3. Run catalog-sync
4. Write books/<track>/<field>.md
5. Update handoff

## Usage Example

```
User: "Start Probability 213 marathon"
→ Read blueprints/math/01_probability_213.md
→ Create lean/E213/Math/Probability/
→ Progress through Phase EA, EB, EC, ...
→ On finish: 4-step sync
```
