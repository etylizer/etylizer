# Plan: Restructure dynamic() detection commits

## Context
The commit chain is: ymmlrnmw → rtonrkvz → okptlvpp → tonzvzvn (empty) → pypoqszt (empty)

- **rtonrkvz**: Currently has basic detection (has_dynamic_mater + var_sources_have_dynamic) + unfold_ty + log level changes + test cases + variable naming bug fix
- **okptlvpp**: Enhanced detection with BFS taint propagation (only changes constr_solve.erl)
- **tonzvzvn**: Empty, titled "Simple dynamic() detection"
- **pypoqszt**: Empty, titled "BFS search for dynamic()"

## Goal
1. **rtonrkvz** should become simpler: if dynamic() is **anywhere** in the constraints, disable redundancy checks completely (no per-branch detection)
2. **tonzvzvn** should receive the current basic detection from rtonrkvz (has_dynamic_mater + var_sources_have_dynamic)
3. **pypoqszt** should receive the BFS detection from okptlvpp (dynamic_tainted_vars + propagate_taint)
4. Resolve conflicts after rtonrkvz

## Steps

### Step 1: Edit rtonrkvz — Replace detection with simple global check
In constr_solve.erl at rtonrkvz: instead of has_dynamic_mater checking per-branch, add a simple function `has_dynamic_constr` that checks if dynamic() appears anywhere in the full constraint set. If yes, skip all redundancy checks.

Keep everything else in rtonrkvz unchanged (unfold_ty, log levels, test cases, etc.).

### Step 2: Resolve conflicts in okptlvpp
okptlvpp only changes constr_solve.erl. After rtonrkvz changes, the context will conflict. Resolve so okptlvpp becomes a no-op or minimal (since the old basic detection it was replacing no longer exists). Actually okptlvpp should become empty since its changes no longer apply.

### Step 3: Edit tonzvzvn — Add basic detection algorithm
Add to constr_solve.erl: has_dynamic_mater + var_sources_have_dynamic (the original rtonrkvz code), replacing the simple global check with per-branch detection.

### Step 4: Edit pypoqszt — Add BFS detection algorithm
Add to constr_solve.erl: Replace var_sources_have_dynamic with BFS-based dynamic_tainted_vars + propagate_taint + has_tainted_var + collect_vars + add_var_edges (the original okptlvpp code).

### Step 5: Verify
Check `jj log` and `jj diff` for each commit to verify correctness.
