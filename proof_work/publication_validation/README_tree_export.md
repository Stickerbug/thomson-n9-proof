# Sharp root full-tree export: conditional coverage only

This directory contains a complete explicit binary coverage tree exported from one root invocation of an instrumented copy of the frozen analytic engine. It establishes only the engine's conditional domain coverage statement. It does not replace an independent arithmetic checker, the proofs of coefficient enclosures and symmetry, local certificates, PSD and pair reduction, or the complete nine-point Thomson proof.

The original engine, original coefficients, local certificates, original root replay, and input manifest are read only. Their complete before/after SHA-256 bindings are checked by the exporter. No Lean installation is involved.

## Files

- `sharp_tree_export.py`: exclusive-creation driver, instrumentation generator, and exact geometry selfcheck.
- `sharp_tree_engine_instrumented.py`: generated copy. Arithmetic and split order are unchanged. Library paths point to the original native dependencies. Observation hooks write initialized root inputs, every split, terminal leaf, and pending frontier; a finally block preserves the frontier on Python exceptions during traversal.
- `sharp_tree_instrumentation.patch`: reviewable complete difference from the frozen engine.
- `sharp_root_tree.jsonl`: every internal node and terminal/pending frontier node, never just counts or hashes.
- `sharp_root_inputs.json`: complete initialized rootinputs, field-for-field equal to the frozen replay, including F_mid_sym, epsF, d_mid, c_interval, delta, bits, K root floor tensor, D root ceil, Gram root ceil, normalized local cores, and boundary activations/multipliers.
- `sharp_tree_metadata.json`: original coefficient/local/replay/input hashes, source hashes, schema, root box, root invocation count and limits.
- `sharp_tree_result.json`: complete original engine result with root inputs and export bindings.
- `sharp_tree_selfcheck.json`: full-tree geometry/connectivity selfcheck and hashes.
- `sharp_tree_export.log`: execution output; see completion record for process exit code and measured times.
- `sharp_tree_failure.json` / `sharp_tree_selfcheck_failure.json`: retained when the corresponding operation fails; successful runs do not create these files.

## Schema: sharp-root-tree-v1

One compact JSON object per line. Each node has `type`, `path`, `box`, `levels`, and `indices`. The root path is the empty string. Children of path p are p+"0" and p+"1". Rational endpoints use exact Fraction strings; levels and indices are three integer arrays. The root box is exactly [-1,14/25]^3, explicitly recorded in metadata.

- `type="split"`: includes `axis`, an integer 0, 1, or 2. Both children must exist. Side 0 is the lower closed half, side 1 the upper closed half. Their shared face is the exact midpoint. The split axis has the minimum current level, ties resolved by axis number.
- `type="leaf"`: includes `kind`, `ident` (string or null), and `witness` (exact integer decimal string or null). Kinds are positive, gram_negative, ordered_disjoint, local_region, boundary_multiplier. Positive and boundary_multiplier save the engine integer minimum; the other kinds use null witnesses exactly as the original engine does. Local/boundary identities identify the original normalized inputs.
- `type="pending"`: includes `active_boundary_ids`. These are unproved frontier boxes retained in full if limits or exceptions stop traversal. A pending node is never a proved leaf.

For coordinate i, its exact interval is [-1+(39/25)*indices[i]/2^levels[i], -1+(39/25)*(indices[i]+1)/2^levels[i]]. At a split only the split-axis level increases by one and its child index becomes twice the parent index plus the side. All other coordinates stay identical. Nodes are emitted in depth-first order. The structure can be reconstructed from root splits alone.

## Input reconstruction and checks

The driver decodes original F_coefficients and c I384 endpoint numerators and their exact powers-of-two denominators from the original coefficient file. This preserves the original interval error epsF when the original check_analytic symmetrizes coefficient midpoints. Using already symmetric F_mid_sym as zero-width intervals would lose epsF and is not used. Local regions and boundary multipliers are passed directly from the original rootinputs and normalized again; equality with the original normalized values is asserted. At initialization, every rootinputs field and its original canonical SHA-256 must match before traversal starts.

One root call is permitted: budget 200000 nodes and 180 seconds, bits=96, delta=0. The original guard is unchanged. The driver refuses to overwrite existing files using exclusive x mode. Do not rerun the driver in this populated directory; doing so cannot safely be used as a resume mechanism. Complete outputs and failures remain available for review.

The selfcheck reads every JSONL node, rejects duplicate paths, reconstructs every exact box from levels/indices, follows all children from the root, checks midpoint partition and child levels/indices, rejects unreachable nodes, and compares leaf counts and transcript to the engine return. Counts/hashes supplement these full geometry checks. This selfcheck intentionally makes no independent claim that leaf arithmetic witnesses, local premises, or coefficient enclosures are valid. An independently implemented checker must validate those claims.
