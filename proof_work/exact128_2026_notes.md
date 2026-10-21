# Guarded native signed128 Bernstein backend

Files: exact128_2026.c, exact128_2026.py, exact128_2026_test.py, exact128_2026_test_results.json. This is an independent backend only; no existing engine or root run was modified.

NativeTensor accepts a three-dimensional exact integer array, each dimension1..64. Its shape is the polynomial coefficient tensor shape. Internal storage is uint64 with trailing dimension2. Python and C both require little endian and C validates signed128 two's complement byte layout. C accesses signed128 values only via memcpy, avoiding pointer aliasing and signed shifts.

Every conversion and C operation rejects coefficients not strictly in(−2^124,2^124). C split scans the entire input before writing any output. Two inputs plus upper flag have magnitude<2^125; signed128 has much larger limit2^127. Division uses C quotient then explicitly subtracts1 for negative odd sums, giving floor((x+y+upper)/2), with upper0 floor and upper1 ceil. Each output coefficient remains within the original integer convex range, so repeated subdivision preserves the strict guard. No scale adjustment occurs.

Public operations: NativeTensor(object_array), tensor.shape, tensor.dtype='signed128-native', tensor.min()/max() returning Python int, tensor.split(axis,upper=False) returning two native tensors, tensor.to_object() for checks. Module split(tensor,axis,upper) is a convenience adapter. Native split and min/max recheck C-side ranges every call. Internal _words/_wrap are private and should not be mutated or used with external noncontiguous data.

The library compiles from the C source using /usr/bin/gcc -O2 -std=gnu11 -shared -fPIC into a source-hash-named .so. Call library() once during serial setup before starting concurrent workers, avoiding simultaneous first compilation. Mathematical correctness depends on audited C integer arithmetic and compiler behavior, not a floating solver. Preserve the source hash in any full proof wrapper.

Crosscheck run passed:120 random tensors plus5 extreme/axis64 tensors;750 complete lower/upper split comparisons with the original Python object implementation and min/max equality;450 independent Fraction midpoint floor/ceil comparisons;15 shape/range/C-guard rejection checks. Inputs included near±(2^124−1), negative odd sums, and signed128 overflow magnitudes. Direct C range rejection also confirmed no output write. Total1.745 seconds, exit0.

No claim of global Thomson certification is made by this backend or its tests. An engine adapter must preserve exact root tensor values, dispatch split/min/max correctly, and retain all existing domain and leaf-cover checks.
