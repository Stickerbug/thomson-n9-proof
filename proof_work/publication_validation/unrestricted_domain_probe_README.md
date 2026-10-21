# Unrestricted physical Gram domain probe — discovery only

A clear negative value was found and sampling stopped immediately. The equilateral rational point u=v=t=0.58 lies outside the sharp cube, and its physical Gram determinant is exactly (1-0.58)^2*(1+2*0.58)=0.381024>0. All three pairwise dots are strictly below 1.

Using the original numerical solution A and c from d10_relative_normal2026_results.json, the float residual is -0.0004000015432459314. Independent 90-digit Decimal reevaluation of those same numerical coefficients gives

    Rf = -0.00040000154324718690233141914696295809752881643959803068197384292366541032302079528259888

The new script writes out the formula and Q recurrence. F uses the average of all six coordinate permutations, including multiplicities. Three known contact controls AAA, AFF and DDD produce float residuals of magnitude at most 8.44e-15, checking this normalization. The result contains the point, Gram determinant, F, three diagonal F values, all three pair energies, c, source SHA256, deterministic random seed and sample counts.

Five samples were examined: two equilateral points, one random physical Gram point, one lower Gram boundary point and one upper Gram boundary point. The main probe took 0.1069406250026077 seconds and exited 0. The process stopped at the first confirmed residual below -0.0001, without optimization or a full-domain certificate.

This is a discovery calculation for the archived numerical matrix, not a rigorous interval evaluation of the exact sharp kernel. It gives a clear reason to retain the existing pair reduction: directly enlarging this sharp-kernel claim to the entire physical Gram domain is not supported. No previously PASS module, archived certificate or old kernel was modified. No Lean installation was attempted.
